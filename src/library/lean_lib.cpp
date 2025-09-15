

// ========== phashtable.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/bit_tricks.h"
#include "library/parray.h"

#ifndef LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY
#define LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY 8
#endif

#ifndef LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY
#define LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY 64
#endif

namespace lean {

template<typename T>
class default_hash_entry {
protected:
    enum state { Free, Deleted, Used };

    unsigned  m_hash; //!< cached hash code
    state     m_state;
    union {
        T     m_data;
    };
    explicit default_hash_entry(bool):m_hash(0), m_state(Deleted) {} // NOLINT
public:
    typedef T                data;
    default_hash_entry():m_hash(0), m_state(Free) {}
    default_hash_entry(default_hash_entry const & src):
        m_hash(src.m_hash), m_state(src.m_state) {
        if (m_state == Used)
            new (&m_data) T(src.get_data());
    }
    default_hash_entry(T const & v, unsigned h):m_hash(h), m_state(Used) {
        new (&m_data) T(v);
    }
    ~default_hash_entry() { if (m_state == Used) m_data.~T(); }

    static default_hash_entry mk_deleted() { return default_hash_entry(false); }

    bool is_free() const { return m_state == Free; }
    bool is_deleted() const { return m_state == Deleted; }
    bool is_used() const { return m_state == Used; }

    unsigned get_hash() const  { return m_hash; }
    void set_hash(unsigned h)  { m_hash = h; }

    T const & get_data() const { lean_assert(is_used()); return m_data; }

    void set_data(T const & d) {
        if (is_used())
            m_data.~T();
        new (&m_data) T(d);
        m_state = Used;
    }

    default_hash_entry & operator=(default_hash_entry const & src) {
        if (is_used())
            m_data.~T();
        m_hash  = src.m_hash;
        m_state = src.m_state;
        if (m_state == Used)
            new (&m_data) T(src.get_data());
        return *this;
    }
};

template<typename Entry, typename HashProc, typename EqProc, bool ThreadSafe = false>
class phashtable_core : private HashProc, private EqProc {
protected:
    typedef parray<Entry, ThreadSafe> table;
    typedef typename Entry::data      data;
    typedef Entry                     entry;

    table    m_table;
    unsigned m_size;
    unsigned m_num_deleted;

    static void copy_table(table const & source, table & target) {
        lean_assert(target.get_rc() == 1);
        typename table::exclusive_access B(target);
        unsigned target_sz   = B.size();
        unsigned target_mask = target_sz - 1;
        source.for_each([&](entry const & e) {
                if (!e.is_used())
                    return;
                unsigned hash  = e.get_hash();
                unsigned begin = hash & target_mask;
                unsigned idx   = begin;
                for (; idx < target_sz; idx++) {
                    if (B[idx].is_free()) {
                        B.set(idx, e);
                        return;
                    }
                }
                idx = 0;
                for (; idx < begin; idx++) {
                    if (B[idx].is_free()) {
                        B.set(idx, e);
                        return;
                    }
                }
            });
    }

    void expand_table() {
        table new_table(m_table.size() << 1, entry());
        copy_table(m_table, new_table);
        swap(m_table, new_table);
        m_num_deleted = 0;
    }

    void expand_table_if_needed() {
        if ((m_size + m_num_deleted) << 2 > (m_table.size() * 3))
            expand_table();
    }

    void remove_deleted_entries() {
        table new_table(m_table.size(), entry());
        copy_table(m_table, new_table);
        swap(m_table, new_table);
        m_num_deleted = 0;
    }

    unsigned get_hash(data const & e) const { return HashProc::operator()(e); }
    bool equals(data const & e1, data const & e2) const { return EqProc::operator()(e1, e2); }

public:
    phashtable_core(unsigned initial_capacity = LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY,
                    HashProc const & h = HashProc(),
                    EqProc const & e = EqProc()):
        HashProc(h),
        EqProc(e),
        m_table(initial_capacity, entry()),
        m_size(0),
        m_num_deleted(0) {
        lean_assert(is_power_of_two(initial_capacity));
    }

    phashtable_core(phashtable_core const & source):
        HashProc(source), EqProc(source),
        m_table(source.m_table), m_size(source.m_size), m_num_deleted(source.m_num_deleted) {
    }

    unsigned size() const { return m_size; }

    unsigned capacity() const { return m_table.size(); }

    friend void swap(phashtable_core & t1, phashtable_core & t2) {
        swap(t1.m_table, t2.m_table);
        std::swap(t1.m_size, t2.m_size);
        std::swap(t1.m_num_deleted, t2.m_num_deleted);
    }

    #define INSERT_LOOP_BODY()                                          \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    A.set(idx, entry(e, hash));                         \
                    return;                                             \
                }                                                       \
            } else if (curr.is_free()) {                                \
                unsigned new_idx;                                       \
                if (found_deleted) {                                    \
                    new_idx = del_idx; m_num_deleted--;                 \
                } else {                                                \
                    new_idx = idx;                                      \
                }                                                       \
                A.set(new_idx, entry(e, hash));                         \
                m_size++;                                               \
                return;                                                 \
            } else {                                                    \
                lean_assert(curr.is_deleted());                         \
                del_idx = idx;                                          \
            }                                                           \
        } ((void) 0)

    void insert(data const & e) {
        expand_table_if_needed();
        typename table::exclusive_access A(m_table);
        unsigned hash      = get_hash(e);
        unsigned cap       = A.size();
        unsigned mask      = cap - 1;
        unsigned begin     = hash & mask;
        unsigned idx       = begin;
        bool found_deleted = false;
        unsigned del_idx   = 0;
        for (; idx < cap; idx++) {
            INSERT_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            INSERT_LOOP_BODY();
        }
        lean_unreachable();
    }

    #undef INSERT_LOOP_BODY

    template<typename F>
    void for_each(F && fn) const {
        m_table.for_each([&](entry const & e) {
                if (e.is_used()) {
                    fn(e.get_data());
                }
            });
    }

    #define CONTAINS_LOOP_BODY()                                            \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    return true;                                        \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return false;                                           \
            }                                                           \
        } ((void) 0)

    bool contains(data const & e) const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            CONTAINS_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            CONTAINS_LOOP_BODY();
        }
        return false;
    }

    #undef CONTAINS_LOOP_BODY

    #define FIND_LOOP_BODY()                                            \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    return optional<data>(curr.get_data());             \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return optional<data>();                                \
            }                                                           \
        } ((void) 0)

    optional<data> find(data const & e) const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            FIND_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            FIND_LOOP_BODY();
        }
        return optional<data>();
    }

    #undef FIND_LOOP_BODY

private:
    #define ERASE_LOOP_BODY()                                           \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    goto found_elem;                                    \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return false;                                           \
            }                                                           \
        } ((void) 0)

    bool erase_aux(data const & e) {
        typename table::exclusive_access A(m_table);
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            ERASE_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            ERASE_LOOP_BODY();
        }
        return false; /* e is not in the table */
      found_elem:
        unsigned next_idx = idx + 1;
        if (next_idx == cap)
            next_idx = 0;
        if (A[next_idx].is_free()) {
            A.set(idx, entry());
            lean_assert(A[idx].is_free());
            m_size--;
        } else {
            A.set(idx, entry::mk_deleted());
            lean_assert(A[idx].is_deleted());
            m_num_deleted++;
            m_size--;
            if (m_num_deleted > m_size && m_num_deleted > LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY) {
                return true;
            }
        }
        return false;
    }

    #undef ERASE_LOOP_BODY

public:
    void erase(data const & e) {
        if (erase_aux(e)) {
            remove_deleted_entries();
        }
    }

    void clear() {
        if (m_size == 0 && m_num_deleted == 0)
            return;
        unsigned overhead = 0;
        unsigned cap      = 0;
        {
            typename table::exclusive_access A(m_table);
            cap   = A.size();
            for (unsigned idx = 0; idx < cap; idx++) {
                if (!A[idx].is_free)
                    A.set(idx, entry());
                else
                    overhead++;
            }
        }
        if (cap > LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY && overhead << 2 > (cap * 3)) {
            cap     = cap >> 1;
            lean_assert(is_power_of_two(cap));
            m_table = table(cap, entry());
        }
        m_size        = 0;
        m_num_deleted = 0;
    }


    bool check_invariant() const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned cap = A.size();
        unsigned num_deleted = 0;
        unsigned num_used = 0;
        for (unsigned idx = 0; idx < cap; idx++) {
            entry const & curr = A[idx];
            if (curr.is_deleted()) {
                num_deleted++;
            }
            if (curr.is_used()) {
                num_used++;
            }
        }
        lean_assert(num_deleted == m_num_deleted);
        lean_assert(num_used == m_size);
        return true;
    }
};

template<typename T, typename HashProc, typename EqProc, bool ThreadSafe = false>
class phashtable : public phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe> {
public:
    phashtable(unsigned initial_capacity = LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY,
               HashProc const & h = HashProc(),
               EqProc const & e = EqProc()):
        phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe>(initial_capacity, h, e) {}

    phashtable(phashtable const & src):
        phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe>(src) {}

    phashtable & operator=(phashtable const & s) {
        this->m_table       = s.m_table;
        this->m_size        = s.m_size;
        this->m_num_deleted = s.m_num_deleted;
        return *this;
    }
};
}




// ========== defeq_canonizer.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
/* \brief Return an expression that is definitionally equal to \c e.

   \remark The predicate locals_subset(r, e) holds for the resulting expression r.

   \remark updated is set to true if previous results may have been updated.

   \remark This procedure is meant to be used to canonize type class instances and
   proofs. It is too expensive for arbitrary terms.

   \remark Suppose we invoke defeq_canonize for every type class instance
   in a big term T, and we replace them with the result returned by defeq_canonize.
   If updated is not true, then forall instances I1 and I2 in the resulting term T',
   if I1 and I2 are definitionally equal and have the same local constants, then
   I1 and I2 are structurally equal.

   \remark Suppose we invoke defeq_canonize for every type class instance in a big term T,
   and updated is true in the end. Then, if we reset updated to false and restart the process,
   then eventually updated will be false after a finite number of restarts. */
class defeq_canonizer {
public:
    struct state {
        /* Canonical mapping I -> J (i.e., J is the canonical expression for I).
           Invariant: locals_subset(J, I) */
        rb_expr_map<expr>    m_C;
        /* Mapping from head symbol N to list of expressions es s.t.
           for each e in es, head_symbol(e) = N. */
        name_map<list<expr>> m_M;
    };
private:
    type_context_old & m_ctx;
    state &        m_state;
    bool *         m_updated{nullptr};

    optional<name> get_head_symbol(expr type);
    optional<expr> find_defeq(name const & h, expr const & e);
    void replace_C(expr const & e1, expr const & e2);
    void insert_C(expr const & e1, expr const & e2);
    void insert_M(name const & h, expr const & e);
    void replace_M(name const & h, expr const & e, expr const & new_e);
    expr canonize_core(expr const & e);

public:
    defeq_canonizer(type_context_old & ctx, state & s);

    expr canonize(expr const & e, bool & updated);
    expr canonize(expr const & e);

    state const & get_state() const { return m_state; }
    void set_state(state const & s) { m_state = s; }
};

inline bool is_eqp(defeq_canonizer::state const & s1, defeq_canonizer::state const & s2) {
    return is_eqp(s1.m_C, s2.m_C) && is_eqp(s1.m_M, s2.m_M);
}

void initialize_defeq_canonizer();
void finalize_defeq_canonizer();
}




// ========== defeq_canonizer.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/type_context.h"
#include "library/defeq_canonizer.h"

namespace lean {
defeq_canonizer::defeq_canonizer(type_context_old & ctx, state & s):
    m_ctx(ctx), m_state(s) {
}

optional<name> defeq_canonizer::get_head_symbol(expr type) {
    type    = m_ctx.whnf(type);
    expr const & fn = get_app_fn(type);
    if (is_constant(fn)) {
        return optional<name>(const_name(fn));
    } else if (is_pi(type)) {
        type_context_old::tmp_locals locals(m_ctx);
        expr l = locals.push_local_from_binding(type);
        return get_head_symbol(instantiate(binding_body(type), l));
    } else {
        return optional<name>();
    }
}

optional<expr> defeq_canonizer::find_defeq(name const & h, expr const & e) {
    list<expr> const * lst = m_state.m_M.find(h);
    if (!lst) return none_expr();
    for (expr const & e1 : *lst) {
        if (locals_subset(e1, e) && m_ctx.is_def_eq(e1, e))
            return some_expr(e1);
    }
    return none_expr();
}

void defeq_canonizer::replace_C(expr const & e1, expr const & e2) {
    m_state.m_C.insert(e1, e2);
    if (m_updated)
        *m_updated = true;
}

void defeq_canonizer::insert_C(expr const & e1, expr const & e2) {
    m_state.m_C.insert(e1, e2);
}

void defeq_canonizer::insert_M(name const & h, expr const & e) {
    list<expr> const * lst = m_state.m_M.find(h);
    if (lst) {
        m_state.m_M.insert(h, cons(e, *lst));
    } else {
        m_state.m_M.insert(h, to_list(e));
    }
}

void defeq_canonizer::replace_M(name const & h, expr const & e, expr const & new_e) {
    list<expr> const * lst = m_state.m_M.find(h);
    lean_assert(lst);
    m_state.m_M.insert(h, cons(new_e, remove(*lst, e)));
}

expr defeq_canonizer::canonize_core(expr const & e) {
    if (auto it = m_state.m_C.find(e)) {
        expr e1 = *it;
        if (e1 == e)
            return e;
        expr e2 = canonize_core(e1);
        if (e2 != e1) {
            replace_C(e, e2);
        }
        return e2;
    }
    expr e_type  = m_ctx.infer(e);
    optional<name> h = get_head_symbol(e_type);
    if (!h) {
        /* canonization is not support for type of e */
        insert_C(e, e);
        return e;
    } else if (optional<expr> new_e = find_defeq(*h, e)) {
        if (get_weight(e) < get_weight(*new_e) && locals_subset(e, *new_e)) {
            replace_C(*new_e, e);
            replace_M(*h, *new_e, e);
            insert_C(e, e);
            return e;
        } else {
            insert_C(e, *new_e);
            return *new_e;
        }
    } else {
        insert_C(e, e);
        insert_M(*h, e);
        return e;
    }
}

static void trace(type_context_old & ctx, expr const & e, expr const & r) {
    lean_trace("defeq_canonizer", scope_trace_env _(ctx.env(), ctx); tout() << "\n" << e << "\n==>\n" << r << "\n";);
}

expr defeq_canonizer::canonize(expr const & e, bool & updated) {
    type_context_old::transparency_scope scope(m_ctx, transparency_mode::Instances);
    m_updated = &updated;
    expr r = canonize_core(e);
    trace(m_ctx, e, r);
    return r;
}

expr defeq_canonizer::canonize(expr const & e) {
    type_context_old::transparency_scope scope(m_ctx, transparency_mode::Instances);
    m_updated = nullptr;
    expr r = canonize_core(e);
    trace(m_ctx, e, r);
    return r;
}

void initialize_defeq_canonizer() {
    register_trace_class("defeq_canonizer");
}

void finalize_defeq_canonizer() {
}
}




// ========== persistent_context_cache.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/unique_id.h"
#include "library/abstract_context_cache.h"

namespace lean {
class context_cache;
typedef unique_id context_cache_id;

/*
   Ideally, we could have a "functional" implementation of abstract_context_cache using rb_map and rb_tree.
   This "functional" implementation could be used to store the cache, for example, in tactic_state objects.
   We don't use this solution for two reasons:
   - rb_map (and rb_tree) are 10x slower than hashtable maps (and sets).
   - The functional object would increase the size of the tactic_state object considerably.

   This class provides an alternative implementation where the tactic_state stores only the cache id.
   This id is used to retrieve a thread local context_cache object.
   See comment at abstract_context_cache for more details.
*/
class persistent_context_cache : public abstract_context_cache {
    context_cache_id                        m_id;
    std::unique_ptr<abstract_context_cache> m_cache_ptr;
public:
    persistent_context_cache(context_cache_id, options const &);
    virtual ~persistent_context_cache();

    context_cache_id get_id() const { return m_id; }

    /* Cached configuration options */
    virtual options const & get_options() const override;
    virtual bool get_unfold_lemmas() const override;
    virtual unsigned get_nat_offset_cnstr_threshold() const override;
    virtual unsigned get_smart_unfolding() const override;
    virtual unsigned get_class_instance_max_depth() const override;

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override;
    virtual void set_infer(expr const &, expr const &) override;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override;

    virtual optional<optional<expr>> get_instance(expr const &) override;
    virtual void set_instance(expr const &, optional<expr> const &) override;

    virtual optional<optional<expr>> get_subsingleton(expr const &) override;
    virtual void set_subsingleton(expr const &, optional<expr> const &) override;

    /* this method should flush the instance and subsingleton cache */
    virtual void flush_instances() override;

    virtual void reset_frozen_local_instances() override;
    virtual void set_frozen_local_instances(local_instances const & lis) override;
    virtual optional<local_instances> get_frozen_local_instances() const override;

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) override;
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) override;

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) override;

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) override;

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) override;
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) override;
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) override;
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) override;
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) override;
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) override;

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) override;
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) override;

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) override;
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) override;

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) override;
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) override;
};
}




// ========== persistent_context_cache.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "library/persistent_context_cache.h"
#include "library/context_cache.h"

namespace lean {
typedef std::pair<unique_id, std::unique_ptr<abstract_context_cache>> unique_id_context_cache_pair;

MK_THREAD_LOCAL_GET_DEF(unique_id_context_cache_pair, get_unique_id_context_cache_pair);

persistent_context_cache::persistent_context_cache(unique_id id, options const & opts) {
    unique_id_context_cache_pair & p = get_unique_id_context_cache_pair();
    if (p.second && p.first == id && p.second->get_options() == opts) {
        /* Reuse thread local cache */
        m_cache_ptr.swap(p.second);
        m_id = mk_unique_id();
    } else {
        m_cache_ptr.reset(new context_cache(opts));
        m_id = mk_unique_id();
    }
}

persistent_context_cache::~persistent_context_cache() {
    unique_id_context_cache_pair & p = get_unique_id_context_cache_pair();
    p.first = m_id;
    m_cache_ptr.swap(p.second);
}

options const & persistent_context_cache::get_options() const {
    return m_cache_ptr->get_options();
}

bool persistent_context_cache::get_unfold_lemmas() const {
    return m_cache_ptr->get_unfold_lemmas();
}

unsigned persistent_context_cache::get_nat_offset_cnstr_threshold() const {
    return m_cache_ptr->get_nat_offset_cnstr_threshold();
}

unsigned persistent_context_cache::get_smart_unfolding() const {
    return m_cache_ptr->get_smart_unfolding();
}

unsigned persistent_context_cache::get_class_instance_max_depth() const {
    return m_cache_ptr->get_class_instance_max_depth();
}

optional<declaration> persistent_context_cache::get_decl(type_context_old & ctx, transparency_mode m, name const & n) {
    return m_cache_ptr->get_decl(ctx, m, n);
}

projection_info const * persistent_context_cache::get_proj_info(type_context_old & ctx, name const & n) {
    return m_cache_ptr->get_proj_info(ctx, n);
}

bool persistent_context_cache::get_aux_recursor(type_context_old & ctx, name const & n) {
    return m_cache_ptr->get_aux_recursor(ctx, n);
}

void persistent_context_cache::get_unification_hints(type_context_old & ctx, name const & f1, name const & f2, buffer<unification_hint> & hints) {
    return m_cache_ptr->get_unification_hints(ctx, f1, f2, hints);
}

optional<expr> persistent_context_cache::get_infer(expr const & e) {
    return m_cache_ptr->get_infer(e);
}

void persistent_context_cache::set_infer(expr const & e, expr const & t) {
    return m_cache_ptr->set_infer(e, t);
}

bool persistent_context_cache::get_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->get_equiv(m, e1, e2);
}

void persistent_context_cache::set_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->set_equiv(m, e1, e2);
}

bool persistent_context_cache::get_is_def_eq_failure(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->get_is_def_eq_failure(m, e1, e2);
}

void persistent_context_cache::set_is_def_eq_failure(transparency_mode m, expr const & e1, expr const & e2) {
    return m_cache_ptr->set_is_def_eq_failure(m, e1, e2);
}

optional<expr> persistent_context_cache::get_whnf(transparency_mode m, expr const & e) {
    return m_cache_ptr->get_whnf(m, e);
}

void persistent_context_cache::set_whnf(transparency_mode m, expr const & e, expr const & r) {
    return m_cache_ptr->set_whnf(m, e, r);
}

optional<optional<expr>> persistent_context_cache::get_instance(expr const & e) {
    return m_cache_ptr->get_instance(e);
}

void persistent_context_cache::set_instance(expr const & e, optional<expr> const & r) {
    return m_cache_ptr->set_instance(e, r);
}

optional<optional<expr>> persistent_context_cache::get_subsingleton(expr const & e) {
    return m_cache_ptr->get_subsingleton(e);
}

void persistent_context_cache::set_subsingleton(expr const & e, optional<expr> const & r) {
    return m_cache_ptr->set_subsingleton(e, r);
}

void persistent_context_cache::flush_instances() {
    return m_cache_ptr->flush_instances();
}

void persistent_context_cache::reset_frozen_local_instances() {
    return m_cache_ptr->reset_frozen_local_instances();
}

void persistent_context_cache::set_frozen_local_instances(local_instances const & lis) {
    return m_cache_ptr->set_frozen_local_instances(lis);
}

optional<local_instances> persistent_context_cache::get_frozen_local_instances() const {
    return m_cache_ptr->get_frozen_local_instances();
}

optional<fun_info> persistent_context_cache::get_fun_info(transparency_mode m, expr const & e) {
    return m_cache_ptr->get_fun_info(m, e);
}

void persistent_context_cache::set_fun_info(transparency_mode m, expr const & e, fun_info const & r) {
    return m_cache_ptr->set_fun_info(m, e, r);
}

optional<fun_info> persistent_context_cache::get_fun_info_nargs(transparency_mode m, expr const & e, unsigned k) {
    return m_cache_ptr->get_fun_info_nargs(m, e, k);
}

void persistent_context_cache::set_fun_info_nargs(transparency_mode m, expr const & e, unsigned k, fun_info const & r) {
    return m_cache_ptr->set_fun_info_nargs(m, e, k, r);
}

optional<unsigned> persistent_context_cache::get_specialization_prefix_size(transparency_mode m, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialization_prefix_size(m, e, k);
}

void persistent_context_cache::set_specialization_prefix_size(transparency_mode m, expr const & e, unsigned k, unsigned r) {
    return m_cache_ptr->set_specialization_prefix_size(m, e, k, r);
}

optional<ss_param_infos> persistent_context_cache::get_subsingleton_info(transparency_mode m, expr const & e) {
    return m_cache_ptr->get_subsingleton_info(m, e);
}

void persistent_context_cache::set_subsingleton_info(transparency_mode m, expr const & e, ss_param_infos const & r) {
    return m_cache_ptr->set_subsingleton_info(m, e, r);
}

optional<ss_param_infos> persistent_context_cache::get_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned k) {
    return m_cache_ptr->get_subsingleton_info_nargs(m, e, k);
}

void persistent_context_cache::set_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned k, ss_param_infos const & r) {
    return m_cache_ptr->set_subsingleton_info_nargs(m, e, k, r);
}

optional<ss_param_infos> persistent_context_cache::get_specialized_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_subsingleton_info_nargs(m, e, k);
}

void persistent_context_cache::set_specialization_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned k, ss_param_infos const & r) {
    return m_cache_ptr->set_specialization_subsingleton_info_nargs(m, e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_simp_congr_lemma(expr const & e, unsigned k) {
    return m_cache_ptr->get_simp_congr_lemma(e, k);
}

void persistent_context_cache::set_simp_congr_lemma(expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_simp_congr_lemma(e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_specialized_simp_congr_lemma(expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_simp_congr_lemma(e, k);
}

void persistent_context_cache::set_specialized_simp_congr_lemma(expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_specialized_simp_congr_lemma(e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_congr_lemma(expr const & e, unsigned k) {
    return m_cache_ptr->get_congr_lemma(e, k);
}

void persistent_context_cache::set_congr_lemma(expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_congr_lemma(e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_specialized_congr_lemma(expr const & e, unsigned k) {
    return m_cache_ptr->get_specialized_congr_lemma(e, k);
}

void persistent_context_cache::set_specialized_congr_lemma(expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_specialized_congr_lemma(e, k, r);
}

optional<congr_lemma> persistent_context_cache::get_hcongr_lemma(expr const & e, unsigned k) {
    return m_cache_ptr->get_hcongr_lemma(e, k);
}

void persistent_context_cache::set_hcongr_lemma(expr const & e, unsigned k, congr_lemma const & r) {
    return m_cache_ptr->set_hcongr_lemma(e, k, r);
}

optional<app_builder_info> persistent_context_cache::get_app_builder_info(expr const & e, unsigned k) {
    return m_cache_ptr->get_app_builder_info(e, k);
}

void persistent_context_cache::set_app_builder_info(expr const & e, unsigned k, app_builder_info const & r) {
    return m_cache_ptr->set_app_builder_info(e, k, r);
}


optional<app_builder_info> persistent_context_cache::get_app_builder_info(expr const & e, list<bool> const & m) {
    return m_cache_ptr->get_app_builder_info(e, m);
}

void persistent_context_cache::set_app_builder_info(expr const & e, list<bool> const & m, app_builder_info const & r) {
    return m_cache_ptr->set_app_builder_info(e, m, r);
}

void initialize_persistent_context_cache() {
    /* We need to reset the cache since the unique_id local counters are reset too. */
    register_thread_local_reset_fn([]() { get_unique_id_context_cache_pair() = unique_id_context_cache_pair(); });
}

void finalize_persistent_context_cache() {
}
}




// ========== abstract_parser.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <string>
#include "util/name_map.h"
#include "util/exception_with_pos.h"
#include "kernel/pos_info_provider.h"

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception_with_pos {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception_with_pos(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception_with_pos(msg), m_pos(p) {}
    virtual optional<pos_info> get_pos() const override { return some(m_pos); }
    std::string const & get_msg() const { return m_msg; }
    virtual throwable * clone() const override { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const override { throw *this; }
};

/** \brief Base class for frontend parsers with basic functions */
class abstract_parser : public pos_info_provider {
public:
    /** \brief Return the current position information */
    virtual pos_info pos() const = 0;

    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    virtual bool curr_is_token(name const & tk) const = 0;
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const = 0;
    /** \brief Read the next token if the current one is not End-of-file. */
    virtual void next() = 0;

    virtual unsigned parse_small_nat() = 0;
    virtual std::string parse_string_lit() = 0;
};
}




// ========== locals.h ==========

/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_set.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
namespace lean {
void collect_univ_params_core(level const & l, name_set & r);
name_set collect_univ_params(expr const & e, name_set const & ls = name_set());
/**
  \remark If restricted is true, then locals in meta-variable applications and local constants
  are ignored.
*/
class collected_locals {
    name_set     m_local_names;
    buffer<expr> m_locals;
public:
    void insert(expr const & l);
    bool contains(name const & n) const { return m_local_names.contains(n); }
    bool contains(expr const & l) const { return contains(mlocal_name(l)); }
    buffer<expr> const & get_collected() const { return m_locals; }
    bool empty() const { return m_locals.empty(); }
};

void collect_locals(expr const & e, collected_locals & ls, bool restricted = false);

/** \brief Return true iff locals(e1) is a subset of locals(e2). */
bool locals_subset(expr const & e1, expr const & e2);

level_param_names to_level_param_names(name_set const & ls);

/** \brief Return true iff \c [begin_locals, end_locals) contains \c local */
template<typename It>
bool contains_local(expr const & local, It const & begin_locals, It const & end_locals) {
    return std::any_of(begin_locals, end_locals, [&](expr const & l) { return mlocal_name(local) == mlocal_name(l); });
}

template<typename T>
bool contains_local(expr const & l, T const & locals) {
    return std::any_of(locals.begin(), locals.end(),
                       [&](expr const & l1) { return mlocal_name(l1) == mlocal_name(l); });
}

/** \brief Return true iff \c e contains a local constant \c h s.t. mlocal_name(h) in s */
bool contains_local(expr const & e, name_set const & s);

/** \brief Return true iff \c e contains a local constant named \c n (it uses mlocal_name) */
bool contains_local(expr const & e, name const & n);

/** \brief Return true iff \e contains the local constant \c h */
inline bool depends_on(expr const & e, expr const & h) {
    return contains_local(e, mlocal_name(h));
}

/** \brief Return true iff one of \c es contains the local constant \c h */
optional<expr> depends_on(unsigned sz, expr const * es, expr const & h);

/** \brief Return true iff \c e depends on any of the local constants in \c hs */
bool depends_on_any(expr const & e, unsigned hs_sz, expr const * hs);
inline bool depends_on_any(expr const & e, buffer<expr> const & hs) {
    return depends_on_any(e, hs.size(), hs.data());
}

/** \brief Replace the given local constants occurring in \c e with the given terms */
expr replace_locals(expr const & e, unsigned sz, expr const * locals, expr const * terms);
expr replace_locals(expr const & e, buffer<expr> const & locals, buffer<expr> const & terms);
inline expr replace_local(expr const & e, expr const & local, expr const & term) {
    return replace_locals(e, 1, &local, &term);
}
}




// ========== locals.cpp ==========

/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/expr.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "library/placeholder.h"
#include "library/locals.h"

namespace lean {
void collect_univ_params_core(level const & l, name_set & r) {
    for_each(l, [&](level const & l) {
            if (!has_param(l))
                return false;
            if (is_param(l) && !is_placeholder(l))
                r.insert(param_id(l));
            return true;
        });
}

name_set collect_univ_params(expr const & e, name_set const & ls) {
    if (!has_param_univ(e)) {
        return ls;
    } else {
        name_set r = ls;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_param_univ(e)) {
                    return false;
                } else if (is_sort(e)) {
                    collect_univ_params_core(sort_level(e), r);
                } else if (is_constant(e)) {
                    for (auto const & l : const_levels(e))
                        collect_univ_params_core(l, r);
                }
                return true;
            });
        return r;
    }
}

level_param_names to_level_param_names(name_set const & ls) {
    level_param_names r;
    ls.for_each([&](name const & n) {
            r = level_param_names(n, r);
        });
    return r;
}

void collected_locals::insert(expr const & l) {
    if (m_local_names.contains(mlocal_name(l)))
        return;
    m_local_names.insert(mlocal_name(l));
    m_locals.push_back(l);
}

void collect_locals(expr const & e, collected_locals & ls, bool restricted) {
    if (!has_local(e))
        return;
    expr_set visited;
    std::function<void(expr const & e)> visit = [&](expr const & e) {
        if (!has_local(e))
            return;
        if (restricted && is_meta(e))
            return;
        if (visited.find(e) != visited.end())
            return;
        visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Sort:
            break; // do nothing
        case expr_kind::Local:
            if (!restricted)
                visit(mlocal_type(e));
            ls.insert(e);
            break;
        case expr_kind::Meta:
            lean_assert(!restricted);
            visit(mlocal_type(e));
            break;
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
            break;
        case expr_kind::App:
            visit(app_fn(e));
            visit(app_arg(e));
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            visit(binding_domain(e));
            visit(binding_body(e));
            break;
        case expr_kind::Let:
            visit(let_type(e));
            visit(let_value(e));
            visit(let_body(e));
            break;
        }
    };
    visit(e);
}

/** \brief Return true iff locals(e1) is a subset of locals(e2) */
bool locals_subset(expr const & e1, expr const & e2) {
    if (!has_local(e1)) {
        // empty set is a subset of anything
        return true;
    }
    if (!has_local(e2)) {
        lean_assert(has_local(e1));
        return false;
    }
    collected_locals S;
    collect_locals(e2, S);
    bool is_sub = true;
    for_each(e1, [&](expr const & e, unsigned) {
            if (!is_sub || !has_local(e))
                return false; // stop search
            if (is_local(e) && !S.contains(e))
                is_sub = false;
            return true;
        });
    return is_sub;
}

bool contains_local(expr const & e, name const & n) {
    if (!has_local(e))
        return false;
    bool result = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (result || !has_local(e))  {
                return false;
            } else if (is_local(e) && mlocal_name(e) == n) {
                result = true;
                return false;
            } else {
                return true;
            }
        });
    return result;
}

bool contains_local(expr const & e, name_set const & s) {
    if (!has_local(e))
        return false;
    bool result = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (result || !has_local(e))  {
                return false;
            } else if (is_local(e) && s.contains(mlocal_name(e))) {
                result = true;
                return false;
            } else {
                return true;
            }
        });
    return result;
}

optional<expr> depends_on(unsigned sz, expr const * es, expr const & h) {
    for (unsigned i = 0; i < sz; i++)
        if (depends_on(es[i], h))
            return some_expr(es[i]);
    return none_expr();
}

bool depends_on_any(expr const & e, unsigned hs_sz, expr const * hs) {
    return std::any_of(hs, hs+hs_sz, [&](expr const & h) { return depends_on(e, h); });
}

expr replace_locals(expr const & e, unsigned sz, expr const * locals, expr const * terms) {
    return instantiate_rev(abstract_locals(e, sz, locals), sz, terms);
}

expr replace_locals(expr const & e, buffer<expr> const & locals, buffer<expr> const & terms) {
    lean_assert(locals.size() == terms.size());
    lean_assert(std::all_of(locals.begin(), locals.end(), is_local));
    return replace_locals(e, locals.size(), locals.data(), terms.data());
}
}




// ========== io_state_stream.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "kernel/ext_exception.h"
#include "kernel/abstract_type_context.h"
#include "library/exception.h"
#include "library/io_state.h"

namespace lean {
/** \brief Base class for \c regular and \c diagnostic wrapper classes. */
class io_state_stream {
protected:
    environment                     m_env;
    formatter                       m_formatter;
    std::shared_ptr<output_channel> m_stream;
public:
    io_state_stream(environment const & env, formatter const & fmt, std::shared_ptr<output_channel> const & s):
        m_env(env), m_formatter(fmt), m_stream(s) {}
    io_state_stream(environment const & env, io_state const & ios, abstract_type_context & ctx, std::shared_ptr<output_channel> const & stream):
        m_env(env), m_formatter(ios.get_formatter_factory()(env, ios.get_options(), ctx)),
        m_stream(stream) {}
    io_state_stream(environment const & env, io_state const & ios, abstract_type_context & ctx, bool regular = true):
        io_state_stream(env, ios, ctx, regular ? ios.get_regular_channel_ptr() : ios.get_diagnostic_channel_ptr()) {}
    std::ostream & get_stream() const { return m_stream->get_stream(); }
    std::shared_ptr<output_channel> get_channel() const { return m_stream; }
    void flush() { get_stream().flush(); }
    formatter const & get_formatter() const { return m_formatter; }
    options get_options() const { return m_formatter.get_options(); }
    environment const & get_environment() const { return m_env; }
    io_state_stream update_options(options const & o) const { return io_state_stream(m_env, m_formatter.update_options(o), m_stream); }
};

inline io_state_stream regular(environment const & env, io_state const & ios, abstract_type_context & ctx) {
    return io_state_stream(env, ios, ctx, true);
}
inline io_state_stream diagnostic(environment const & env, io_state const & ios, abstract_type_context & ctx) {
    return io_state_stream(env, ios, ctx, false);
}

// hack for using std::endl with channels
struct endl_class { endl_class() {} };
const endl_class endl;

class ext_exception;

io_state_stream const & operator<<(io_state_stream const & out, endl_class);
io_state_stream const & operator<<(io_state_stream const & out, option_kind k);
io_state_stream const & operator<<(io_state_stream const & out, expr const & e);
io_state_stream const & operator<<(io_state_stream const & out, level const & l);
io_state_stream const & operator<<(io_state_stream const & out, ext_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, formatted_exception const & ex);
io_state_stream const & operator<<(io_state_stream const & out, format const & f);
template<typename T> io_state_stream const & display(io_state_stream const & out, T const & t) {
    out.get_stream() << t;
    return out;
}
struct display_profiling_time;
io_state_stream const & operator<<(io_state_stream const & out, display_profiling_time const &);
inline io_state_stream const & operator<<(io_state_stream const & out, char const * d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, name const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, unsigned d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, std::string const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, options const & d) { return display(out, d); }
inline io_state_stream const & operator<<(io_state_stream const & out, pair<format const &, options const &> const & d) { return display(out, d); }
}




// ========== io_state_stream.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/level.h"
#include "library/io_state_stream.h"
#include "util/timeit.h"

namespace lean {
io_state_stream const & operator<<(io_state_stream const & out, endl_class) {
    out.get_stream() << std::endl;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, option_kind k) {
    out.get_stream() << k;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr_kind const & k) {
    out.get_stream() << k;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, expr const & e) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(group(out.get_formatter()(e)), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, level const & l) {
    out.get_stream() << l;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, ext_exception const & ex) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(ex.pp(out.get_formatter()), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, format const & f) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(f, opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, formatted_exception const & ex) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(ex.pp(), opts);
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, display_profiling_time const & t) {
    out.get_stream() << t;
    return out;
}

}




// ========== scoped_ext.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "util/list.h"
#include "util/rb_map.h"
#include "util/name.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/module.h"
#include "library/fingerprint.h"

namespace lean {
enum class scope_kind { Namespace, Section };
enum class persistence { scope, file, global };

typedef environment (*push_scope_fn)(environment const &, io_state const &, scope_kind);
typedef environment (*pop_scope_fn)(environment const &, io_state const &, scope_kind);

void register_scoped_ext(push_scope_fn push, pop_scope_fn pop);

/** \brief Create a new scope, all scoped extensions are notified. */
environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n = name());
/** \brief Delete the most recent scope, all scoped extensions are notified.
    \remark method throws an exception if there are no open scopes, or \c n does not match the name of the open scope
*/
environment pop_scope(environment const & env, io_state const & ios, name const & n = name());
/** \brief Similar to \c pop_scope, but it always succeed.
    It always pops the current open scope, and does nothing if there are no open scopes.
*/
environment pop_scope_core(environment const & env, io_state const & ios);
/** \brief Return true iff there are open scopes */
bool has_open_scopes(environment const & env);

/** \brief Add a new namespace (if it does not exist) */
environment add_namespace(environment const & env, name const & ns);

name const & get_namespace(environment const & env);
name const & get_scope_header(environment const & env);
/** \brief Return the current stack of namespaces.
    Example: at
      namespace foo
      namespace bla
      namespace boo
      - It returns [foo.bla.boo, foo.bla, foo]

    \remark This is *not* the set of opened namespaces. */
list<name> const & get_namespaces(environment const & env);
bool in_section(environment const & env);

/** \brief Check if \c n may be a reference to a namespace, if it is return it.
    The procedure checks if \c n is a registered namespace, if it is not, it tries
    to prefix \c n with each prefix in the current scope. Example: suppose the scope is:
       namespace foo
         namespace bla
           namespace boo
              ...
    Then, the procedure tries n, 'foo.bla.boo'+n, 'foo.bla'+n, 'foo'+n. */
optional<name> to_valid_namespace_name(environment const & env, name const & n);

std::vector<name> get_namespace_completion_candidates(environment const & env);

/** \brief Mark the given namespace as opened */
environment mark_namespace_as_open(environment const & env, name const & n);
/** \brief Return the set of namespaces marked as "open" using \c mark_namespace_as_open. */
name_set get_opened_namespaces(environment const & env);

/** \brief Return true iff \c n is a namespace */
bool is_namespace(environment const & env, name const & n);

/** \brief Auxilary template used to simplify the creation of environment extensions that support
    the scope */
template<typename Config>
class scoped_ext : public environment_extension {
    typedef typename Config::state            state;
    typedef typename Config::entry            entry;
    static void add_entry(environment const & env, io_state const & ios, state & s, entry const & e) {
        Config::add_entry(env, ios, s, e);
    }
    static void  write_entry(serializer & s, entry const & e) { Config::write_entry(s, e); }
    static entry read_entry(deserializer & d) { return Config::read_entry(d); }
    static const char * get_serialization_key() { return Config::get_serialization_key(); }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return Config::get_fingerprint(e);
    }

    /* Stack of states, it is updated using push/pop operations */
    list<state>           m_scopes;
    state                 m_state; // explicit top-most (current) scope

    /* Add \c e to all states in \c l. */
    static list<state> add_all(environment const & env, io_state const & ios, list<state> const & l, entry const & e) {
        if (is_nil(l)) {
            return l;
        } else {
            state new_s = head(l);
            add_entry(env, ios, new_s, e);
            return cons(new_s, add_all(env, ios, tail(l), e));
        }
    }

    /* Add persistent entry, updating all states with this entry. This method is invoked when importing files. */
    scoped_ext _register_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        add_entry(env, ios, r.m_state, e);
        r.m_scopes = add_all(env, ios, r.m_scopes, e);
        return r;
    }

    /* Add entry to current state */
    scoped_ext _add_tmp_entry(environment const & env, io_state const & ios, entry const & e) const {
        scoped_ext r(*this);
        add_entry(env, ios, r.m_state, e);
        return r;
    }

public:
    /** \brief Open a namespace/section. It returns the new updated state. */
    scoped_ext push() const {
        scoped_ext r(*this);
        r.m_scopes           = cons(m_state, r.m_scopes);
        return r;
    }

    /** \brief Close namespace/section. It returns the new updated state.
        \pre There are open namespaces */
    scoped_ext pop() const {
        lean_assert(!is_nil(m_scopes));
        scoped_ext r(*this);
        r.m_state  = head(m_scopes);
        r.m_scopes = tail(m_scopes);
        return r;
    }

    struct modification : public lean::modification {
        LEAN_MODIFICATION(get_serialization_key())

        entry m_entry;

        modification() {}
        modification(entry const & e) : m_entry(e) {}

        void perform(environment & env) const override {
            env = register_entry(env, get_global_ios(), m_entry);
        }

        void serialize(serializer & s) const override {
            write_entry(s, m_entry);
        }

        static std::shared_ptr<lean::modification const> deserialize(deserializer & d) {
            return std::make_shared<modification>(read_entry(d));
        }
    };

    struct reg {
        unsigned m_ext_id;
        reg() {
            register_scoped_ext(push_fn, pop_fn);
            modification::init();
            m_ext_id = environment::register_extension(std::make_shared<scoped_ext>());
        }
        ~reg() {
            modification::finalize();
        }
    };

    static reg * g_ext;
    static void initialize() { g_ext = new reg(); }
    static void finalize() { delete g_ext; }

    static scoped_ext const & get(environment const & env) {
        return static_cast<scoped_ext const &>(env.get_extension(g_ext->m_ext_id));
    }
    static environment update(environment const & env, scoped_ext const & ext) {
        return env.update(g_ext->m_ext_id, std::make_shared<scoped_ext>(ext));
    }
    static environment push_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).push());
    }
    static environment pop_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).pop());
    }

    static environment register_entry(environment const & env, io_state const & ios, entry const & e) {
        return update(env, get(env)._register_entry(env, ios, e));
    }

    static environment add_entry(environment env, io_state const & ios, entry const & e, persistence persist) {
        if (auto h = get_fingerprint(e)) {
            env = update_fingerprint(env, *h);
        }
        if (persist == persistence::scope) {
            return update(env, get(env)._add_tmp_entry(env, ios, e));
        } else {
            if (persist == persistence::global) {
                env = module::add(env, std::make_shared<modification>(e));
            }
            return update(env, get(env)._register_entry(env, ios, e));
        }
    }

    static environment add_entry(environment const & env, io_state const & ios, entry const & e, bool persistent) {
        return add_entry(env, ios, e, persistent ? persistence::global : persistence::scope);
    }

    static state const & get_state(environment const & env) {
        return get(env).m_state;
    }
};

template<typename Config>
typename scoped_ext<Config>::reg * scoped_ext<Config>::g_ext = nullptr;


void initialize_scoped_ext();
void finalize_scoped_ext();
}




// ========== scoped_ext.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "library/scoped_ext.h"

namespace lean {
typedef std::tuple<push_scope_fn, pop_scope_fn> entry;
typedef std::vector<entry> scoped_exts;
static scoped_exts * g_exts = nullptr;
static scoped_exts & get_exts() { return *g_exts; }

void register_scoped_ext(push_scope_fn push, pop_scope_fn pop) {
    get_exts().emplace_back(push, pop);
}

struct scope_mng_ext : public environment_extension {
    name_set         m_namespace_set;     // all namespaces registered in the system
    name_set         m_opened_namespaces; // set of namespaces marked as "open"
    list<name>       m_namespaces;        // stack of namespaces/sections
    list<name>       m_headers;           // namespace/section header
    list<scope_kind> m_scope_kinds;
};

struct scope_mng_ext_reg {
    unsigned m_ext_id;
    scope_mng_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<scope_mng_ext>()); }
};

static scope_mng_ext_reg * g_ext = nullptr;
static scope_mng_ext const & get_extension(environment const & env) {
    return static_cast<scope_mng_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, scope_mng_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<scope_mng_ext>(ext));
}

name const & get_namespace(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_namespaces) ? head(ext.m_namespaces) : name::anonymous();
}

name const & get_scope_header(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_namespaces) ? head(ext.m_headers) : name::anonymous();
}

list<name> const & get_namespaces(environment const & env) {
    return get_extension(env).m_namespaces;
}

bool in_section(environment const & env) {
    scope_mng_ext const & ext = get_extension(env);
    return !is_nil(ext.m_scope_kinds) && head(ext.m_scope_kinds) == scope_kind::Section;
}

environment mark_namespace_as_open(environment const & env, name const & n) {
    scope_mng_ext ext = get_extension(env);
    ext.m_opened_namespaces.insert(n);
    return update(env, ext);
}

name_set get_opened_namespaces(environment const & env) {
    return get_extension(env).m_opened_namespaces;
}

bool is_namespace(environment const & env, name const & n) {
    return get_extension(env).m_namespace_set.contains(n);
}

optional<name> to_valid_namespace_name(environment const & env, name const & n) {
    scope_mng_ext const & ext = get_extension(env);
    if (ext.m_namespace_set.contains(n))
        return optional<name>(n);
    for (auto const & ns : ext.m_namespaces) {
        name r = ns + n;
        if (ext.m_namespace_set.contains(r))
            return optional<name>(r);
    }
    return optional<name>();
}

std::vector<name> get_namespace_completion_candidates(environment const & env) {
    std::vector<name> ret;
    scope_mng_ext const & ext = get_extension(env);
    ext.m_namespace_set.for_each([&](name const & ns) {
        ret.push_back(ns);
        for (auto const & open_ns : ext.m_namespaces)
            if (open_ns != ns && is_prefix_of(open_ns, ns))
                ret.push_back(ns.replace_prefix(open_ns, {}));
    });
    return ret;
}

struct new_namespace_modification : public modification {
    LEAN_MODIFICATION("nspace")

    name m_ns;

    new_namespace_modification(name const & ns) : m_ns(ns) {}
    new_namespace_modification() {}

    void perform(environment & env) const override {
        scope_mng_ext ext = get_extension(env);
        ext.m_namespace_set.insert(m_ns);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_ns;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n;
        d >> n;
        return std::make_shared<new_namespace_modification>(n);
    }
};

environment add_namespace(environment const & env, name const & ns) {
    scope_mng_ext ext = get_extension(env);
    if (!ext.m_namespace_set.contains(ns)) {
        ext.m_namespace_set.insert(ns);
        environment r = update(env, ext);
        r = module::add(r, std::make_shared<new_namespace_modification>(ns));
        if (ns.is_atomic())
            return r;
        else
            return add_namespace(r, ns.get_prefix());
    } else {
        return env;
    }
}

environment push_scope(environment const & env, io_state const & ios, scope_kind k, name const & n) {
    if (k == scope_kind::Namespace && in_section(env))
        throw exception("invalid namespace declaration, a namespace cannot be declared inside a section");
    name new_n = get_namespace(env);
    if (k == scope_kind::Namespace)
        new_n = new_n + n;
    scope_mng_ext ext = get_extension(env);
    bool save_ns = false;
    if (!ext.m_namespace_set.contains(new_n)) {
        save_ns  = true;
        ext.m_namespace_set.insert(new_n);
    }
    ext.m_namespaces  = cons(new_n, ext.m_namespaces);
    ext.m_headers     = cons(n, ext.m_headers);
    ext.m_scope_kinds = cons(k, ext.m_scope_kinds);
    environment r = update(env, ext);
    for (auto const & t : get_exts()) {
        r = std::get<0>(t)(r, ios, k);
    }
    if (save_ns)
        r = module::add(r, std::make_shared<new_namespace_modification>(new_n));
    return r;
}

environment pop_scope_core(environment const & env, io_state const & ios) {
    scope_mng_ext ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        return env;
    scope_kind k      = head(ext.m_scope_kinds);
    ext.m_namespaces  = tail(ext.m_namespaces);
    ext.m_headers     = tail(ext.m_headers);
    ext.m_scope_kinds = tail(ext.m_scope_kinds);
    environment r = update(env, ext);
    for (auto const & t : get_exts()) {
        r = std::get<1>(t)(r, ios, k);
    }
    return r;
}

environment pop_scope(environment const & env, io_state const & ios, name const & n) {
    scope_mng_ext ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        throw exception("invalid end of scope, there are no open namespaces/sections");
    if (n != head(ext.m_headers))
        throw exception(sstream() << "invalid end of scope, begin/end mismatch, scope starts with '"
                        << head(ext.m_headers) << "', and ends with '" << n << "'");
    return pop_scope_core(env, ios);
}

bool has_open_scopes(environment const & env) {
    scope_mng_ext ext = get_extension(env);
    return !is_nil(ext.m_namespaces);
}

void initialize_scoped_ext() {
    g_exts = new scoped_exts();
    g_ext  = new scope_mng_ext_reg();
    new_namespace_modification::init();
}

void finalize_scoped_ext() {
    new_namespace_modification::finalize();
    delete g_exts;
    delete g_ext;
}
}




// ========== noncomputable.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
bool is_marked_noncomputable(environment const & env, name const & n);
/** \brief Return true if \c n is noncomputable */
bool is_noncomputable(environment const & env, name const & n);
/** \brief Mark \c n as noncomputable */
environment mark_noncomputable(environment const & env, name const & n);
/** \brief In standard mode, check if definitions that are not propositions can compute */
bool check_computable(environment const & env, name const & n);
optional<name> get_noncomputable_reason(environment const & env, name const & n);
void initialize_noncomputable();
void finalize_noncomputable();
}




// ========== noncomputable.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/util.h"
#include "library/fingerprint.h"
#include "library/trace.h"
#include "library/quote.h"
#include "library/constants.h"
// TODO(Leo): move inline attribute declaration to library
#include "library/compiler/inliner.h"
namespace lean {
struct noncomputable_ext : public environment_extension {
    name_set m_noncomputable;
    noncomputable_ext() {}
};

struct noncomputable_ext_reg {
    unsigned m_ext_id;
    noncomputable_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<noncomputable_ext>());
    }
};

static noncomputable_ext_reg * g_ext = nullptr;
static noncomputable_ext const & get_extension(environment const & env) {
    return static_cast<noncomputable_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, noncomputable_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<noncomputable_ext>(ext));
}

struct noncomputable_modification : public modification {
    LEAN_MODIFICATION("ncomp")

    name m_decl;

    noncomputable_modification() {}
    noncomputable_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        noncomputable_ext ext = get_extension(env);
        ext.m_noncomputable.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<noncomputable_modification>(read_name(d));
    }
};

// TODO(Leo): implement better support for extending this set of builtin constants
static bool is_builtin_extra(name const & n) {
    return
        n == get_io_core_name() ||
        n == get_monad_io_impl_name() ||
        n == get_monad_io_terminal_impl_name() ||
        n == get_monad_io_file_system_impl_name() ||
        n == get_monad_io_environment_impl_name() ||
        n == get_monad_io_process_impl_name() ||
        n == get_monad_io_random_impl_name();
}

static bool is_noncomputable(type_checker & tc, noncomputable_ext const & ext, name const & n) {
    environment const & env = tc.env();
    if (ext.m_noncomputable.contains(n))
        return true;
    declaration const & d = env.get(n);
    if (!d.is_trusted()) {
        return false; /* ignore nontrusted definitions */
    } else if (d.is_axiom() && !tc.is_prop(d.get_type())) {
        return true;
    } else if (d.is_constant_assumption()) {
        return !env.is_builtin(d.get_name()) && !tc.is_prop(d.get_type()) && !is_builtin_extra(d.get_name());
    } else {
        return false;
    }
}

bool is_noncomputable(environment const & env, name const & n) {
    type_checker tc(env);
    auto ext = get_extension(env);
    return is_noncomputable(tc, ext, n);
}

bool is_marked_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    return ext.m_noncomputable.contains(n);
}

environment mark_noncomputable(environment const & env, name const & n) {
    auto ext = get_extension(env);
    ext.m_noncomputable.insert(n);
    environment new_env = update(env, ext);
    return module::add(new_env, std::make_shared<noncomputable_modification>(n));
}

struct get_noncomputable_reason_fn {
    struct found {
        name m_reason;
        found(name const & r):m_reason(r) {}
    };

    type_checker &            m_tc;
    noncomputable_ext const & m_ext;
    expr_set                  m_cache;

    get_noncomputable_reason_fn(type_checker & tc):
        m_tc(tc), m_ext(get_extension(tc.env())) {
    }

    void visit_constant(expr const & e) {
        if (is_noncomputable(m_tc, m_ext, const_name(e)))
            throw found(const_name(e));
    }

    bool should_visit(expr const & e) {
        if (m_cache.find(e) != m_cache.end())
            return false;
        m_cache.insert(e);
        expr type = m_tc.whnf(m_tc.infer(e));
        if (m_tc.is_prop(type) || is_sort(type))
            return false;
        while (is_pi(type)) {
            expr l = mk_local(m_tc.next_name(), binding_name(type), binding_domain(type), binding_info(type));
            type = m_tc.whnf(instantiate(binding_body(type), l));
        }
        return !is_sort(type);
    }

    void visit_macro(expr const & e) {
        if (is_expr_quote(e) || is_pexpr_quote(e))
            return;
        if (should_visit(e)) {
            for (unsigned i = 0; i < macro_num_args(e); i++)
                visit(macro_arg(e, i));
        }
    }

    void visit_app(expr const & e) {
        if (should_visit(e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            if (is_constant(fn) && is_inline(m_tc.env(), const_name(fn))) {
                if (auto new_e = unfold_app(m_tc.env(), e)) {
                    visit(*new_e);
                    return;
                }
            }
            visit(fn);
            for (expr const & arg : args)
                visit(arg);
        }
    }

    void visit_binding(expr const & _e) {
        if (should_visit(_e)) {
            buffer<expr> ls;
            expr e = _e;
            while (is_lambda(e) || is_pi(e)) {
                expr d = instantiate_rev(binding_domain(e), ls.size(), ls.data());
                expr l = mk_local(m_tc.next_name(), binding_name(e), d, binding_info(e));
                ls.push_back(l);
                e = binding_body(e);
            }
            visit(instantiate_rev(e, ls.size(), ls.data()));
        }
    }

    void visit_let(expr const & e) {
        if (should_visit(e)) {
            visit(instantiate(let_body(e), let_value(e)));
        }
    }

    void visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Sort:      return;
        case expr_kind::Macro:     visit_macro(e);    return;
        case expr_kind::Constant:  visit_constant(e); return;
        case expr_kind::Var:       lean_unreachable();
        case expr_kind::Meta:      lean_unreachable();
        case expr_kind::Local:     return;
        case expr_kind::App:       visit_app(e);      return;
        case expr_kind::Lambda:    visit_binding(e);  return;
        case expr_kind::Pi:        visit_binding(e);  return;
        case expr_kind::Let:       visit_let(e);      return;
        }
    }

    void operator()(expr const & e) {
        visit(e);
    }
};

optional<name> get_noncomputable_reason(environment const & env, name const & n) {
    declaration const & d = env.get(n);
    if (!d.is_definition())
        return optional<name>();
    type_checker tc(env);
    if (tc.is_prop(d.get_type()))
        return optional<name>(); // definition is a proposition, then do nothing
    expr const & v = d.get_value();
    auto ext = get_extension(env);
    bool ok  = true;
    /* quick check */
    for_each(v, [&](expr const & e, unsigned) {
            if (!ok) return false; // stop the search
            if (is_constant(e) && is_noncomputable(tc, ext, const_name(e))) {
                ok = false;
            }
            return true;
        });
    if (ok) {
        return optional<name>();
    }
    /* expensive check */
    try {
        get_noncomputable_reason_fn proc(tc);
        proc(v);
        return optional<name>();
    } catch (get_noncomputable_reason_fn::found & r) {
        return optional<name>(r.m_reason);
    }
}

bool check_computable(environment const & env, name const & n) {
    return !get_noncomputable_reason(env, n);
}

void initialize_noncomputable() {
    g_ext           = new noncomputable_ext_reg();
    noncomputable_modification::init();
}

void finalize_noncomputable() {
    noncomputable_modification::finalize();
    delete g_ext;
}
}




// ========== norm_num.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include <unordered_map>
#include <string>
#include "util/name_map.h"
#include "util/numerics/mpq.h"
#include "kernel/environment.h"
#include "library/type_context.h"
#include "library/num.h"
#include "library/arith_instance.h"

namespace lean {
class norm_num_context {
    type_context_old & m_ctx;
    arith_instance m_ainst;

    pair<expr, expr> mk_norm_add(expr const &, expr const &);
    pair<expr, expr> mk_norm_add1(expr const &);
    pair<expr, expr> mk_norm_mul(expr const &, expr const &);
    expr mk_const(name const & n);
    expr mk_cong(expr const &, expr const &, expr const &, expr const &, expr const &);
    expr mk_zero() { return m_ainst.mk_zero(); }
    expr mk_one() { return m_ainst.mk_one(); }
    expr mk_add(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_add(), e1, e2); }
    expr mk_neg(expr const & e) { return mk_app(m_ainst.mk_neg(), e); }
    expr mk_mul(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_mul(), e1, e2); }
    expr mk_div(expr const & e1, expr const & e2) { return mk_app(m_ainst.mk_div(), e1, e2); }
    expr mk_bit0(expr const & e1) { return mk_app(m_ainst.mk_bit0(), e1); }
    expr mk_bit1(expr const & e1) { return mk_app(m_ainst.mk_bit1(), e1); }

    expr mk_has_zero() { return m_ainst.mk_has_zero(); }
    expr mk_has_one() { return m_ainst.mk_has_one(); }
    expr mk_has_add() { return m_ainst.mk_has_add(); }
    expr mk_has_sub() { return m_ainst.mk_has_sub(); }
    expr mk_has_neg() { return m_ainst.mk_has_neg(); }
    expr mk_has_mul() { return m_ainst.mk_has_mul(); }
    expr mk_has_div() { return m_ainst.mk_has_div(); }

    expr mk_add_monoid() { return m_ainst.mk_add_monoid(); }
    expr mk_monoid() { return m_ainst.mk_monoid(); }
    expr mk_distrib() { return m_ainst.mk_distrib(); }
    expr mk_add_comm() { return m_ainst.mk_add_comm_semigroup(); }
    expr mk_add_comm_group() { return m_ainst.mk_add_comm_group(); }
    expr mk_add_group() { return m_ainst.mk_add_group(); }
    expr mk_mul_zero_class() { return m_ainst.mk_mul_zero_class(); }
    expr mk_ring() { return m_ainst.mk_ring(); }
    expr mk_semiring() { return m_ainst.mk_semiring(); }
    expr mk_field() { return m_ainst.mk_field(); }
    expr mk_lin_ord_semiring() { return m_ainst.mk_linear_ordered_semiring(); }
    expr mk_lin_ord_ring() { return m_ainst.mk_linear_ordered_ring(); }
    expr mk_partial_order() { return m_ainst.mk_partial_order(); }

    expr mk_num(mpq const & q) { return m_ainst.mk_num(q); }

    expr mk_pos_prf(expr const &);
    expr mk_nonneg_prf(expr const &);
    expr mk_norm_eq_neg_add_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_add_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_add_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_add_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_mul_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_neg_mul_pos(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_mul_neg(expr const &, expr const &, expr const &);
    expr mk_norm_eq_pos_mul_pos(expr const &, expr const &, expr const &);
    expr mk_norm_div_add(expr const &, expr const &, expr const &);
    expr mk_norm_add_div(expr const &, expr const &, expr const &);
    expr mk_norm_div_mul(expr const &, expr const &, expr const &);
    expr mk_norm_mul_div(expr const &, expr const &, expr const &);
    expr_pair mk_norm_nat_sub(expr const &, expr const &);
    expr mk_nonzero_prf(expr const & e);
    pair<expr, expr> get_type_and_arg_of_neg(expr const &);

    bool is_numeral(expr const & e) const;
    bool is_neg_app(expr const &) const;
    bool is_div(expr const &) const;
    bool is_nat_const(expr const &) const;
    mpq mpq_of_expr(expr const & e);
    optional<mpq> to_mpq(expr const & e);
    expr mk_norm_eq(expr const &, expr const &);

public:
    norm_num_context(type_context_old & ctx): m_ctx(ctx), m_ainst(ctx) {}

    pair<expr, expr> mk_norm(expr const & e);
};

inline pair<expr, expr> mk_norm_num(type_context_old & ctx, expr const & e) {
    return norm_num_context(ctx).mk_norm(e);
}
}




// ========== norm_num.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/trace.h"
#include "library/norm_num.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/comp_val.h"

namespace lean {
bool norm_num_context::is_numeral(expr const & e) const {
    return is_num(e);
}

bool norm_num_context::is_nat_const(expr const & e) const {
    return is_constant(e) && const_name(e) == get_nat_name();
}

bool norm_num_context::is_neg_app(expr const & e) const {
    return is_const_app(e, get_has_neg_neg_name(), 3);
}

bool norm_num_context::is_div(expr const & e) const {
    return is_const_app(e, get_has_div_div_name(), 4);
}

expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_ainst.get_levels());
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a,
                               expr const & b, expr const & eq) {
    return mk_app({mk_const(get_norm_num_mk_cong_name()), type, op, a, b, eq});
}

// returns <t, p> such that p is a proof that lhs + rhs = t.
pair<expr, expr> norm_num_context::mk_norm_add(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_lhs[0];
    auto typec = args_lhs[1];
    expr rv;
    expr prf;
    if (is_bit0(lhs) && is_bit0(rhs)) { // typec is has_add
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
        rv = mk_app(lhs_head, type, typec, p.first);
        prf = mk_app({mk_const(get_norm_num_bit0_add_bit0_helper_name()), type, mk_add_comm(),
                    args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs) && is_bit1(rhs)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[3]);
        rv = mk_app({rhs_head, type, args_rhs[1], args_rhs[2], p.first});
        prf = mk_app({mk_const(get_norm_num_bit0_add_bit1_helper_name()), type, mk_add_comm(), args_rhs[1],
                    args_lhs[2], args_rhs[3], p.first, p.second});
    } else if (is_bit0(lhs) && is_one(rhs)) {
        rv  = mk_bit1(args_lhs[2]);
        prf = mk_app({mk_const(get_norm_num_bit0_add_one_name()), type, typec, args_rhs[1], args_lhs[2]});
    } else if (is_bit1(lhs) && is_bit0(rhs)) { // typec is has_one
        auto p = mk_norm_add(args_lhs[3], args_rhs[2]);
        rv  = mk_app(lhs_head, type, typec, args_lhs[2], p.first);
        prf = mk_app({mk_const(get_norm_num_bit1_add_bit0_helper_name()), type, mk_add_comm(), typec,
                    args_lhs[3], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs) && is_bit1(rhs)) { // typec is has_one
        auto add_ts = mk_norm_add(args_lhs[3], args_rhs[3]);
        expr add1   = mk_app({mk_const(get_norm_num_add1_name()), type, args_lhs[2], typec, add_ts.first});
        auto p = mk_norm_add1(add1);
        rv  = mk_bit0(p.first);
        prf = mk_app({mk_const(get_norm_num_bit1_add_bit1_helper_name()), type, mk_add_comm(), typec,
                    args_lhs[3], args_rhs[3], add_ts.first, p.first, add_ts.second, p.second});
    } else if (is_bit1(lhs) && is_one(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(get_norm_num_add1_name()), type, args_lhs[2], typec, lhs});
        auto p = mk_norm_add1(add1);
        rv = p.first;
        prf = mk_app({mk_const(get_norm_num_bit1_add_one_helper_name()), type, args_lhs[2], typec,
                    args_lhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_bit0(rhs)) { // typec is has_one
        rv  = mk_bit1(args_rhs[2]);
        prf = mk_app({mk_const(get_norm_num_one_add_bit0_name()), type, mk_add_comm(), typec, args_rhs[2]});
    } else if (is_one(lhs) && is_bit1(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(get_norm_num_add1_name()), type, args_rhs[2], args_rhs[1], rhs});
        auto p = mk_norm_add1(add1);
        rv  = p.first;
        prf = mk_app({mk_const(get_norm_num_one_add_bit1_helper_name()), type, mk_add_comm(), typec,
                    args_rhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_one(rhs)) {
        rv  = mk_bit0(lhs);
        prf = mk_app({mk_const(get_norm_num_one_add_one_name()), type, mk_has_add(), typec});
    } else if (is_zero(lhs)) {
        rv  = rhs;
        prf = mk_app({mk_const(get_norm_num_bin_zero_add_name()), type, mk_add_monoid(), rhs});
    } else if (is_zero(rhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_norm_num_bin_add_zero_name()), type, mk_add_monoid(), lhs});
    } else {
        throw exception("mk_norm_add got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_add1(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr p = args[3];
    buffer<expr> ne_args;
    expr ne = get_app_args(p, ne_args);
    expr rv;
    expr prf;
    // args[1] = has_add, args[2] = has_one
    if (is_bit0(p)) {
        auto has_one = args[2];
        rv  = mk_bit1(ne_args[2]);
        prf = mk_app({mk_const(get_norm_num_add1_bit0_name()), args[0], args[1], args[2], ne_args[2]});
    } else if (is_bit1(p)) { // ne_args : has_one, has_add
        auto np = mk_norm_add1(mk_app({mk_const(get_norm_num_add1_name()), args[0], args[1], args[2], ne_args[3]}));
        rv  = mk_bit0(np.first);
        prf = mk_app({mk_const(get_norm_num_add1_bit1_helper_name()), args[0], mk_add_comm(),
                    args[2], ne_args[3], np.first, np.second});
    } else if (is_zero(p)) {
        rv  = mk_one();
        prf = mk_app({mk_const(get_norm_num_add1_zero_name()), args[0], mk_add_monoid(), args[2]});
    } else if (is_one(p)) {
        rv  = mk_bit0(mk_one());
        prf = mk_app({mk_const(get_norm_num_add1_one_name()), args[0], args[1], args[2]});
    } else {
        throw exception("malformed add1");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_mul(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_rhs[0];
    auto typec = args_rhs[1];
    expr rv;
    expr prf;
    if (is_zero(rhs)) {
        rv  = rhs;
        prf = mk_app({mk_const(get_mul_zero_name()), type, mk_mul_zero_class(), lhs});
    } else if (is_zero(lhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_zero_mul_name()), type, mk_mul_zero_class(), rhs});
    } else if (is_one(rhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_mul_one_name()), type, mk_monoid(), lhs});
    } else if (is_bit0(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[2]);
        rv  = mk_app({rhs_head, type, typec, mtp.first});
        prf = mk_app({mk_const(get_norm_num_mul_bit0_helper_name()), type, mk_distrib(), lhs,
                    args_rhs[2], mtp.first, mtp.second});
    } else if (is_bit1(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[3]);
        auto atp = mk_norm_add(mk_bit0(mtp.first), lhs);
        rv  = atp.first;
        prf = mk_app({mk_const(get_norm_num_mul_bit1_helper_name()), type, mk_semiring(), lhs, args_rhs[3],
                    mtp.first, atp.first, mtp.second, atp.second});
    } else {
        throw exception("mk_norm_mul got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

optional<mpq> norm_num_context::to_mpq(expr const & e) {
    auto v = to_num(e);
    if (v) {
        return optional<mpq>(mpq(*v));
    } else {
        return optional<mpq>();
    }
}

mpq norm_num_context::mpq_of_expr(expr const & e) {
    if (auto r = m_ainst.eval(e))
        return *r;
    else
        throw exception("failed to evaluate arithmetic expression");
}

pair<expr, expr> norm_num_context::get_type_and_arg_of_neg(expr const & e) {
    lean_assert(is_neg_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    return pair<expr, expr>(args[0], args[2]);
}

// returns a proof that s_lhs + s_rhs = rhs, where all are negated numerals
expr norm_num_context::mk_norm_eq_neg_add_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    auto s_rhs_v = get_type_and_arg_of_neg(s_rhs).second;
    auto rhs_v = get_type_and_arg_of_neg(rhs);
    expr type = rhs_v.first;
    auto sum_pr = mk_norm(mk_add(s_lhs_v, s_rhs_v)).second;
    return mk_app({mk_const(get_norm_num_neg_add_neg_helper_name()), type, mk_add_comm_group(),
                s_lhs_v, s_rhs_v, rhs_v.second, sum_pr});
}

expr norm_num_context::mk_norm_eq_neg_add_pos(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs);
    expr type = s_lhs_v.first;
    if (is_neg_app(rhs)) {
        auto rhs_v = get_type_and_arg_of_neg(rhs).second;
        auto sum_pr = mk_norm(mk_add(s_rhs, rhs_v)).second;
        return mk_app({mk_const(get_norm_num_neg_add_pos_helper1_name()), type, mk_add_comm_group(),
                    s_lhs_v.second, s_rhs, rhs_v, sum_pr});
    } else {
        auto sum_pr = mk_norm(mk_add(s_lhs_v.second, rhs)).second;
        return mk_app({mk_const(get_norm_num_neg_add_pos_helper2_name()), type, mk_add_comm_group(),
                    s_lhs_v.second, s_rhs, rhs, sum_pr});
    }
}

expr norm_num_context::mk_norm_eq_pos_add_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_rhs));
    lean_assert(!is_neg_app(s_lhs));
    expr prf = mk_norm_eq_neg_add_pos(s_rhs, s_lhs, rhs);
    expr type = get_type_and_arg_of_neg(s_rhs).first;
    return mk_app({mk_const(get_norm_num_pos_add_neg_helper_name()), type, mk_add_comm_group(), s_lhs,
                s_rhs, rhs, prf});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_add_pos(expr const & s_lhs, expr const & s_rhs, expr const & DEBUG_CODE(rhs)) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_add(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

expr norm_num_context::mk_norm_eq_neg_mul_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto prod_pr = mk_norm(mk_mul(s_lhs_v, s_rhs_v));
    lean_assert(to_num(rhs) == to_num(prod_pr.first));
    return mk_app({mk_const(get_norm_num_neg_mul_neg_helper_name()), type, mk_ring(), s_lhs_v,
                s_rhs_v, rhs, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_neg_mul_pos(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_lhs_v, type;
    std::tie(type, s_lhs_v) = get_type_and_arg_of_neg(s_lhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(s_lhs_v, s_rhs));
    return mk_app({mk_const(get_norm_num_neg_mul_pos_helper_name()), type, mk_ring(), s_lhs_v, s_rhs,
                rhs_v, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_pos_mul_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(s_lhs, s_rhs_v));
    return mk_app({mk_const(get_norm_num_pos_mul_neg_helper_name()), type, mk_ring(), s_lhs, s_rhs_v,
                rhs_v, prod_pr.second});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_mul_pos(expr const & s_lhs, expr const & s_rhs, expr const & DEBUG_CODE(rhs)) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_mul(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

// s_lhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_div_add(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> s_lhs_args;
    get_app_args(s_lhs, s_lhs_args);
    expr type = s_lhs_args[0];
    expr num = s_lhs_args[2], den = s_lhs_args[3];
    expr new_lhs = mk_add(num, mk_mul(s_rhs, den));
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(rhs, den));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(get_norm_num_div_add_helper_name()), type, mk_field(), num, den, s_rhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// s_rhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_add_div(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> s_rhs_args;
    get_app_args(s_rhs, s_rhs_args);
    expr type = s_rhs_args[0];
    expr num = s_rhs_args[2], den = s_rhs_args[3];
    expr new_lhs = mk_add(mk_mul(den, s_lhs), num);
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(den, rhs));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(get_norm_num_add_div_helper_name()), type, mk_field(), num, den, s_lhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// if e is a numeral or a negation of a numeral or division, returns proof that e != 0
expr norm_num_context::mk_nonzero_prf(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (const_name(f) == get_has_neg_neg_name()) {
        return mk_app({mk_const(get_norm_num_nonzero_of_neg_helper_name()), args[0], mk_lin_ord_ring(),
                    args[2], mk_nonzero_prf(args[2])});
    } else if (const_name(f) == get_has_div_div_name()) {
        expr num_pr = mk_nonzero_prf(args[2]), den_pr = mk_nonzero_prf(args[3]);
        return mk_app({mk_const(get_norm_num_nonzero_of_div_helper_name()), args[0], mk_field(), args[2],
                    args[3], num_pr, den_pr});
    } else {
        return mk_app({mk_const(get_norm_num_nonzero_of_pos_helper_name()), args[0], mk_lin_ord_semiring(),
                    e, mk_pos_prf(e)});
    }
}

// if e is a numeral, makes a proof that e > 0
expr norm_num_context::mk_pos_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_pos_prf(args[2]);
        return mk_app({mk_const(get_norm_num_pos_bit0_helper_name()), type, mk_lin_ord_semiring(), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(get_norm_num_pos_bit1_helper_name()), type, mk_lin_ord_semiring(), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(get_zero_lt_one_name()), type, mk_lin_ord_semiring()});
    } else {
        throw exception("mk_pos_proof called on zero or non_numeral");
    }
}

expr norm_num_context::mk_nonneg_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_nonneg_prf(args[2]);
        return mk_app({mk_const(get_norm_num_nonneg_bit0_helper_name()), type, mk_lin_ord_semiring(), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(get_norm_num_nonneg_bit1_helper_name()), type, mk_lin_ord_semiring(), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(get_zero_le_one_name()), type, mk_lin_ord_semiring()});
    } else if (is_zero(e)) {
        return mk_app({mk_const(get_le_refl_name()), type, mk_partial_order(), mk_zero()});
    } else {
        throw exception("mk_nonneg_proof called on zero or non_numeral");
    }
}

// s_lhs is div. returns proof that s_lhs * s_rhs = rhs
expr norm_num_context::mk_norm_div_mul(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> args;
    get_app_args(s_lhs, args);
    expr type = args[0];
    expr new_num = mk_mul(args[2], s_rhs);
    auto prf = mk_norm(mk_div(new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    expr den_ne_zero = mk_nonzero_prf(args[3]);
    return mk_app({mk_const(get_norm_num_div_mul_helper_name()), type, mk_field(), args[2], args[3], s_rhs,
                rhs, den_ne_zero, prf.second});
}

expr norm_num_context::mk_norm_mul_div(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> args;
    get_app_args(s_rhs, args);
    expr type = args[0];
    expr new_num = mk_mul(s_lhs, args[2]);
    auto prf = mk_norm(mk_div(new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    expr den_ne_zero = mk_nonzero_prf(args[3]);
    return mk_app({mk_const(get_norm_num_mul_div_helper_name()), type, mk_field(), s_lhs, args[2], args[3],
                rhs, den_ne_zero, prf.second});
}

expr_pair norm_num_context::mk_norm_nat_sub(expr const & s_lhs, expr const & s_rhs) {
    auto norm_lhs = mk_norm(s_lhs);
    auto norm_rhs = mk_norm(s_rhs);
    mpq vall = mpq_of_expr(norm_lhs.first);
    mpq valr = mpq_of_expr(norm_rhs.first);
    if (valr > vall) {
        if (auto lt_pr = mk_nat_val_lt_proof(norm_lhs.first, norm_rhs.first)) {
            expr zeropr = mk_app({mk_constant(get_norm_num_sub_nat_zero_helper_name()),
                        s_lhs, s_rhs, norm_lhs.first, norm_rhs.first, norm_lhs.second, norm_rhs.second, *lt_pr});
            return expr_pair(mk_zero(), zeropr);
        } else {
            throw exception("mk_norm_nat_sub failed to make lt proof");
        }
    } else {
        expr e = mk_num(vall - valr);
        auto seq_pr = mk_norm(mk_add(e, norm_rhs.first));
        expr rpr = mk_app({mk_constant(get_norm_num_sub_nat_pos_helper_name()),
                    s_lhs, s_rhs, norm_lhs.first, norm_rhs.first, e, norm_lhs.second, norm_rhs.second, seq_pr.second});
        return expr_pair(e, rpr);
    }
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f) || args.size() == 0) {
        throw exception("malformed argument to mk_norm");
    }
    expr type = args[0];
    m_ainst.set_type(type);
    if (is_numeral(e)) {
        expr prf = mk_eq_refl(m_ctx, e);
        return pair<expr, expr>(e, prf);
    }
    mpq val   = mpq_of_expr(e);
    expr nval = mk_num(val);

    if (const_name(f) == get_has_add_add_name() && args.size() == 4) {
        expr prf;
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_neg_add_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                if (is_div(lhs_p.first)) {
                    prf = mk_norm_div_add(lhs_p.first, rhs_p.first, nval);
                } else if (is_div(rhs_p.first)) {
                    prf = mk_norm_add_div(lhs_p.first, rhs_p.first, nval);
                } else {
                    prf = mk_norm_eq_pos_add_pos(lhs_p.first, rhs_p.first, nval);
                }
            }
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_sum_name()), type, mk_has_add(), args[2], args[3],
                    lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);

    } else if (const_name(f) == get_has_sub_sub_name() && args.size() == 4) {
        if (is_nat_const(args[0])) {
            return mk_norm_nat_sub(args[2], args[3]);
        }
        expr sum = mk_add(args[2], mk_neg(args[3]));
        auto anprf = mk_norm(sum);
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_subtr_name()), type, mk_add_group(), args[2],
            args[3], anprf.first, anprf.second});
        return expr_pair(nval, rprf);
    } else if (const_name(f) == get_has_neg_neg_name()  && args.size() == 3) {
        auto prf = mk_norm(args[2]);
        lean_assert(mpq_of_expr(prf.first) == neg(val));
        if (is_zero(prf.first)) {
            expr rprf = mk_app({mk_const(get_norm_num_neg_zero_helper_name()), type, mk_add_group(), args[2],
                        prf.second});
            return pair<expr, expr>(prf.first, rprf);
        }

        if (is_neg_app(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2],
                                nval_args[2], prf.second);
            return pair<expr, expr>(nval, rprf);
        } else {
            expr rprf = mk_app({mk_const(get_norm_num_neg_neg_helper_name()), type, mk_add_group(),
                        args[2], nval, prf.second});
            return pair<expr, expr>(nval, rprf);
        }
    } else if (const_name(f) == get_has_mul_mul_name() && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_div(lhs_p.first)) {
            prf = mk_norm_div_mul(lhs_p.first, rhs_p.first, nval);
        } else if (is_div(rhs_p.first)) {
            prf = mk_norm_mul_div(lhs_p.first, rhs_p.first, nval);
        } else if (is_zero(lhs_p.first) || is_zero(rhs_p.first)) {
            prf = mk_norm_mul(lhs_p.first, rhs_p.first).second;
        } else if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else { // bad args passing here
                prf = mk_norm_eq_neg_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_pos_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_prod_name()), type, mk_has_mul(), args[2], args[3],
                          lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_has_div_div_name() && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_div(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr nval_num = nval_args[2], nval_den = nval_args[3];
            auto lhs_mul = mk_norm(mk_mul(lhs_p.first, nval_den));
            auto rhs_mul = mk_norm(mk_mul(nval_num, rhs_p.first));
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            expr nval_den_nonzero = mk_nonzero_prf(nval_den);
            prf = mk_app({mk_const(get_norm_num_div_eq_div_helper_name()), type, mk_field(),
                        lhs_p.first, rhs_p.first, nval_num, nval_den, lhs_mul.first,
                        lhs_mul.second, rhs_mul.second, den_nonzero, nval_den_nonzero});
        } else {
            auto prod = mk_norm(mk_mul(nval, rhs_p.first));
            auto val1 = to_mpq(prod.first), val2 = to_mpq(lhs_p.first);
            if (val1 && val2) {
                lean_assert(*val1 == *val2);
            }
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            prf = mk_app({mk_const(get_norm_num_div_helper_name()), type, mk_field(),
                        lhs_p.first, rhs_p.first, nval, den_nonzero, prod.second});
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_div_name()), type, mk_has_div(),
                    lhs_p.first, rhs_p.first, args[2], args[3], nval, prf,
                    lhs_p.second, rhs_p.second});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit0_name() && args.size() == 3) {
        lean_assert(is_bit0(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[2]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2], nval_args[2], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit1_name() && args.size() == 4) {
        lean_assert(is_bit1(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[3]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1], args[2]), type, args[3],
                            nval_args[3], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if ((const_name(f) == get_has_zero_zero_name() || const_name(f) == get_has_one_one_name())
               && args.size() == 2) {
        return pair<expr, expr>(e, mk_eq_refl(m_ctx, e));
    } else {
        throw exception("mk_norm found unrecognized combo ");
    }
}
}




// ========== module_mgr.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "frontends/lean/module_parser.h"
#include "util/unit.h"
#include "util/name.h"
#include "kernel/environment.h"
#include "util/task.h"
#include "library/io_state.h"
#include "library/trace.h"
#include "frontends/lean/parser.h"
#include "util/lean_path.h"

namespace lean {

enum class module_src {
    OLEAN,
    LEAN,
};

struct module_info {
    bool m_out_of_date = false;

    module_id m_id;
    std::string m_contents;
    module_src m_source = module_src::LEAN;
    time_t m_mtime = -1, m_trans_mtime = -1;

    struct dependency {
        module_id m_id;
        module_name m_import_name;
        std::shared_ptr<module_info const> m_mod_info;
    };
    std::vector<dependency> m_deps;

    struct parse_result {
        options               m_opts;
        std::shared_ptr<loaded_module const> m_loaded_module;
    };
    task<parse_result> m_result;

    optional<module_parser_result> m_snapshots;

    gtask m_olean_task;

    cancellation_token m_cancel;
    log_tree::node m_lt;

    environment const & get_produced_env() const {
        return get(get(m_result).m_loaded_module->m_env);
    }

    environment get_latest_env() const;

    module_info() {}

    module_info(module_id const & id, std::string const & contents, module_src src, time_t mtime)
            : m_id(id), m_contents(contents), m_source(src), m_mtime(mtime) {}
};

class module_vfs {
public:
    virtual ~module_vfs() {}
    // need to support changed lean dependencies of olean files
    // need to support changed editor dependencies of olean files
    virtual std::shared_ptr<module_info> load_module(module_id const &, bool can_use_olean) = 0;
};

class fs_module_vfs : public module_vfs {
public:
    std::unordered_set<module_id> m_modules_to_load_from_source;
    std::shared_ptr<module_info> load_module(module_id const & id, bool can_use_olean) override;
};

class module_mgr {
    bool m_server_mode = false;
    bool m_save_olean = false;

    search_path m_path;
    environment m_initial_env;
    io_state m_ios;
    module_vfs * m_vfs;
    log_tree::node m_lt;

    mutex m_mutex;
    std::unordered_map<module_id, std::shared_ptr<module_info>> m_modules;

    void mark_out_of_date(module_id const & id);
    void build_module(module_id const & id, bool can_use_olean, name_set module_stack);

    std::vector<module_name> get_direct_imports(module_id const & id, std::string const & contents);
    void build_lean(std::shared_ptr<module_info> const & mod, name_set const & module_stack);
    std::pair<cancellation_token, module_parser_result>
    build_lean_snapshots(std::shared_ptr<module_parser> const & mod_parser,
                         std::shared_ptr<module_info> const & old_mod, std::vector<gtask> const & deps,
                         std::string const & contents);

public:
    module_mgr(module_vfs * vfs, log_tree::node const & lt,
               search_path const & path,
               environment const & initial_env, io_state const & ios) :
            m_path(path), m_initial_env(initial_env), m_ios(ios), m_vfs(vfs), m_lt(lt) {}

    void invalidate(module_id const & id);

    std::shared_ptr<module_info const> get_module(module_id const &);

    std::vector<std::shared_ptr<module_info const>> get_all_modules();

    void cancel_all();

    void set_server_mode(bool use_snapshots) { m_server_mode = use_snapshots; }
    bool get_server_mode() const { return m_server_mode; }

    void set_save_olean(bool save_olean) { m_save_olean = save_olean; }
    bool get_save_olean() const { return m_save_olean; }

    environment get_initial_env() const { return m_initial_env; }
    options get_options() const { return m_ios.get_options(); }
    io_state get_io_state() const { return m_ios; }
    void set_log_tree(log_tree::node const & lt) { m_lt = lt; }
};

environment get_combined_environment(environment const & env0,
                                     buffer<std::shared_ptr<module_info const>> const & mods);

}




// ========== module_mgr.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include <algorithm>
#include "util/utf8.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "library/module_mgr.h"
#include "library/module.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/parser.h"
#include "library/library_task_builder.h"

namespace lean {

environment module_info::get_latest_env() const {
    if (m_snapshots) {
        auto snap = *m_snapshots;
        while (snap.m_next) {
            if (auto next = peek(snap.m_next)) {
                snap = *next;
            } else {
                break;
            }
        }
        if (auto parser_snap = snap.m_snapshot_at_end) {
            return parser_snap->m_env;
        }
    }
    if (auto res = peek(m_result)) {
        if (auto env = peek(res->m_loaded_module->m_env)) {
            return *env;
        }
    }
    return environment();
}

void module_mgr::mark_out_of_date(module_id const & id) {
    for (auto & mod : m_modules) {
        if (!mod.second || mod.second->m_out_of_date) continue;
        for (auto & dep : mod.second->m_deps) {
            if (dep.m_id == id) {
                mod.second->m_out_of_date = true;
                mark_out_of_date(mod.first);
                break;
            }
        }
    }
}

static module_loader mk_loader(module_id const & cur_mod, std::vector<module_info::dependency> const & deps) {
    auto deps_per_mod_ptr = std::make_shared<std::unordered_map<module_id, std::vector<module_info::dependency>>>();
    auto & deps_per_mod = *deps_per_mod_ptr;

    buffer<module_info const *> to_process;
    for (auto & d : deps) {
        if (d.m_mod_info) {
            deps_per_mod[cur_mod].push_back(d);
            to_process.push_back(d.m_mod_info.get());
        }
    }
    while (!to_process.empty()) {
        module_info const & m = *to_process.back();
        to_process.pop_back();
        if (deps_per_mod.count(m.m_id)) continue;

        for (auto & d : m.m_deps) {
            if (d.m_mod_info) {
                deps_per_mod[m.m_id].push_back(d);
                if (!deps_per_mod.count(d.m_mod_info->m_id))
                    to_process.push_back(d.m_mod_info.get());
            }
        }
    }

    return[deps_per_mod_ptr] (std::string const & current_module, module_name const & import) -> std::shared_ptr<loaded_module const> {
        try {
            for (auto & d : deps_per_mod_ptr->at(current_module)) {
                if (d.m_import_name.m_name == import.m_name && d.m_import_name.m_relative == import.m_relative) {
                    return get(d.m_mod_info->m_result).m_loaded_module;
                }
            }
        } catch (std::out_of_range) {
            // In files with syntax errors, it can happen that the
            // initial dependency scan does not find all dependencies.
        }
        throw exception(sstream() << "could not resolve import: " << import.m_name);
    };
}

static gtask compile_olean(std::shared_ptr<module_info const> const & mod, log_tree::node const & parsing_lt) {
    auto errs = has_errors(parsing_lt);

    gtask mod_dep = mk_deep_dependency(mod->m_result, [] (buffer<gtask> & deps, module_info::parse_result const & res) {
        for (auto & mdf : res.m_loaded_module->m_modifications)
            mdf->get_task_dependencies(deps);
        deps.push_back(res.m_loaded_module->m_uses_sorry);
    });

    std::vector<gtask> olean_deps;
    for (auto & dep : mod->m_deps)
        if (dep.m_mod_info)
            olean_deps.push_back(dep.m_mod_info->m_olean_task);

    return add_library_task(task_builder<unit>([mod, errs] {
        if (mod->m_source != module_src::LEAN)
            throw exception("cannot build olean from olean");
        auto res = get(mod->m_result);

        if (get(errs)) throw exception("not creating olean file because of errors");

        auto olean_fn = olean_of_lean(mod->m_id);
        exclusive_file_lock output_lock(olean_fn);
        std::ofstream out(olean_fn, std::ios_base::binary);
        write_module(*res.m_loaded_module, out);
        out.close();
        if (!out) throw exception("failed to write olean file");
        return unit();
    }).depends_on(mod_dep).depends_on(olean_deps).depends_on(errs), std::string("saving olean"));
}

// TODO(gabriel): adapt to vfs
static module_id resolve(search_path const & path,
                         module_id const & module_file_name,
                         module_name const & ref) {
    auto base_dir = dirname(module_file_name);
    try {
        return find_file(path, base_dir, ref.m_relative, ref.m_name, ".lean");
    } catch (lean_file_not_found_exception) {
        return olean_file_to_lean_file(find_file(path, base_dir, ref.m_relative, ref.m_name, ".olean"));
    }
}

void module_mgr::build_module(module_id const & id, bool can_use_olean, name_set module_stack) {
    if (auto & existing_mod = m_modules[id])
        if (!existing_mod->m_out_of_date) return;

    auto orig_module_stack = module_stack;
    if (module_stack.contains(id)) {
        throw exception(sstream() << "cyclic import: " << id);
    }
    module_stack.insert(id);

    scope_global_ios scope_ios(m_ios);
    scope_log_tree lt(m_lt.mk_child(id, {}, { id, {{1, 0}, {static_cast<unsigned>(-1), 0}} }, log_tree::DefaultLevel, true));
    scope_traces_as_messages scope_trace_msgs(id, {1, 0});

    try {
        bool already_have_lean_version = m_modules[id] && m_modules[id]->m_source == module_src::LEAN;

        auto mod = m_vfs->load_module(id, !already_have_lean_version && can_use_olean);

        if (mod->m_source == module_src::OLEAN) {
            std::istringstream in2(mod->m_contents, std::ios_base::binary);
            auto olean_fn = olean_of_lean(id);
            bool check_hash = false;
            auto parsed_olean = parse_olean(in2, olean_fn, check_hash);
            // we never need to re-parse .olean files, so discard content
            mod->m_contents.clear();

            if (m_server_mode) {
                // In server mode, we keep the .lean contents instead of the .olean contents around. This can
                // reduce rebuilds in `module_mgr::invalidate`.
                try {
                    mod->m_contents = m_vfs->load_module(id, false)->m_contents;
                } catch (...) {}
            }

            mod->m_lt = lt.get();
            mod->m_trans_mtime = mod->m_mtime;

            for (auto & d : parsed_olean.m_imports) {
                auto d_id = resolve(m_path, id, d);
                build_module(d_id, true, module_stack);

                auto & d_mod = m_modules[d_id];
                mod->m_deps.push_back({ d_id, d, d_mod });
                mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
            }

            if (mod->m_trans_mtime > mod->m_mtime)
                return build_module(id, false, orig_module_stack);

            module_info::parse_result res;

            auto deps = mod->m_deps;
            res.m_loaded_module = cache_preimported_env(
                    { id, parsed_olean.m_imports,
                      parse_olean_modifications(parsed_olean.m_serialized_modifications, id),
                      mk_pure_task<bool>(parsed_olean.m_uses_sorry), {} },
                    m_initial_env, [=] { return mk_loader(id, deps); });

            mod->m_result = mk_pure_task<module_info::parse_result>(res);

            if (auto & old_mod = m_modules[id])
                cancel(old_mod->m_cancel);
            m_modules[id] = mod;
        } else if (mod->m_source == module_src::LEAN) {
            build_lean(mod, module_stack);
            m_modules[id] = mod;
        } else {
            throw exception("unknown module source");
        }
    } catch (throwable & ex) {
        message_builder msg(m_initial_env, m_ios, id, pos_info {1, 0}, ERROR);
        msg.set_exception(ex);
        msg.report();
        throw ex;
    }
}

void module_mgr::build_lean(std::shared_ptr<module_info> const & mod, name_set const & module_stack) {
    auto id = mod->m_id;
    auto & lt = logtree();
    auto end_pos = find_end_pos(mod->m_contents);
    scope_log_tree lt2(lt.mk_child({}, {}, { id, {{1, 0}, end_pos} }));

    auto imports = get_direct_imports(id, mod->m_contents);

    mod->m_lt = logtree();
    mod->m_trans_mtime = mod->m_mtime;
    for (auto & d : imports) {
        module_id d_id;
        std::shared_ptr<module_info const> d_mod;
        try {
            d_id = resolve(m_path, id, d);
            build_module(d_id, true, module_stack);
            d_mod = m_modules[d_id];
            mod->m_trans_mtime = std::max(mod->m_trans_mtime, d_mod->m_trans_mtime);
        } catch (throwable & ex) {
            message_builder(m_initial_env, m_ios, id, {1, 0}, ERROR).set_exception(ex).report();
        }
        mod->m_deps.push_back({ d_id, d, d_mod });
    }

    std::vector<gtask> deps;
    for (auto & d : mod->m_deps)
        if (d.m_mod_info)
            deps.push_back(d.m_mod_info->m_result);
    if (!mod->m_deps.empty()) {
        // also add the preimported environment of the first dependency
        if (auto & mod_info = mod->m_deps.front().m_mod_info) {
            deps.push_back(mk_deep_dependency(mod_info->m_result,
                                              [] (buffer<gtask> & ds, module_info::parse_result const & res) {
                                                  ds.push_back(res.m_loaded_module->m_env);
                                              }));
        }
    }

    auto ldr = mk_loader(id, mod->m_deps);
    auto mod_parser_fn = std::make_shared<module_parser>(id, mod->m_contents, m_initial_env, ldr);
    mod_parser_fn->save_info(m_server_mode);

    module_parser_result snapshots;
    std::tie(mod->m_cancel, snapshots) = build_lean_snapshots(
            mod_parser_fn, m_modules[id], deps, mod->m_contents);
    lean_assert(!mod->m_cancel->is_cancelled());
    scope_cancellation_token scope_cancel(mod->m_cancel);

    if (m_server_mode) {
        // Even just keeping a reference to the final environment costs us
        // a few hundred megabytes (when compiling the standard library).
        mod->m_snapshots = snapshots;
    }

    auto initial_env = m_initial_env;
    mod->m_result = map<module_info::parse_result>(
        get_end(snapshots),
        [id, initial_env, ldr](module_parser_result const & res) {
            module_info::parse_result parse_res;

            lean_always_assert(res.m_snapshot_at_end);
            parse_res.m_loaded_module = cache_preimported_env(
                    export_module(res.m_snapshot_at_end->m_env, id),
                    initial_env, [=] { return ldr; });

            parse_res.m_opts = res.m_snapshot_at_end->m_options;

            return parse_res;
        }).build();

    if (m_save_olean) {
        scope_log_tree_core lt3(&lt);
        mod->m_olean_task = compile_olean(mod, lt2.get());
    }
}

static optional<pos_info> get_first_diff_pos(std::string const & as, std::string const & bs) {
    if (as == bs) return optional<pos_info>();
    char const * a = as.c_str(), * b = bs.c_str();
    int line = 1;
    while (true) {
        char const * ai = strchr(a, '\n');
        char const * bi = strchr(b, '\n');
        if (ai && bi) {
            if (ai - a == bi - b &&
                    ai[1] && bi[1] && // ignore final newlines, the scanner does not see them
                    strncmp(a, b, ai - a) == 0) {
                a = ai + 1;
                b = bi + 1;
                line++;
            } else {
                break;
            }
        } else if (strcmp(a, b) == 0) {
            return optional<pos_info>();
        } else {
            break;
        }
    }
    return optional<pos_info>(line, 0);
}

std::pair<cancellation_token, module_parser_result>
module_mgr::build_lean_snapshots(std::shared_ptr<module_parser> const & mod_parser,
                                 std::shared_ptr<module_info> const & old_mod,
                                 std::vector<gtask> const & deps, std::string const & contents) {
    auto rebuild = [&] {
        if (old_mod) cancel(old_mod->m_cancel);
        auto cancel_tok = mk_cancellation_token();
        return std::make_pair(cancel_tok, mod_parser->parse(optional<std::vector<gtask>>(deps)));
    };

    if (!m_server_mode) return rebuild();
    if (!old_mod) return rebuild();
    if (old_mod->m_source != module_src::LEAN)
        return rebuild();

    for (auto d : old_mod->m_deps) {
        if (!d.m_mod_info && !m_modules[d.m_id]) continue;
        if (d.m_mod_info && m_modules[d.m_id] && m_modules[d.m_id] == d.m_mod_info) continue;

        return rebuild();
    }

    if (!old_mod->m_snapshots) return rebuild();

    auto snap = *old_mod->m_snapshots;
    logtree().reuse("_next"); // TODO(gabriel): this needs to be the same name as in module_parser...
    if (auto diff_pos = get_first_diff_pos(contents, old_mod->m_contents)) {
        return std::make_pair(old_mod->m_cancel,
                              mod_parser->resume_from_start(snap, old_mod->m_cancel,
                                                            *diff_pos, optional<std::vector<gtask>>(deps)));
    } else {
        // no diff
        return std::make_pair(old_mod->m_cancel, snap);
    }
}

static void remove_cr(std::string & str) {
    str.erase(std::remove(str.begin(), str.end(), '\r'), str.end());
}

static bool equal_upto_cr(std::string a, std::string b) {
    remove_cr(a);
    remove_cr(b);
    return a == b;
}

std::shared_ptr<module_info const> module_mgr::get_module(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);
    name_set module_stack;
    build_module(id, true, module_stack);
    return m_modules.at(id);
}

void module_mgr::invalidate(module_id const & id) {
    unique_lock<mutex> lock(m_mutex);

    bool rebuild_rdeps = true;
    if (auto & mod = m_modules[id]) {
        try {
            // HACK(gabriel): On windows vscode sends different line endings than the on-disk version.
            // This causes the server to recompile all files even when just hovering.
            if (equal_upto_cr(m_vfs->load_module(id, false)->m_contents, mod->m_contents)) {
                // content unchanged
                rebuild_rdeps = false;
            }
        } catch (...) {}

        mod->m_out_of_date = true;
    }
    if (rebuild_rdeps) {
        mark_out_of_date(id);
    }

    buffer<module_id> to_rebuild;
    to_rebuild.push_back(id);
    for (auto & mod : m_modules) {
        if (mod.second && mod.second->m_out_of_date)
            to_rebuild.push_back(mod.first);
    }
    for (auto & i : to_rebuild) {
        try {
            build_module(i, true, {});
        } catch (...) {}
    }
}

std::vector<module_name> module_mgr::get_direct_imports(module_id const & id, std::string const & contents) {
    std::vector<module_name> imports;
    try {
        scope_log_tree lt;
        std::istringstream in(contents);
        bool use_exceptions = true;
        parser p(get_initial_env(), m_ios, nullptr, in, id, use_exceptions);
        try {
            p.init_scanner();
        } catch (...) {}
        p.get_imports(imports);
    } catch (...) {}

    return imports;
}

std::vector<std::shared_ptr<module_info const>> module_mgr::get_all_modules() {
    unique_lock<mutex> lock(m_mutex);

    std::vector<std::shared_ptr<module_info const>> mods;
    for (auto & mod : m_modules) {
        if (mod.second) {
            mods.push_back(mod.second);
        }
    }

    return mods;
}

void module_mgr::cancel_all() {
    for (auto & m : m_modules) {
        if (auto mod = m.second) {
            cancel(mod->m_cancel);
        }
    }
}

std::shared_ptr<module_info> fs_module_vfs::load_module(module_id const & id, bool can_use_olean) {
    auto lean_fn = id;
    auto lean_mtime = get_mtime(lean_fn);

    try {
        auto olean_fn = olean_of_lean(lean_fn);
        shared_file_lock olean_lock(olean_fn);
        auto olean_mtime = get_mtime(olean_fn);
        if (olean_mtime != -1 && olean_mtime >= lean_mtime &&
            can_use_olean &&
            !m_modules_to_load_from_source.count(id) &&
            is_candidate_olean_file(olean_fn)) {
            return std::make_shared<module_info>(id, read_file(olean_fn, std::ios_base::binary), module_src::OLEAN, olean_mtime);
        }
    } catch (exception) {}

    return std::make_shared<module_info>(id, read_file(lean_fn), module_src::LEAN, lean_mtime);
}

environment get_combined_environment(environment const & env,
                                     buffer<std::shared_ptr<module_info const>> const & mods) {
    module_id combined_id = "<combined_environment.lean>";

    std::vector<module_info::dependency> deps;
    std::vector<module_name> refs;
    for (auto & mod : mods) {
        // TODO(gabriel): switch module_ids to names, then we don't need this hack
        module_name ref { name(mod->m_id), {} };
        deps.push_back({ mod->m_id, ref, mod });
        refs.push_back(ref);
    }

    return import_modules(env, combined_id, refs, mk_loader(combined_id, deps));
}

}




// ========== update_declaration.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/declaration.h"
namespace lean {
// Helper function for updating "declaration fields"
declaration update_declaration_univ_params(declaration const & d, level_param_names const & ps);
declaration update_declaration_type(declaration const & d, expr const & type);
declaration update_declaration_value(declaration const & d, expr const & value);
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type, expr const & value);
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type);
}




// ========== update_declaration.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/update_declaration.h"

namespace lean {
static declaration update_declaration(declaration d, optional<level_param_names> const & ps,
                                      optional<expr> const & type, optional<expr> const & value) {
    level_param_names _ps = ps ? *ps : d.get_univ_params();
    expr _type = type ? *type : d.get_type();
    expr _value;
    if (d.is_definition()) {
        _value = value ? *value : d.get_value();
    } else {
        lean_assert(!value);
    }
    if (d.is_constant_assumption()) {
        if (is_eqp(d.get_type(), _type) && is_eqp(d.get_univ_params(), _ps))
            return d;
        if (d.is_axiom())
            return mk_axiom(d.get_name(), _ps, _type);
        else
            return mk_constant_assumption(d.get_name(), _ps, _type);
    } else {
        if (is_eqp(d.get_type(), _type) && is_eqp(d.get_value(), _value) && is_eqp(d.get_univ_params(), _ps))
            return d;
        if (d.is_theorem())
            return mk_theorem(d.get_name(), _ps, _type, _value);
        else
            return mk_definition(d.get_name(), _ps, _type, _value, d.get_hints(), d.is_trusted());
    }
}

declaration update_declaration_univ_params(declaration const & d, level_param_names const & ps) {
    return update_declaration(d, optional<level_param_names>(ps), none_expr(), none_expr());
}

declaration update_declaration_type(declaration const & d, expr const & type) {
    return update_declaration(d, optional<level_param_names>(), some_expr(type), none_expr());
}

declaration update_declaration_value(declaration const & d, expr const & value) {
    return update_declaration(d, optional<level_param_names>(), none_expr(), some_expr(value));
}

declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type, expr const & value) {
    return update_declaration(d, optional<level_param_names>(ps), some_expr(type), some_expr(value));
}
declaration update_declaration(declaration const & d, level_param_names const & ps, expr const & type) {
    return update_declaration(d, optional<level_param_names>(ps), some_expr(type), none_expr());
}
}




// ========== abstract_context_cache.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lbool.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "library/congr_lemma.h"
#include "library/projection.h"
#include "library/fun_info.h"
#include "library/local_instances.h"
#include "library/unification_hint.h"

namespace lean {
#define LEAN_NUM_TRANSPARENCY_MODES 5
enum class transparency_mode { All = 0, Semireducible, Instances, Reducible, None };

class type_context_old;

/* Auxiliary information that is cached by the app_builder module in
   the context_cache. */
struct app_builder_info {
    unsigned             m_num_umeta;
    unsigned             m_num_emeta;
    expr                 m_app;
    list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
    list<expr>           m_expl_args; // metavars for explicit arguments
    /*
      IMPORTANT: for m_inst_args we store the arguments in reverse order.
      For example, the first element in the list indicates whether the last argument
      is an instance implicit argument or not. If it is not none, then the element
      is the associated metavariable

      m_expl_args are also stored in reverse order
    */
};

/*
   We have two main kinds of cache in Lean: environmental and contextual.
   The environmental caches only depend on the environment, and are easier to maintain.
   We usually store them in thread local storage, and before using them we compare
   if the current environment is a descendant of the one in the cache, and we
   check for attribute fingerprints.

   This class defines the interface for contextual caches.
   A contextual cache depends on the local_context object.
   Ideally, the cache should be stored in the local_context object,
   but this is not feasible due to performance issues. The local_context object
   should support a fast O(1) copy operation. Thus, we implement it using
   functional data-structures such as red-black trees. This kind of data-structure
   is too inefficient for a cache data structure, and we want to be able to
   use hashtables (at least 10x faster than red-black trees). Another
   issue is that we want to keep the `local_context` object simple and
   without the overhead of many caches.

   We use contextual caches for the operations performed in the following modules:
   type_context_old, app_builder, fun_info and congr_lemma.
   In the type_context_old, we cache inferred types, whnf, type class instances,
   to cite a few.

   This class has been added to address problems with the former `type_context_old_cache_manager`.
   The `type_context_old_cache_manager` objects were stored in thread local objects.
   The correctness of this cache relied on the fact we used to never reuse fresh names in the whole system.
   This is not true in the new name_generator refactoring (for addressing issue #1601).
   The caches for the modules app_builder, congr_lemma and fun_info have the same problem.

   We have implemented a thread local cache reset operation, but it is
   not sufficient for fixing this issue since we only reset the cache
   before each command and when start a task.

   Here is a scenario that demonstrates the problem.
   Suppose we are executing the tactic `t1 <|> t2`.
   First, we execute `t1`, and in the process, the type_context_old
   cache is populated with new local constants created by `t1`.
   Then `t1` fails and we execute `t2`. When, we execute `t2`
   on the initial `tactic_state` object. Thus,
   `t2` may potentially create new local constants using the names
   used by `t1`, but with different types. So, the content
   of the cache is invalid.

   Here are possible implementations of this API:

   - An "imperative" implementation using hashtables, and it is useful for modules
     that own a type_context_old object (e.g., elaborator).
     This implementation is also useful for the new type_context_old API we are going to expose in the `io` monad.

   - In principle, a "functional" implementation using rb_map and rb_tree is possible.
     Then, this version could be stored in the tactic_state or local_context objects.
     We decided to not use it for performe issues. See comment above.

   - For caching contextual information in the tactic framework, we use the following approach:
     * We implement a thread local unique token generator.
     * The token can be viewed as a reference to the cache.
     * tactic_state stores this token.
     * Thread local storage stores the "imperative" implementation and a token of its owner.
     * When we create a type_context_old for a tactic_state we check whether the thread local
       storage contains the cache for the given tactic_state. If yes, we use it, and obtain
       a new token for it since we will perform destructive updates.
       Otherwise, we create a new one.
     * When we finish using the type_context_old, we update the tactic_state with the new fresh token,
       and put the updated cache back into the thread local storage.

       Remark: the thread local storage may store more than one cache.

       Remark: this approach should work well for "sequential" tactic execution.
          For `t1 <|> t2`, if `t1` fails, `t2` will potentially start with the empty cache
          since the thread local storage contains the cache for `t1`.
          We should measure whether this approach is more efficient than the functional one.
          With the "abstract interface", we can even have both approaches.

       Remark: we have considered storing the token on the local context, but this is not ideal
       because there are many tactics that create more than on subgoal (e.g., `apply`),
       and we would have to use an empty cache for each subgoal but the first.
       The situation would be analogous to the `t1 <|> t2` scenario described in the previous
       remark. Moreover, the different subgoals usually have very similar local contexts
       and information cached in one can be reused in the others.

       Remark: recall that in a sequence of tactic_states [s_1, s_2, ...] obtained by executing tactics [t_1, t_2, ...]

            s_1 -t_1-> s_2 -t_2-> s_3 -> ...

       we never reuse names for labeling local declarations, and the cache is reused, since we will store the
       cache on the thread local storage after each step, and will retrieve it before the beginning of the following step.
       Most cached data (e.g., inferred types) is still valid because we never reuse names in the sequence.
       The only exception is cached data related to type class instances and subsigletons (which depends on type class instances).
       Here the result depends on the local instances available in the local context.
       Recall we have two modes for handling local instances:

       1) liberal: any local instance can be used. In this mode, the cache for type class instances and subsigletons has to be
          flushed in the beginning of each step if the local_context is different from the previous one. Actually,
          we do not track the local_context. So, the cache is always flushed in the beginning of each step in the liberal mode.
          This is fine because we only use the "liberal" mode when elaborating the header of a declaration.

       2) frozen: after elaborating the header of a declaration, we freeze the local instances that can be used to
          elaborate its body. The freeze step is also useful to speedup the type_context_old initialization
          (see comment in the type_context_old class). So, we just check if the frozen local instances are the same
          before starting each step. This check is performed in the method `init_local_instances`.

   Here are some benefits of the new approach:

   - The cache will be smaller in many cases. For example, after `t1` fails in `t1 <|> t2`, the cached information
     about its new fresh local constants is not useful anymore, but it stays in the current
     cache.

   - We don't need to check whether the cache is valid or not when we create a new
     type_context_old.

   - It is more efficient when creating temporary type_context_old objects for performing
     a single operation. In this kind of scenario, we can use the dummy cache implementation
     that doesn't cache anything.

   - It is easy to experiment with new cache data structures.

   - We can easily flush the cache if a primitive tactic performs an operation that invalidates it.
     Examples:
     * A tactic that allows user to use all local class instances available in the local context.
     * A tactic that reverses local instances
*/
class abstract_context_cache {
public:
    abstract_context_cache() {}
    abstract_context_cache(abstract_context_cache const &) = delete;
    abstract_context_cache(abstract_context_cache &&) = default;
    virtual ~abstract_context_cache() {}

    abstract_context_cache & operator=(abstract_context_cache const &) = delete;
    abstract_context_cache & operator=(abstract_context_cache &&) = default;

    /* Cached configuration options */
    virtual options const & get_options() const = 0;
    virtual bool get_unfold_lemmas() const = 0;
    virtual unsigned get_nat_offset_cnstr_threshold() const = 0;
    virtual unsigned get_smart_unfolding() const = 0;
    virtual unsigned get_class_instance_max_depth() const = 0;

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) = 0;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) = 0;
    virtual bool get_aux_recursor(type_context_old &, name const &) = 0;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) = 0;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) = 0;
    virtual void set_infer(expr const &, expr const &) = 0;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) = 0;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) = 0;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) = 0;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) = 0;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) = 0;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) = 0;

    virtual optional<optional<expr>> get_instance(expr const &) = 0;
    virtual void set_instance(expr const &, optional<expr> const &) = 0;

    virtual optional<optional<expr>> get_subsingleton(expr const &) = 0;
    virtual void set_subsingleton(expr const &, optional<expr> const &) = 0;

    /* this method should flush the instance and subsingleton cache */
    virtual void flush_instances() = 0;

    virtual void reset_frozen_local_instances() = 0;
    virtual void set_frozen_local_instances(local_instances const & lis) = 0;
    virtual optional<local_instances> get_frozen_local_instances() const = 0;

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) = 0;
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) = 0;

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) = 0;

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) = 0;

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) = 0;
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) = 0;

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) = 0;

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) = 0;
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) = 0;

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) = 0;
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) = 0;
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) = 0;

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) = 0;
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) = 0;

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) = 0;
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) = 0;
};

/* Dummy implementation of the abstract_context_cache interface that does not do cache anything but configuration options. */
class context_cacheless : public abstract_context_cache {
protected:
    bool is_transparent(type_context_old & ctx, transparency_mode m, declaration const & d);
private:
    options                   m_options;
    bool                      m_unfold_lemmas;
    unsigned                  m_nat_offset_cnstr_threshold;
    unsigned                  m_smart_unfolding;
    unsigned                  m_class_instance_max_depth;
    optional<local_instances> m_local_instances;
public:
    context_cacheless();
    context_cacheless(options const &);
    /* Faster version of `context_cacheless(c.get_options())`.
       The bool parameter is not used. It is here just to make sure we don't confuse
       this constructor with the copy constructor. */
    context_cacheless(abstract_context_cache const &, bool);
    context_cacheless(context_cacheless const &) = delete;
    context_cacheless(context_cacheless &&) = default;
    virtual ~context_cacheless() {}

    context_cacheless & operator=(context_cacheless const &) = delete;
    context_cacheless & operator=(context_cacheless &&) = default;

    virtual options const & get_options() const override { return m_options; }
    virtual bool get_unfold_lemmas() const override { return m_unfold_lemmas; }
    virtual unsigned get_nat_offset_cnstr_threshold() const override  { return m_nat_offset_cnstr_threshold; }
    virtual unsigned get_smart_unfolding() const override  { return m_smart_unfolding; }
    virtual unsigned get_class_instance_max_depth() const override  { return m_class_instance_max_depth; }

    virtual void reset_frozen_local_instances() override { m_local_instances = optional<local_instances>(); }
    virtual void set_frozen_local_instances(local_instances const & lis) override { m_local_instances = lis; }
    virtual optional<local_instances> get_frozen_local_instances() const override { return m_local_instances; }

    /* Operations for accessing environment data more efficiently.
       The default implementation provided by this class does not have any optimization. */

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override { return none_expr(); }
    virtual void set_infer(expr const &, expr const &) override {}

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override { return false; }
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override {}

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override { return false; }
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override {}

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override { return none_expr(); }
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override {}

    virtual optional<optional<expr>> get_instance(expr const &) override { return optional<optional<expr>>(); }
    virtual void set_instance(expr const &, optional<expr> const &) override {}

    virtual optional<optional<expr>> get_subsingleton(expr const &) override { return optional<optional<expr>>(); }
    virtual void set_subsingleton(expr const &, optional<expr> const &) override {}

    virtual void flush_instances() override {}

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) override { return optional<fun_info>(); }
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) override {}

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<fun_info>(); }
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) override {}

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) override { return optional<unsigned>(); }
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) override {}

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) override { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) override {}

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<ss_param_infos>(); }
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override {}

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override { return optional<ss_param_infos>(); }
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override {}

    /* Cache support for congr_lemma module */

    virtual optional<congr_lemma> get_simp_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_specialized_simp_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_specialized_simp_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_specialized_congr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_specialized_congr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    virtual optional<congr_lemma> get_hcongr_lemma(expr const &, unsigned) override { return optional<congr_lemma>(); }
    virtual void set_hcongr_lemma(expr const &, unsigned, congr_lemma const &) override {}

    /* Cache support for app_builder */

    virtual optional<app_builder_info> get_app_builder_info(expr const &, unsigned) override { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(expr const &, unsigned, app_builder_info const &) override {}

    virtual optional<app_builder_info> get_app_builder_info(expr const &, list<bool> const &) override { return optional<app_builder_info>(); }
    virtual void set_app_builder_info(expr const &, list<bool> const &, app_builder_info const &) override {}
};

void initialize_abstract_context_cache();
void finalize_abstract_context_cache();
}




// ========== abstract_context_cache.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "library/abstract_context_cache.h"
#include "library/type_context.h"
#include "library/class.h"
#include "library/reducible.h"
#include "library/aux_recursors.h"

#ifndef LEAN_DEFAULT_UNFOLD_LEMMAS
#define LEAN_DEFAULT_UNFOLD_LEMMAS false
#endif

#ifndef LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD
#define LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD 1024
#endif

#ifndef LEAN_DEFAULT_SMART_UNFOLDING
#define LEAN_DEFAULT_SMART_UNFOLDING true
#endif

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

namespace lean {
static name * g_class_instance_max_depth = nullptr;
static name * g_nat_offset_threshold     = nullptr;
static name * g_unfold_lemmas            = nullptr;
static name * g_smart_unfolding          = nullptr;

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

unsigned get_nat_offset_cnstr_threshold(options const & o) {
    return o.get_unsigned(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD);
}

bool get_unfold_lemmas(options const & o) {
    return o.get_bool(*g_unfold_lemmas, LEAN_DEFAULT_UNFOLD_LEMMAS);
}

bool get_smart_unfolding(options const & o) {
    return o.get_bool(*g_smart_unfolding, LEAN_DEFAULT_SMART_UNFOLDING);
}

context_cacheless::context_cacheless():
    m_unfold_lemmas(LEAN_DEFAULT_UNFOLD_LEMMAS),
    m_nat_offset_cnstr_threshold(LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD),
    m_smart_unfolding(LEAN_DEFAULT_SMART_UNFOLDING),
    m_class_instance_max_depth(LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH) {
}

context_cacheless::context_cacheless(options const & o):
    m_options(o),
    m_unfold_lemmas(::lean::get_unfold_lemmas(o)),
    m_nat_offset_cnstr_threshold(::lean::get_nat_offset_cnstr_threshold(o)),
    m_smart_unfolding(::lean::get_smart_unfolding(o)),
    m_class_instance_max_depth(::lean::get_class_instance_max_depth(o)) {
}

context_cacheless::context_cacheless(abstract_context_cache const & c, bool):
    m_options(c.get_options()),
    m_unfold_lemmas(c.get_unfold_lemmas()),
    m_nat_offset_cnstr_threshold(c.get_nat_offset_cnstr_threshold()),
    m_smart_unfolding(c.get_smart_unfolding()),
    m_class_instance_max_depth(c.get_class_instance_max_depth()) {
}

bool context_cacheless::is_transparent(type_context_old & ctx, transparency_mode m, declaration const & d) {
    if (m == transparency_mode::None)
        return false;
    name const & n = d.get_name();
    if (get_proj_info(ctx, n) != nullptr)
        return false;
    if (m == transparency_mode::All)
        return true;
    if (d.is_theorem() && !get_unfold_lemmas())
        return false;
    if (m == transparency_mode::Instances && is_instance(ctx.env(), d.get_name()))
        return true;
    auto s = get_reducible_status(ctx.env(), d.get_name());
    if (s == reducible_status::Reducible && (m == transparency_mode::Reducible || m == transparency_mode::Instances))
        return true;
    if (s != reducible_status::Irreducible && m == transparency_mode::Semireducible)
        return true;
    return false;
}

optional<declaration> context_cacheless::get_decl(type_context_old & ctx, transparency_mode m, name const & n) {
    if (auto d = ctx.env().find(n)) {
        if (d->is_definition() && is_transparent(ctx, m, *d)) {
            return d;
        }
    }
    return optional<declaration>();
}

projection_info const * context_cacheless::get_proj_info(type_context_old & ctx, name const & n) {
    return get_projection_info(ctx.env(), n);
}

bool context_cacheless::get_aux_recursor(type_context_old & ctx, name const & n) {
    return ::lean::is_aux_recursor(ctx.env(), n);
}

void context_cacheless::get_unification_hints(type_context_old & ctx, name const & f1, name const & f2, buffer<unification_hint> & hints) {
    return ::lean::get_unification_hints(ctx.env(), f1, f2, hints);
}

void initialize_abstract_context_cache() {
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");
    g_nat_offset_threshold         = new name{"unifier", "nat_offset_cnstr_threshold"};
    register_unsigned_option(*g_nat_offset_threshold, LEAN_DEFAULT_NAT_OFFSET_CNSTR_THRESHOLD,
                             "(unifier) the unifier has special support for offset nat constraints of the form: "
                             "(t + k_1 =?= s + k_2), (t + k_1 =?= k_2) and (k_1 =?= k_2), "
                             "where k_1 and k_2 are numerals, t and s are arbitrary terms, and they all have type nat, "
                             "the offset constraint solver is used if k_1 and k_2 are smaller than the given threshold");
    g_unfold_lemmas = new name{"type_context", "unfold_lemmas"};
    register_bool_option(*g_unfold_lemmas, LEAN_DEFAULT_UNFOLD_LEMMAS,
                         "(type-context) whether to unfold lemmas (e.g., during elaboration)");
    g_smart_unfolding = new name{"type_context", "smart_unfolding"};
    register_bool_option(*g_smart_unfolding, LEAN_DEFAULT_SMART_UNFOLDING,
                         "(type-context) enable/disable smart unfolding (e.g., during elaboration)");
}

void finalize_abstract_context_cache() {
    delete g_class_instance_max_depth;
    delete g_nat_offset_threshold;
    delete g_smart_unfolding;
    delete g_unfold_lemmas;
}
}




// ========== unfold_macros.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Unfold any macro occurring in \c e that has trust level higher than the one
    allowed in \c env.

    \remark We use this function before sending declarations to the kernel.
    The kernel refuses any expression containing "untrusted" macros, i.e.,
    macros with trust level higher than the one allowed.
*/
expr unfold_untrusted_macros(environment const & env, expr const & e);

declaration unfold_untrusted_macros(environment const & env, declaration const & d);

expr unfold_all_macros(environment const & env, expr const & e);

declaration unfold_all_macros(environment const & env, declaration const & d);
}




// ========== unfold_macros.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/find_fn.h"
#include "kernel/expr_maps.h"
#include "library/type_context.h"
#include "library/unfold_macros.h"
#include "library/replace_visitor_with_tc.h"
#include "library/exception.h"

/* If the trust level of all macros is < LEAN_BELIEVER_TRUST_LEVEL,
   then we skip the unfold_untrusted_macros potentially expensive step.
   The following definition is commented because we are currently testing the AC macros. */
// #define LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL

namespace lean {
class unfold_untrusted_macros_fn : public replace_visitor_with_tc {
    optional<unsigned> m_trust_lvl;

    virtual expr visit_macro(expr const & e) override {
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        auto def = macro_def(e);
        expr r = update_macro(e, new_args.size(), new_args.data());
        if (!m_trust_lvl || def.trust_level() >= *m_trust_lvl) {
            if (optional<expr> new_r = m_ctx.expand_macro(r)) {
                return visit(*new_r);
            } else {
                throw generic_exception(e, "failed to expand macro");
            }
        } else {
            return r;
        }
    }

public:
    unfold_untrusted_macros_fn(type_context_old & ctx, optional<unsigned> const & lvl):
        replace_visitor_with_tc(ctx), m_trust_lvl(lvl) {}
};

static bool contains_untrusted_macro(unsigned trust_lvl, expr const & e) {
#if defined(LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL)
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL) return false;
#endif
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) {
                return is_macro(e) && macro_def(e).trust_level() >= trust_lvl;
            }));
}

expr unfold_untrusted_macros(environment const & env, expr const & e, optional<unsigned> const & trust_lvl) {
    if (!trust_lvl || contains_untrusted_macro(*trust_lvl, e)) {
        type_context_old ctx(env, transparency_mode::All);
        return unfold_untrusted_macros_fn(ctx, trust_lvl)(e);
    } else {
        return e;
    }
}

expr unfold_untrusted_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, optional<unsigned>(env.trust_lvl()));
}

expr unfold_all_macros(environment const & env, expr const & e) {
    return unfold_untrusted_macros(env, e, {});
}

static bool contains_untrusted_macro(unsigned trust_lvl, declaration const & d) {
#if defined(LEAN_ALL_MACROS_HAVE_SMALL_TRUST_LVL)
    if (trust_lvl > LEAN_BELIEVER_TRUST_LEVEL) return false;
#endif
    if (!d.is_trusted())
        return false;
    if (contains_untrusted_macro(trust_lvl, d.get_type()))
        return true;
    return (d.is_definition() || d.is_theorem()) && contains_untrusted_macro(trust_lvl, d.get_value());
}

declaration unfold_untrusted_macros(environment const & env, declaration const & d, optional<unsigned> const & trust_lvl) {
    if (!trust_lvl || contains_untrusted_macro(*trust_lvl, d)) {
        expr new_t = unfold_untrusted_macros(env, d.get_type(), trust_lvl);
        if (d.is_theorem()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_theorem(d.get_name(), d.get_univ_params(), new_t, new_v);
        } else if (d.is_definition()) {
            expr new_v = unfold_untrusted_macros(env, d.get_value(), trust_lvl);
            return mk_definition(d.get_name(), d.get_univ_params(), new_t, new_v,
                                 d.get_hints(), d.is_trusted());
        } else if (d.is_axiom()) {
            return mk_axiom(d.get_name(), d.get_univ_params(), new_t);
        } else if (d.is_constant_assumption()) {
            return mk_constant_assumption(d.get_name(), d.get_univ_params(), new_t);
        } else {
            lean_unreachable();
        }
    } else {
        return d;
    }
}

declaration unfold_untrusted_macros(environment const & env, declaration const & d) {
    return unfold_untrusted_macros(env, d, optional<unsigned>(env.trust_lvl()));
}

declaration unfold_all_macros(environment const & env, declaration const & d) {
    return unfold_untrusted_macros(env, d, {});
}
}




// ========== max_sharing.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/expr.h"

namespace lean {
/**
   \brief Functional object for creating expressions with maximally
   shared sub-expressions.
*/
class max_sharing_fn {
    struct imp;
    friend expr max_sharing(expr const & a);
    std::unique_ptr<imp> m_ptr;
public:
    max_sharing_fn();
    ~max_sharing_fn();

    expr operator()(expr const & a);

    /** \brief Return true iff \c a was already processed by this object. */
    bool already_processed(expr const & a) const;

    /** \brief Clear the cache. */
    void clear();
};

/**
   \brief The resultant expression is structurally identical to the input one, but
   it uses maximally shared sub-expressions.
*/
expr max_sharing(expr const & a);
}




// ========== max_sharing.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include <unordered_set>
#include <functional>
#include "util/buffer.h"
#include "util/interrupt.h"
#include "library/max_sharing.h"

namespace lean {
/**
   \brief Implementation of the functional object for creating expressions with maximally
   shared sub-expressions.
*/
struct max_sharing_fn::imp {
    typedef typename std::unordered_set<expr, expr_hash, is_bi_equal_proc> expr_cache;
    typedef typename std::unordered_set<level, level_hash>                 level_cache;
    expr_cache  m_expr_cache;
    level_cache m_lvl_cache;

    level apply(level const & l) {
        auto r = m_lvl_cache.find(l);
        if (r != m_lvl_cache.end())
            return *r;
        level res;
        switch (l.kind()) {
        case level_kind::Zero:   case level_kind::Param:
        case level_kind::Meta:
            res = l;
            break;
        case level_kind::Succ:
            res = update_succ(l, apply(succ_of(l)));
            break;
        case level_kind::Max:
            res = update_max(l, apply(max_lhs(l)), apply(max_rhs(l)));
            break;
        case level_kind::IMax:
            res = update_max(l, apply(imax_lhs(l)), apply(imax_rhs(l)));
            break;
        }
        m_lvl_cache.insert(res);
        return res;
    }

    expr apply(expr const & a) {
        check_system("max_sharing");
        auto r = m_expr_cache.find(a);
        if (r != m_expr_cache.end())
            return *r;
        expr res;
        switch (a.kind()) {
        case expr_kind::Var:
            res = a;
            break;
        case expr_kind::Constant:
            res = update_constant(a, map(const_levels(a), [&](level const & l) { return apply(l); }));
            break;
        case expr_kind::Sort:
            res = update_sort(a, apply(sort_level(a)));
            break;
        case expr_kind::App: {
            expr new_f = apply(app_fn(a));
            expr new_a = apply(app_arg(a));
                res = update_app(a, new_f, new_a);
            break;
        }
        case expr_kind::Lambda: case expr_kind::Pi: {
            expr new_d = apply(binding_domain(a));
            expr new_b = apply(binding_body(a));
            res = update_binding(a, new_d, new_b);
            break;
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(a));
            expr new_v = apply(let_value(a));
            expr new_b = apply(let_body(a));
            res = update_let(a, new_t, new_v, new_b);
            break;
        }
        case expr_kind::Meta:  case expr_kind::Local:
            res = update_mlocal(a, apply(mlocal_type(a)));
            break;
        case expr_kind::Macro: {
            buffer<expr> new_args;
            for (unsigned i = 0; i < macro_num_args(a); i++)
                new_args.push_back(macro_arg(a, i));
            res = update_macro(a, new_args.size(), new_args.data());
            break;
        }}
        m_expr_cache.insert(res);
        return res;
    }

    expr operator()(expr const & a) {
        // we must disable approximate/opportunistic hash-consing used in the kernel
        scoped_expr_caching disable(false);
        return apply(a);
    }

    bool already_processed(expr const & a) const {
        auto r = m_expr_cache.find(a);
        return r != m_expr_cache.end() && is_eqp(*r, a);
    }
};

max_sharing_fn::max_sharing_fn():m_ptr(new imp) {}
max_sharing_fn::~max_sharing_fn() {}
expr max_sharing_fn::operator()(expr const & a) { return (*m_ptr)(a); }
void max_sharing_fn::clear() { m_ptr->m_expr_cache.clear(); }
bool max_sharing_fn::already_processed(expr const & a) const { return m_ptr->already_processed(a); }

expr max_sharing(expr const & a) {
    return max_sharing_fn::imp()(a);
}
}




// ========== quote.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
bool is_expr_quote(expr const &e);
bool is_pexpr_quote(expr const &e);
expr const & get_expr_quote_value(expr const & e);
expr const & get_pexpr_quote_value(expr const & e);
expr mk_unelaborated_expr_quote(expr const & e);
expr mk_elaborated_expr_quote(expr const & e);
expr mk_pexpr_quote(expr const & e);

expr mk_antiquote(expr const & e);
bool is_antiquote(expr const & e);
expr const & get_antiquote_expr(expr const & e);

expr mk_pexpr_quote_and_substs(expr const & e, bool is_strict);

void initialize_quote();
void finalize_quote();
}




// ========== quote.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "library/placeholder.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/kernel_serializer.h"
#include "library/exception.h"
#include "library/util.h"
#include "library/quote.h"
#include "library/type_context.h"

namespace lean {
static std::string * g_expr_quote_opcode  = nullptr;
static expr * g_expr                = nullptr;
static expr * g_pexpr               = nullptr;
static name * g_expr_quote_pre      = nullptr;
static name * g_expr_quote_macro    = nullptr;

/** \brief A compact way of encoding quoted expressions inside Lean expressions. Used for values of type
    `reflected e` and `pexpr`. */
class expr_quote_macro : public macro_definition_cell {
    expr m_value;
    bool m_reflected;
public:
    expr_quote_macro(expr const & v, bool reflected):m_value(v), m_reflected(reflected) {}
    virtual bool lt(macro_definition_cell const & d) const override {
        return m_value < static_cast<expr_quote_macro const &>(d).m_value;
    }
    virtual name get_name() const override { return *g_expr_quote_macro; }
    virtual expr check_type(expr const &, abstract_type_context & ctx, bool infer_only) const override {
        if (m_reflected) {
            expr ty = ctx.check(m_value, infer_only);
            return mk_app(mk_constant(get_reflected_name(), {get_level(ctx, ty)}), ty, m_value);
        } else {
            return *g_pexpr;
        }
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return optional<expr>();
    }
    virtual unsigned trust_level() const override { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        /* Hack: we do *not* compare m_value's because quoted expressions may contain
           relevant position information that is ignored by the equality predicate for expressions.
        */
        return this == &other;
    }
    char const * prefix() const {
        return m_reflected ? "`(" : "``(";
    }
    virtual void display(std::ostream & out) const override {
        out << prefix() << m_value << ")";
    }
    virtual unsigned hash() const override { return m_value.hash(); }
    virtual void write(serializer & s) const override { s << *g_expr_quote_opcode << m_value << m_reflected; }
    expr const & get_value() const { return m_value; }
    bool const & is_reflected() const { return m_reflected; }
};

expr mk_elaborated_expr_quote(expr const & e) {
    return mk_macro(macro_definition(new expr_quote_macro(e, /* reflected */ true)));
}
expr mk_unelaborated_expr_quote(expr const & e) {
    // We use a transparent annotation instead of the opaque macro above so that the quoted term is accessible to
    // collect_locals etc.
    return mk_annotation(*g_expr_quote_pre, e);
}
expr mk_pexpr_quote(expr const & e) {
    return mk_macro(macro_definition(new expr_quote_macro(e, /* reflected */ false)));
}

bool is_expr_quote(expr const & e) {
    if (is_annotation(e, *g_expr_quote_pre)) {
        return true;
    }
    if (is_macro(e)) {
        if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
            return m->is_reflected();
        }
    }
    return false;
}
bool is_pexpr_quote(expr const & e) {
    if (is_macro(e)) {
        if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
            return !m->is_reflected();
        }
    }
    return false;
}

expr const & get_expr_quote_value(expr const & e) {
    lean_assert(is_expr_quote(e));
    if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
        return m->get_value();
    } else {
        return get_annotation_arg(e);
    }
}

expr const & get_pexpr_quote_value(expr const & e) {
    lean_assert(is_pexpr_quote(e));
    return static_cast<expr_quote_macro const *>(macro_def(e).raw())->get_value();
}

static name * g_antiquote = nullptr;

expr mk_antiquote(expr const & e) { return mk_annotation(*g_antiquote, e); }
bool is_antiquote(expr const & e) { return is_annotation(e, *g_antiquote); }
expr const & get_antiquote_expr(expr const & e) {
    lean_assert(is_antiquote(e));
    return get_annotation_arg(e);
}

static name * g_quote_fresh = nullptr;

expr mk_pexpr_quote_and_substs(expr const & e, bool is_strict) {
    name x("_x");
    name_generator ngen(*g_quote_fresh);
    buffer<expr> locals;
    buffer<expr> aqs;
    expr s = replace(e, [&](expr const & t, unsigned) {
            if (is_antiquote(t)) {
                expr local = mk_local(ngen.next(), x.append_after(locals.size() + 1),
                                      mk_expr_placeholder(), binder_info());
                locals.push_back(local);
                aqs.push_back(get_antiquote_expr(t));
                return some_expr(local);
            }
            if (is_local(t) && is_strict) {
                throw generic_exception(t, "unexpected local in quotation expression");
            }
            return none_expr();
        });
    expr r        = mk_pexpr_quote(Fun(locals, s));
    expr subst    = mk_constant(get_expr_subst_name());
    expr to_pexpr = mk_constant(get_to_pexpr_name());
    for (expr const & aq : aqs) {
        r = mk_app(subst, r, mk_app(to_pexpr, aq));
    }
    return r;
}

void initialize_quote() {
    g_quote_fresh         = new name("_quote_fresh");
    register_name_generator_prefix(*g_quote_fresh);
    g_expr_quote_macro    = new name("expr_quote_macro");
    g_expr_quote_opcode   = new std::string("Quote");
    g_expr           = new expr(mk_app(Const(get_expr_name()), mk_bool_tt()));
    g_pexpr          = new expr(mk_app(Const(get_expr_name()), mk_bool_ff()));

    g_antiquote      = new name("antiquote");
    g_expr_quote_pre = new name("expr_quote_pre");
    register_annotation(*g_antiquote);
    register_annotation(*g_expr_quote_pre);

    register_macro_deserializer(*g_expr_quote_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    expr e; bool reflected;
                                    d >> e >> reflected;
                                    return mk_macro(macro_definition(new expr_quote_macro(e, reflected)));
                                });
}

void finalize_quote() {
    delete g_quote_fresh;
    delete g_expr_quote_pre;
    delete g_expr_quote_macro;
    delete g_expr_quote_opcode;
    delete g_expr;
    delete g_pexpr;
    delete g_antiquote;
}
}




// ========== elab_context.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "library/abstract_context_cache.h"
#include "library/metavar_context.h"

namespace lean {
/*
  The elaboration context contains the main data used to elaborate a Lean expression.
  This context is shared between different \c type_context objects.
  A \c type_context object is used to infer types; solve unification/matching constraints;
  perform type class resolution; and reduce terms. Each \c type_context object may
  use a different \c local_context (i.e., hypotheses).

  When we create a \c type_context object we just need to provide this \c elab_context
  object and a \c local_context.

  In the tactic framework, we define a subclass called \c tactic_context.
  It contains additional information such as the set of goals. The \c tactic_context
  is the preferred way to write tactics in C++.

  In the past, the \c type_context object would contain the information stored here.
  This decision created several problems when we needed to create multiple \c type_context
  objects with different local contexts and/or for solving different unification/matching
  constraints. The main benefits of the new design are:
  - Multiple \c type_context objects may share the same \c elab_context.
  - Faster \c type_context creation.
  - It allows us to provide a clean Lean API for using type_context objects directly.
*/
class elab_context {
protected:
    environment              m_env;
    metavar_context          m_mctx;
    name_generator           m_ngen;
    context_cacheless        m_dummy_cache;
    abstract_context_cache * m_cache;

    friend class type_context;     // TODO(Leo): delete after we have a cleaner API here
    friend class type_context_old; // TODO(Leo): delete after refactoring
public:
    elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, abstract_context_cache * cache);
    elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, options const & opts);
    elab_context(elab_context const &) = delete;
    elab_context(elab_context &&) = delete;
    ~elab_context() {}

    elab_context const & operator=(elab_context const &) = delete;
    elab_context const & operator=(elab_context &&) = delete;

    environment const & env() const { return m_env; }
    metavar_context & mctx() { return m_mctx; }
    abstract_context_cache & cache() { return *m_cache; }
    name next_name() { return m_ngen.next(); }
};
}




// ========== elab_context.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/elab_context.h"

namespace lean {
elab_context::elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, abstract_context_cache * cache):
    m_env(env),
    m_mctx(mctx),
    m_ngen(ngen),
    m_cache(cache) {
}

elab_context::elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, options const & opts):
    m_env(env),
    m_mctx(mctx),
    m_ngen(ngen),
    m_dummy_cache(opts),
    m_cache(&m_dummy_cache) {
}
}




// ========== library_task_builder.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task_builder.h"
#include "util/log_tree.h"
#include "util/cancellable.h"
#include "library/io_state.h"
#include <string>

namespace lean {

struct library_scopes {
    log_tree::node m_lt;

    library_scopes(log_tree::node const & n) : m_lt(n) {}

    std::unique_ptr<gtask_imp> operator()(std::unique_ptr<gtask_imp> &&);
};

struct exception_reporter {
    std::unique_ptr<gtask_imp> operator()(std::unique_ptr<gtask_imp> &&);
};

template <class Res>
task<Res> add_library_task(task_builder<Res> && builder, std::string const & description,
                           bool add_producer = true, log_tree::detail_level lvl = log_tree::DefaultLevel) {
    auto lt = logtree().mk_child({}, description, logtree().get_location(), lvl);
    auto task = builder.wrap(library_scopes(lt)).build();
    if (add_producer) lt.set_producer(task);
    return task;
}

template <class Res>
task<Res> mk_library_task(task_builder<Res> && builder, std::string const & description) {
    return add_library_task(std::forward<task_builder<Res>>(builder), description, false);
}

template <class Res>
task<Res> add_library_task(task_builder<Res> && builder,
                           log_tree::detail_level lvl = log_tree::DefaultLevel,
                           bool add_producer = true) {
    return add_library_task(std::forward<task_builder<Res>>(builder), {}, add_producer, lvl);
}

}




// ========== library_task_builder.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/library_task_builder.h"
#include "library/message_builder.h"

namespace lean {

struct library_scopes_imp : public delegating_task_imp {
    io_state m_ios;
    log_tree::node m_lt;

    library_scopes_imp(std::unique_ptr<gtask_imp> && base, log_tree::node const & lt) :
        delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)),
        m_ios(get_global_ios()), m_lt(lt) {}

    // TODO(gabriel): set logtree status to cancelled?

    void execute(void * result) override {
        scope_global_ios scope1(m_ios);
        scope_log_tree scope2(m_lt);
        if (m_lt) m_lt.set_state(log_tree::state::Running);
        try {
            delegating_task_imp::execute(result);
        } catch (interrupted) {
            if (m_lt) m_lt.set_state(log_tree::state::Cancelled);
            throw;
        }
    }
};

std::unique_ptr<gtask_imp> library_scopes::operator()(std::unique_ptr<gtask_imp> && base) {
    return std::unique_ptr<gtask_imp>(new library_scopes_imp(
            std::forward<std::unique_ptr<gtask_imp>>(base), m_lt));
}

struct exception_reporter_imp : public delegating_task_imp {
    exception_reporter_imp(std::unique_ptr<gtask_imp> && base) :
        delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)) {}

    void execute(void * result) override {
        try {
            delegating_task_imp::execute(result);
        } catch (std::exception & ex) {
            message_builder(environment(), get_global_ios(),
                            logtree().get_location().m_file_name,
                            logtree().get_location().m_range.m_begin,
                            ERROR)
                    .set_exception(ex)
                    .report();
            throw;
        }
    }
};

std::unique_ptr<gtask_imp> exception_reporter::operator()(std::unique_ptr<gtask_imp> && base) {
    return std::unique_ptr<gtask_imp>(new exception_reporter_imp(
            std::forward<std::unique_ptr<gtask_imp>>(base)));
}

}




// ========== pipe.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
typedef void* HANDLE;
#else
#endif

namespace lean  {

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

struct pipe {
    HANDLE m_read_fd;
    HANDLE m_write_fd;
    pipe();
    pipe(HANDLE read_fd, HANDLE write_fd) :
        m_read_fd(read_fd), m_write_fd(write_fd) {}
    pipe(pipe const & p) :
        m_read_fd(p.m_read_fd), m_write_fd(p.m_write_fd) {}
};
#else
struct pipe {
    int m_read_fd;
    int m_write_fd;
    pipe();
    pipe(int read_fd, int write_fd) :
        m_read_fd(read_fd), m_write_fd(write_fd) {}
    pipe(pipe const & p) :
        m_read_fd(p.m_read_fd), m_write_fd(p.m_write_fd) {}
};

#endif

}




// ========== pipe.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include "library/pipe.h"
#include "util/exception.h"


#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#else
#include <unistd.h>
#endif

namespace lean {

pipe::pipe() {
    #if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
    #else
    int fds[2];
    if (::pipe(fds) == -1) {
        throw exception("unable to create pipe");
    } else {
        m_read_fd = fds[0];
        m_write_fd = fds[1];
    }
    #endif
}

}




// ========== bin_app.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Return true iff \c t is of the form <tt>((f s1) s2)</tt> */
bool is_bin_app(expr const & t, expr const & f);
/** \brief Return true iff \c t is of the form <tt>((f s1) s2)</tt>, if the result is true, then store a1 -> lhs, a2 -> rhs */
bool is_bin_app(expr const & t, expr const & f, expr & lhs, expr & rhs);

/** \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
    <tt>(op args[0] (op args[1] (op ... )))</tt> */
expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args);
expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l);

/** \brief Version of foldr that only uses unit when num_args == 0 */
template<typename MkBin, typename MkUnit>
expr foldr_compact(MkBin && mkb, MkUnit && mku, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return mku();
    } else {
        expr r = args[num_args - 1];
        unsigned i = num_args - 1;
        while (i > 0) {
            --i;
            r = mkb(args[i], r);
        }
        return r;
    }
}

/** \brief Version of foldr that only uses unit when num_args == 0 */
template<typename MkBin, typename MkUnit>
expr foldr(MkBin && mkb, MkUnit && mku, unsigned num_args, expr const * args) {
    expr r = mku();
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mkb(args[i], r);
    }
    return r;
}

/** \brief Return unit if <tt>num_args == 0</tt>, args[0] if <tt>num_args == 1</tt>, and
    <tt>(op ... (op (op args[0] args[1]) args[2]) ...)</tt> */
expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args);
expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l);
}




// ========== bin_app.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/bin_app.h"

namespace lean {
bool is_bin_app(expr const & t, expr const & f) {
    return is_app(t) && is_app(app_fn(t)) && app_fn(app_fn(t)) == f;
}

bool is_bin_app(expr const & t, expr const & f, expr & lhs, expr & rhs) {
    if (is_bin_app(t, f)) {
        lhs = app_arg(app_fn(t));
        rhs = app_arg(t);
        return true;
    } else {
        return false;
    }
}

expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[num_args - 1];
        unsigned i = num_args - 1;
        while (i > 0) {
            --i;
            r = mk_app(op, args[i], r);
        }
        return r;
    }
}
expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_rop(op, unit, l.size(), l.begin());
}

expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[0];
        for (unsigned i = 1; i < num_args; i++) {
            r = mk_app(op, r, args[i]);
        }
        return r;
    }
}
expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_lop(op, unit, l.size(), l.begin());
}
}




// ========== pattern_attribute.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
bool has_pattern_attribute(environment const & env, name const & d);
environment set_pattern_attribute(environment const & env, name const & d);
void initialize_pattern_attribute();
void finalize_pattern_attribute();
}




// ========== pattern_attribute.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/attribute_manager.h"

namespace lean {
static name * g_pattern_attr = nullptr;

static basic_attribute const & get_pattern_attribute() {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_pattern_attr));
}

bool has_pattern_attribute(environment const & env, name const & d) {
    return has_attribute(env, *g_pattern_attr, d);
}

environment set_pattern_attribute(environment const & env, name const & n) {
    return get_pattern_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, true);
}

void initialize_pattern_attribute() {
    g_pattern_attr = new name({"pattern"});
    register_system_attribute(basic_attribute(*g_pattern_attr, "mark that a definition can be used in a pattern"
                                              "(remark: the dependent pattern matching compiler will unfold the definition)"));
}

void finalize_pattern_attribute() {
    delete g_pattern_attr;
}
}




// ========== cache_helper.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/type_context.h"

namespace lean {
/** \brief Helper class for making sure we have a cache that is compatible
    with a given environment and transparency mode. */
template<typename Cache>
class cache_compatibility_helper {
    std::unique_ptr<Cache> m_cache_ptr[LEAN_NUM_TRANSPARENCY_MODES];
public:
    Cache & get_cache_for(environment const & env, transparency_mode m) {
        unsigned midx = static_cast<unsigned>(m);
        if (!m_cache_ptr[midx] || !is_eqp(env, m_cache_ptr[midx]->env())) {
            m_cache_ptr[midx].reset(new Cache(env));
        }
        return *m_cache_ptr[midx].get();
    }

    Cache & get_cache_for(type_context_old const & ctx) {
        return get_cache_for(ctx.env(), ctx.mode());
    }

    void clear() {
        for (unsigned i = 0; i < 4; i++) m_cache_ptr[i].reset();
    }
};
}




// ========== reducible.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/util.h"

namespace lean {
enum class reducible_status { Reducible, Semireducible, Irreducible };
/** \brief Mark the definition named \c n as reducible or not.

    The method throws an exception if \c n is
      - not a definition
      - a theorem
      - an opaque definition that was not defined in main module

    "Reducible" definitions can be freely unfolded by automation (i.e., elaborator, simplifier, etc).
    We should view it as a hint to automation.
*/
environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent);

reducible_status get_reducible_status(environment const & env, name const & n);

inline bool is_reducible(environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Reducible; }
inline bool is_semireducible(environment const & env, name const & n) { return get_reducible_status(env, n) == reducible_status::Semireducible; }

/* \brief Execute the given function for each declaration explicitly marked with a reducibility annotation */
void for_each_reducible(environment const & env, std::function<void(name const &, reducible_status)> const & fn);

/** \brief Create a predicate that returns true for all non reducible constants in \c env */
name_predicate mk_not_reducible_pred(environment const & env);
/** \brief Create a predicate that returns true for irreducible constants  in \c env */
name_predicate mk_irreducible_pred(environment const & env);

unsigned get_reducibility_fingerprint(environment const & env);

void initialize_reducible();
void finalize_reducible();
}




// ========== reducible.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/attribute_manager.h"

namespace lean {
static name * g_reducibility = nullptr;

unsigned get_reducibility_fingerprint(environment const & env) {
    return get_attribute_fingerprint(env, *g_reducibility);
}

struct reducibility_attribute_data : public attr_data {
    reducible_status m_status;
    reducibility_attribute_data() {}
    reducibility_attribute_data(reducible_status status) : m_status(status) {}

    virtual unsigned hash() const override {
        return static_cast<unsigned>(m_status);
    }
    void write(serializer & s) const {
        s << static_cast<char>(m_status);
    }
    void read(deserializer & d) {
        char c;
        d >> c;
        m_status = static_cast<reducible_status>(c);
    }
};

bool operator==(reducibility_attribute_data const & d1, reducibility_attribute_data const & d2) {
    return d1.m_status == d2.m_status;
}

template class typed_attribute<reducibility_attribute_data>;
typedef typed_attribute<reducibility_attribute_data> reducibility_attribute;

static reducibility_attribute const & get_reducibility_attribute() {
    return static_cast<reducibility_attribute const &>(get_system_attribute(*g_reducibility));
}

class reducibility_proxy_attribute : public proxy_attribute<reducibility_attribute_data> {
    typedef proxy_attribute<reducibility_attribute_data> parent;
public:
    reducibility_proxy_attribute(char const * id, char const * descr, reducible_status m_status):
        parent(id, descr, m_status) {}

    virtual typed_attribute<reducibility_attribute_data> const & get_attribute() const override {
        return get_reducibility_attribute();
    }

    virtual environment set(environment const & env, io_state const & ios, name const & n,
                            unsigned prio, bool persistent) const override {
        declaration const & d = env.get(n);
        if (!d.is_definition())
            throw exception(sstream() << "invalid reducible command, '" << n << "' is not a definition");
        return parent::set(env, ios, n, prio, persistent);
    }
};

void initialize_reducible() {
    g_reducibility = new name("reducibility");
    register_system_attribute(reducibility_attribute(*g_reducibility, "internal attribute for storing reducibility"));

    register_system_attribute(reducibility_proxy_attribute("reducible", "reducible", reducible_status::Reducible));
    register_system_attribute(reducibility_proxy_attribute("semireducible", "semireducible", reducible_status::Semireducible));
    register_system_attribute(reducibility_proxy_attribute("irreducible", "irreducible", reducible_status::Irreducible));

    register_incompatible("reducible", "semireducible");
    register_incompatible("reducible", "irreducible");
    register_incompatible("semireducible", "irreducible");
}

void finalize_reducible() {
    delete g_reducibility;
}

environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent) {
    return get_reducibility_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, {s}, persistent);
}

reducible_status get_reducible_status(environment const & env, name const & n) {
    auto data = get_reducibility_attribute().get(env, n);
    if (data)
        return data->m_status;
    return reducible_status::Semireducible;
}

name_predicate mk_not_reducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return get_reducible_status(env, n) != reducible_status::Reducible;
    };
}

name_predicate mk_irreducible_pred(environment const & env) {
    return [=](name const & n) { // NOLINT
        return get_reducible_status(env, n) == reducible_status::Irreducible;
    };
}
}




// ========== util.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/expr_pair.h"

namespace lean {
/* If \c n is not in \c env, then return \c. Otherwise, find the first j >= idx s.t.
   n.append_after(j) is not in \c env. */
name mk_unused_name(environment const & env, name const & n, unsigned & idx);

/* If \c n is not in \c env, then return \c. Otherwise, find the first j >= 1 s.t.
   n.append_after(j) is not in \c env. */
name mk_unused_name(environment const & env, name const & n);

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type);

optional<expr> is_optional_param(expr const & e);

optional<expr_pair> is_auto_param(expr const & e);

/** \brief Return the universe level of the type of \c A.
    Throws an exception if the (relaxed) whnf of the type
    of A is not a sort. */
level get_level(abstract_type_context & ctx, expr const & A);

/** brief Return a name that does not appear in `lp_names`. */
name mk_fresh_lp_name(level_param_names const & lp_names);

/** \brief Return true iff \c n occurs in \c m */
bool occurs(expr const & n, expr const & m);
/** \brief Return true iff there is a constant named \c n in \c m. */
bool occurs(name const & n, expr const & m);

/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_k) */
bool is_app_of(expr const & t, name const & f_name);
/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_nargs) */
bool is_app_of(expr const & t, name const & f_name, unsigned nargs);

/** \brief If type is of the form (auto_param A p) or (opt_param A v), return A. Otherwise, return type. */
expr consume_auto_opt_param(expr const & type);

/** \brief Unfold constant \c e or constant application (i.e., \c e is of the form (f ....),
    where \c f is a constant */
optional<expr> unfold_term(environment const & env, expr const & e);
/** \brief If \c e is of the form <tt>(f a_1 ... a_n)</tt>, where \c f is
    a non-opaque definition, then unfold \c f, and beta reduce.
    Otherwise, return none. */
optional<expr> unfold_app(environment const & env, expr const & e);

/** \brief Reduce (if possible) universe level by 1.
    \pre is_not_zero(l) */
optional<level> dec_level(level const & l);

bool has_punit_decls(environment const & env);
bool has_pprod_decls(environment const & env);
bool has_eq_decls(environment const & env);
bool has_heq_decls(environment const & env);
bool has_and_decls(environment const & env);

/** \brief Return true iff \c n is the name of a recursive datatype in \c env.
    That is, it must be an inductive datatype AND contain a recursive constructor.

    \remark Records are inductive datatypes, but they are not recursive.

    \remark For mutually indutive datatypes, \c n is considered recursive
    if there is a constructor taking \c n. */
bool is_recursive_datatype(environment const & env, name const & n);

/** \brief Return true if \c n is a recursive *and* reflexive datatype.

    We say an inductive type T is reflexive if it contains at least one constructor that
    takes as an argument a function returning T. */
bool is_reflexive_datatype(abstract_type_context & tc, name const & n);

/** \brief Return true iff \c n is an inductive predicate, i.e., an inductive datatype that is in Prop.

    \remark If \c env does not have Prop (i.e., Type.{0} is not impredicative), then this method always return false. */
bool is_inductive_predicate(environment const & env, name const & n);

/** \brief Return true iff \c n is an inductive type with a recursor with an extra level parameter. */
bool can_elim_to_type(environment const & env, name const & n);

/** \brief Store in \c result the introduction rules of the given inductive datatype.
    \remark this procedure does nothing if \c n is not an inductive datatype. */
void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result);

/** \brief If \c e is a constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app(environment const & env, expr const & e);

/** \brief If \c e is a constructor application, or a definition that wraps a
    constructor application, then return the name of the constructor.
    Otherwise, return none. */
optional<name> is_constructor_app_ext(environment const & env, expr const & e);

/** \brief Store in \c result a bit-vector indicating which fields of the constructor \c n are
    (computationally) relevant.
    \pre inductive::is_intro_rule(env, n) */
void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result);

/** \brief Return the index (position) of the given constructor in the inductive datatype declaration.
    \pre inductive::is_intro_rule(env, n) */
unsigned get_constructor_idx(environment const & env, name const & n);

/** Given a C.rec, each minor premise has n arguments, and some of these arguments are inductive
    hypotheses. This function return then number of inductive hypotheses for the minor premise associated with
    the constructor named \c n. */
unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n);
/** Given a constructor \c n, store in the bitmask rec_mask[i] = true iff the i-th argument
    of \c n is recursive.

    \pre is_intro_rule(n) && rec_mask.empty() */
void get_constructor_rec_arg_mask(environment const & env, name const & n, buffer<bool> & rec_mask);
/** Combines get_num_inductive_hypotheses_for and get_constructor_rec_arg_mask */
unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n, buffer<bool> & rec_mask);

/* Store in `rec_args` the recursive arguments of constructor application \c `e`.
   The result is false if `e` is not a constructor application.
   The unsigned value at rec_args represents the arity of the recursive argument.
   The value is only greater than zero for reflexive inductive datatypes such as:

      inductive inftree (A : Type)
      | leaf : A → inftree
      | node : (nat → inftree) → inftree
*/
bool get_constructor_rec_args(environment const & env, expr const & e, buffer<pair<expr, unsigned>> & rec_args);

/** \brief Given an expression \c e, return the number of arguments expected arguments.

    \remark This function computes the type of \c e, and then counts the number of nested
    Pi's. Weak-head-normal-forms are computed for the type of \c e.
    \remark The type and whnf are computed using \c tc. */
unsigned get_expect_num_args(abstract_type_context & ctx, expr e);

/** \brief "Consume" Pi-type \c type. This procedure creates local constants based on the domain of \c type
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached in the domain.
    The procedure returns the "body" of type. */
expr to_telescope(expr const & type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief "Consume" fun/lambda. This procedure creates local constants based on the arguments of \c e
    and store them in telescope. If \c binfo is provided, then the local constants are annoted with the given
    binder_info, otherwise the procedure uses the one attached to the arguments.
    The procedure returns the "body" of function. */
expr fun_to_telescope(expr const & e, buffer<expr> & telescope, optional<binder_info> const & binfo);

/** \brief Similar to previous procedure, but puts \c type in whnf */
expr to_telescope(type_checker & ctx, expr type, buffer<expr> & telescope,
                  optional<binder_info> const & binfo = optional<binder_info>());

/** \brief Return the universe where inductive datatype resides
    \pre \c ind_type is of the form <tt>Pi (a_1 : A_1) (a_2 : A_2[a_1]) ..., Type.{lvl}</tt> */
level get_datatype_level(environment const & env, expr const & ind_type);

/** \brief Update the result sort of the given type */
expr update_result_sort(expr t, level const & l);

expr instantiate_univ_param (expr const & e, name const & p, level const & l);

expr mk_true();
bool is_true(expr const & e);
expr mk_true_intro();

bool is_and(expr const & e, expr & arg1, expr & arg2);
bool is_and(expr const & e);
expr mk_and(expr const & a, expr const & b);
expr mk_and_intro(abstract_type_context & ctx, expr const & Ha, expr const & Hb);
expr mk_and_elim_left(abstract_type_context & ctx, expr const & H);
expr mk_and_elim_right(abstract_type_context & ctx, expr const & H);

expr mk_unit(level const & l);
expr mk_unit_mk(level const & l);

expr mk_pprod(abstract_type_context & ctx, expr const & A, expr const & B);
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b);
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p);
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p);

expr mk_unit(level const & l, bool prop);
expr mk_unit_mk(level const & l, bool prop);

expr mk_pprod(abstract_type_context & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b, bool prop);
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p, bool prop);
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p, bool prop);

expr mk_nat_type();
bool is_nat_type(expr const & e);
expr mk_nat_zero();
expr mk_nat_one();
expr mk_nat_bit0(expr const & e);
expr mk_nat_bit1(expr const & e);
expr mk_nat_add(expr const & e1, expr const & e2);

expr mk_int_type();
bool is_int_type(expr const & e);

expr mk_char_type();

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f);
bool is_ite(expr const & e);

bool is_iff(expr const & e);
bool is_iff(expr const & e, expr & lhs, expr & rhs);
expr mk_iff(expr const & lhs, expr const & rhs);
expr mk_iff_refl(expr const & a);

expr mk_propext(expr const & lhs, expr const & rhs, expr const & iff_pr);

expr mk_eq(abstract_type_context & ctx, expr const & lhs, expr const & rhs);
expr mk_eq_refl(abstract_type_context & ctx, expr const & a);
expr mk_eq_symm(abstract_type_context & ctx, expr const & H);
expr mk_eq_trans(abstract_type_context & ctx, expr const & H1, expr const & H2);
expr mk_eq_subst(abstract_type_context & ctx, expr const & motive,
                 expr const & x, expr const & y, expr const & xeqy, expr const & h);
expr mk_eq_subst(abstract_type_context & ctx, expr const & motive, expr const & xeqy, expr const & h);

expr mk_congr_arg(abstract_type_context & ctx, expr const & f, expr const & H);

/** \brief Create an proof for x = y using subsingleton.elim (in standard mode) */
expr mk_subsingleton_elim(abstract_type_context & ctx, expr const & h, expr const & x, expr const & y);

/** \brief Return true iff \c e is a term of the form (eq.rec ....) */
bool is_eq_rec_core(expr const & e);
/** \brief Return true iff \c e is a term of the form (eq.rec ....) */
bool is_eq_rec(expr const & e);
/** \brief Return true iff \c e is a term of the form (eq.drec ....) */
bool is_eq_drec(expr const & e);

bool is_eq(expr const & e);
bool is_eq(expr const & e, expr & lhs, expr & rhs);
bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs);
/** \brief Return true iff \c e is of the form (eq A a a) */
bool is_eq_a_a(expr const & e);
/** \brief Return true iff \c e is of the form (eq A a a') where \c a and \c a' are definitionally equal */
bool is_eq_a_a(abstract_type_context & ctx, expr const & e);

expr mk_heq(abstract_type_context & ctx, expr const & lhs, expr const & rhs);
bool is_heq(expr const & e);
bool is_heq(expr const & e, expr & lhs, expr & rhs);
bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs);

expr mk_cast(abstract_type_context & ctx, expr const & H, expr const & e);

expr mk_false();
expr mk_empty();

bool is_false(expr const & e);
bool is_empty(expr const & e);
/** \brief Return an element of type t given an element \c f : false */
expr mk_false_rec(abstract_type_context & ctx, expr const & f, expr const & t);

bool is_or(expr const & e);
bool is_or(expr const & e, expr & A, expr & B);

/** \brief Return true if \c e is of the form <tt>(not arg)</tt> or <tt>arg -> false</tt>, and store \c arg in \c a.
     Return false otherwise */
bool is_not(expr const & e, expr & a);
inline bool is_not(expr const & e) { expr a; return is_not(e, a); }
/** \brief Extends is_not to handle (lhs ≠ rhs). In the new case, it stores (lhs = rhs) in \c a. */
bool is_not_or_ne(expr const & e, expr & a);
expr mk_not(expr const & e);

/** \brief Create the term <tt>absurd e not_e : t</tt>. */
expr mk_absurd(abstract_type_context & ctx, expr const & t, expr const & e, expr const & not_e);

/** \brief Returns none if \c e is not an application with at least two arguments.
    Otherwise it returns <tt>app_fn(app_fn(e))</tt>. */
optional<expr> get_binary_op(expr const & e);
optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2);

/** \brief Makes n-ary (right-associative) application. */
expr mk_nary_app(expr const & op, buffer<expr> const & nary_args);
expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args);

expr mk_bool();
expr mk_bool_tt();
expr mk_bool_ff();
expr to_bool_expr(bool b);

/* Similar to is_head_beta, but ignores annotations around the function. */
bool is_annotated_head_beta(expr const & t);
/* Similar to head_beta_reduce, but also reduces annotations around the function. */
expr annotated_head_beta_reduce(expr const & t);

bool is_exists(expr const & e, expr & A, expr & p);
bool is_exists(expr const & e);

expr try_eta(expr const & e);
expr beta_reduce(expr t);
expr eta_reduce(expr t);
expr beta_eta_reduce(expr t);

enum class implicit_infer_kind { Implicit, RelaxedImplicit, None };

/** \brief Infer implicit parameter annotations for the first \c nparams using mode
    specified by \c k. */
expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k);


/** Given an inductive datatype named \c n, return a recursor for \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_recursor(environment const & env, name const & n);

/** Given an inductive datatype named \c n, return a cases_on recursor \c n that supports dependent elimination
    even if \c n is an inductive predicate. */
name get_dep_cases_on(environment const & env, name const & n);

/** We generate auxiliary meta definitions for regular recursive definitions.
    The auxiliary meta definition has a clear runtime cost execution model, and
    we use it in the VM. This function returns an auxiliary meta definition for the given name. */
name mk_aux_meta_rec_name(name const & n);

/** Return some(n') if \c n is a name created using mk_aux_meta_rec_name(n') */
optional<name> is_aux_meta_rec_name(name const & n);

/** Convert an expression representing a `name` literal into a `name` object. */
optional<name> name_lit_to_name(expr const & name_lit);

/** Return (tactic unit) type */
expr mk_tactic_unit();

std::string const & get_version_string();

void initialize_library_util();
void finalize_library_util();
}




// ========== util.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/fresh_name.h"
#include "kernel/find_fn.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/replace_visitor.h"
#include "library/type_context.h"
#include "library/string.h"
#include "version.h"
#include "githash.h" // NOLINT

namespace lean {
name mk_unused_name(environment const & env, name const & n, unsigned & idx) {
    name curr = n;
    while (true) {
        if (!env.find(curr))
            return curr;
        curr = n.append_after(idx);
        idx++;
    }
}

name mk_unused_name(environment const & env, name const & n) {
    unsigned idx = 1;
    return mk_unused_name(env, n, idx);
}

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type) {
    unsigned r = 0;
    while (is_pi(type)) {
        type = binding_body(type);
        r++;
    }
    return r;
}

optional<expr> is_optional_param(expr const & e) {
    if (is_app_of(e, get_opt_param_name(), 2)) {
        return some_expr(app_arg(e));
    } else {
        return none_expr();
    }
}

optional<expr_pair> is_auto_param(expr const & e) {
    if (is_app_of(e, get_auto_param_name(), 2)) {
        return optional<expr_pair>(app_arg(app_fn(e)), app_arg(e));
    } else {
        return optional<expr_pair>();
    }
}

level get_level(abstract_type_context & ctx, expr const & A) {
    expr S = ctx.relaxed_whnf(ctx.infer(A));
    if (!is_sort(S))
        throw exception("invalid expression, sort expected");
    return sort_level(S);
}

name mk_fresh_lp_name(level_param_names const & lp_names) {
    name l("l");
    int i = 1;
    while (std::find(lp_names.begin(), lp_names.end(), l) != lp_names.end()) {
        l = name("l").append_after(i);
        i++;
    }
    return l;
}

bool occurs(expr const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return n == e; }));
}

bool occurs(name const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; }));
}

bool is_app_of(expr const & t, name const & f_name) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name;
}

bool is_app_of(expr const & t, name const & f_name, unsigned nargs) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name && get_app_num_args(t) == nargs;
}

expr consume_auto_opt_param(expr const & type) {
    if (is_app_of(type, get_auto_param_name(), 2) || is_app_of(type, get_opt_param_name(), 2)) {
        return app_arg(app_fn(type));
    } else {
        return type;
    }
}

optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return none_expr();
    expr d = instantiate_value_univ_params(*decl, const_levels(f));
    buffer<expr> args;
    get_app_rev_args(e, args);
    return some_expr(apply_beta(d, args.size(), args.data()));
}

optional<expr> unfold_app(environment const & env, expr const & e) {
    if (!is_app(e))
        return none_expr();
    return unfold_term(env, e);
}

optional<level> dec_level(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
        return none_level();
    case level_kind::Succ:
        return some_level(succ_of(l));
    case level_kind::Max:
        if (auto lhs = dec_level(max_lhs(l))) {
        if (auto rhs = dec_level(max_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    case level_kind::IMax:
        // Remark: the following mk_max is not a typo. The following
        // assertion justifies it.
        if (auto lhs = dec_level(imax_lhs(l))) {
        if (auto rhs = dec_level(imax_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Return true if environment has a constructor named \c c that returns
    an element of the inductive datatype named \c I, and \c c must have \c nparams parameters. */
bool has_constructor(environment const & env, name const & c, name const & I, unsigned nparams) {
    auto d = env.find(c);
    if (!d || d->is_definition())
        return false;
    expr type = d->get_type();
    unsigned i = 0;
    while (is_pi(type)) {
        i++;
        type = binding_body(type);
    }
    if (i != nparams)
        return false;
    type = get_app_fn(type);
    return is_constant(type) && const_name(type) == I;
}

bool has_punit_decls(environment const & env) {
    return has_constructor(env, get_punit_star_name(), get_punit_name(), 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, get_eq_refl_name(), get_eq_name(), 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, get_heq_refl_name(), get_heq_name(), 2);
}

bool has_pprod_decls(environment const & env) {
    return has_constructor(env, get_pprod_mk_name(), get_pprod_name(), 4);
}

bool has_and_decls(environment const & env) {
    return has_constructor(env, get_and_intro_name(), get_and_name(), 4);
}

/* n is considered to be recursive if it is an inductive datatype and
   1) It has a constructor that takes n as an argument
   2) It is part of a mutually recursive declaration, and some constructor
      of an inductive datatype takes another inductive datatype from the
      same declaration as an argument. */
bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            if (find(binding_domain(type), [&](expr const & e, unsigned) {
                        if (is_constant(e)) {
                            name const & c = const_name(e);
                            if (decl->m_name == c) return true;
                        }
                        return false;
                    })) {
                return true;
            }
            type = binding_body(type);
        }
    }
    return false;
}

bool is_reflexive_datatype(abstract_type_context & tc, name const & n) {
    environment const & env = tc.env();
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            expr arg   = tc.whnf(binding_domain(type));
            if (is_pi(arg) && find(arg, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; })) {
                return true;
            }
            expr local = mk_local(tc.next_name(), binding_domain(type));
            type = instantiate(binding_body(type), local);
        }
    }
    return false;
}

level get_datatype_level(environment const & env, expr const & ind_type) {
    expr it = ind_type;
    while (is_pi(it))
        it = binding_body(it);
    if (is_sort(it)) {
        return sort_level(it);
    } else {
        type_checker ctx(env);
        buffer<expr> telescope;
        expr it = ctx.whnf(to_telescope(ctx, ind_type, telescope));
        if (is_sort(it)) {
            return sort_level(it);
        } else {
            throw exception("invalid inductive datatype type");
        }
    }
}

expr update_result_sort(expr t, level const & l) {
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

bool is_inductive_predicate(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    return is_zero(get_datatype_level(env, env.get(n).get_type()));
}

bool can_elim_to_type(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    declaration ind_decl = env.get(n);
    declaration rec_decl = env.get(inductive::get_elim_name(n));
    return rec_decl.get_num_univ_params() > ind_decl.get_num_univ_params();
}

void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result) {
    if (auto decl = inductive::is_inductive_decl(env, n)) {
        for (inductive::intro_rule const & ir : decl->m_intro_rules) {
            result.push_back(inductive::intro_rule_name(ir));
        }
    }
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return optional<name>();
    expr const * it = &decl->get_value();
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

static bool is_irrelevant_field_type(type_checker & tc, expr const & ftype) {
    if (tc.is_prop(ftype)) return true;
    buffer<expr> tele;
    expr n_ftype = to_telescope(tc, ftype, tele);
    return is_sort(n_ftype) || tc.is_prop(n_ftype);
}

void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result) {
    lean_assert(inductive::is_intro_rule(env, n));
    expr type        = env.get(n).get_type();
    name I_name      = *inductive::is_intro_rule(env, n);
    unsigned nparams = *inductive::get_num_params(env, I_name);
    buffer<expr> telescope;
    type_checker tc(env);
    to_telescope(tc, type, telescope);
    lean_assert(telescope.size() >= nparams);
    for (unsigned i = nparams; i < telescope.size(); i++) {
        result.push_back(!is_irrelevant_field_type(tc, mlocal_type(telescope[i])));
    }
}

unsigned get_constructor_idx(environment const & env, name const & n) {
    lean_assert(inductive::is_intro_rule(env, n));
    name I_name = *inductive::is_intro_rule(env, n);
    buffer<name> cnames;
    get_intro_rule_names(env, I_name, cnames);
    unsigned r  = 0;
    for (name const & cname : cnames) {
        if (cname == n)
            return r;
        r++;
    }
    lean_unreachable();
}

unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n, buffer<bool> & rec_mask) {
    lean_assert(inductive::is_intro_rule(env, n));
    lean_assert(rec_mask.empty());
    name I_name = *inductive::is_intro_rule(env, n);
    inductive::inductive_decl decl = *inductive::is_inductive_decl(env, I_name);
    type_context_old tc(env);
    type_context_old::tmp_locals locals(tc);
    expr type   = tc.whnf(env.get(n).get_type());
    unsigned r  = 0;
    while (is_pi(type)) {
        auto dom = tc.whnf(binding_domain(type));
        while (is_pi(dom)) {
            dom = tc.whnf(instantiate(binding_body(dom), locals.push_local_from_binding(dom)));
        }
        auto fn = get_app_fn(dom);
        if (is_constant(fn) && const_name(fn) == decl.m_name) {
            rec_mask.push_back(true);
            r++;
        } else {
            rec_mask.push_back(false);
        }
        type = tc.whnf(instantiate(binding_body(type), locals.push_local_from_binding(type)));
    }
    return r;
}

unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n) {
    buffer<bool> rec_mask;
    return get_num_inductive_hypotheses_for(env, n, rec_mask);
}

void get_constructor_rec_arg_mask(environment const & env, name const & n, buffer<bool> & rec_mask) {
    get_num_inductive_hypotheses_for(env, n, rec_mask);
}

expr instantiate_univ_param (expr const & e, name const & p, level const & l) {
    return instantiate_univ_params(e, to_list(p), to_list(l));
}

unsigned get_expect_num_args(abstract_type_context & ctx, expr e) {
    push_local_fn push_local(ctx);
    unsigned r = 0;
    while (true) {
        e = ctx.whnf(e);
        if (!is_pi(e))
            return r;
        // TODO(Leo): try to avoid the following instantiate.
        expr local = push_local(binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}

expr to_telescope(bool pi, expr e, buffer<expr> & telescope,
                  optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, type, telescope, binfo);
}

expr fun_to_telescope(expr const & e, buffer<expr> & telescope,
                      optional<binder_info> const & binfo) {
    return to_telescope(false, e, telescope, binfo);
}

expr to_telescope(type_checker & ctx, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    expr new_type = ctx.whnf(type);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = mk_local(ctx.next_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(ctx.next_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = ctx.whnf(type);
    }
    return type;
}

/* ----------------------------------------------

   Helper functions for creating basic operations

   ---------------------------------------------- */
static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_elim_left = nullptr;
static expr * g_and_elim_right = nullptr;

expr mk_true() {
    return *g_true;
}

bool is_true(expr const & e) {
    return e == *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
}

bool is_and(expr const & e) {
    return is_app_of(e, get_and_name(), 2);
}

bool is_and(expr const & e, expr & arg1, expr & arg2) {
    if (is_and(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return true;
    } else {
        return false;
    }
}

expr mk_and(expr const & a, expr const & b) {
    return mk_app(*g_and, a, b);
}

expr mk_and_intro(abstract_type_context & ctx, expr const & Ha, expr const & Hb) {
    return mk_app(*g_and_intro, ctx.infer(Ha), ctx.infer(Hb), Ha, Hb);
}

expr mk_and_elim_left(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_left, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_and_elim_right(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_right, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_unit(level const & l) {
    return mk_constant(get_punit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_punit_star_name(), {l});
}

expr mk_pprod(abstract_type_context & ctx, expr const & A, expr const & B) {
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_name(), {l1, l2}), A, B);
}

expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b) {
    expr A = ctx.infer(a);
    expr B = ctx.infer(b);
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_mk_name(), {l1, l2}), A, B, a, b);
}

expr mk_pprod_fst(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_fst_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pprod_snd(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_snd_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

static expr * g_nat         = nullptr;
static expr * g_nat_zero    = nullptr;
static expr * g_nat_one     = nullptr;
static expr * g_nat_bit0_fn = nullptr;
static expr * g_nat_bit1_fn = nullptr;
static expr * g_nat_add_fn  = nullptr;

static void initialize_nat() {
    g_nat            = new expr(mk_constant(get_nat_name()));
    g_nat_zero       = new expr(mk_app(mk_constant(get_has_zero_zero_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_zero_name())}));
    g_nat_one        = new expr(mk_app(mk_constant(get_has_one_one_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name())}));
    g_nat_bit0_fn    = new expr(mk_app(mk_constant(get_bit0_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
    g_nat_bit1_fn    = new expr(mk_app(mk_constant(get_bit1_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name()), mk_constant(get_nat_has_add_name())}));
    g_nat_add_fn     = new expr(mk_app(mk_constant(get_has_add_add_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
}

static void finalize_nat() {
    delete g_nat;
    delete g_nat_zero;
    delete g_nat_one;
    delete g_nat_bit0_fn;
    delete g_nat_bit1_fn;
    delete g_nat_add_fn;
}

expr mk_nat_type() { return *g_nat; }
bool is_nat_type(expr const & e) { return e == *g_nat; }
expr mk_nat_zero() { return *g_nat_zero; }
expr mk_nat_one() { return *g_nat_one; }
expr mk_nat_bit0(expr const & e) { return mk_app(*g_nat_bit0_fn, e); }
expr mk_nat_bit1(expr const & e) { return mk_app(*g_nat_bit1_fn, e); }
expr mk_nat_add(expr const & e1, expr const & e2) { return mk_app(*g_nat_add_fn, e1, e2); }

static expr * g_int = nullptr;

static void initialize_int() {
    g_int = new expr(mk_constant(get_int_name()));
}

static void finalize_int() {
    delete g_int;
}

expr mk_int_type() { return *g_int; }
bool is_int_type(expr const & e) { return e == *g_int; }

static expr * g_char = nullptr;

expr mk_char_type() { return *g_char; }

static void initialize_char() {
    g_char = new expr(mk_constant(get_char_name()));
}

static void finalize_char() {
    delete g_char;
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }

expr mk_pprod(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and(a, b) : mk_pprod(ctx, a, b);
}
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(ctx, a, b) : mk_pprod_mk(ctx, a, b);
}
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_left(ctx, p) : mk_pprod_fst(ctx, p);
}
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_right(ctx, p) : mk_pprod_snd(ctx, p);
}

bool is_ite(expr const & e) {
    return is_app_of(e, get_ite_name(), 5);
}

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f) {
    if (is_ite(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 5);
        c = args[0]; H = args[1]; A = args[2]; t = args[3]; f = args[4];
        return true;
    } else {
        return false;
    }
}

bool is_iff(expr const & e) {
    return is_app_of(e, get_iff_name(), 2);
}

bool is_iff(expr const & e, expr & lhs, expr & rhs) {
    if (!is_iff(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}
expr mk_iff(expr const & lhs, expr const & rhs) {
    return mk_app(mk_constant(get_iff_name()), lhs, rhs);
}
expr mk_iff_refl(expr const & a) {
    return mk_app(mk_constant(get_iff_refl_name()), a);
}
expr mk_propext(expr const & lhs, expr const & rhs, expr const & iff_pr) {
    return mk_app(mk_constant(get_propext_name()), lhs, rhs, iff_pr);
}

expr mk_eq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_name(), {lvl}), A, lhs, rhs);
}

expr mk_eq_refl(abstract_type_context & ctx, expr const & a) {
    expr A    = ctx.whnf(ctx.infer(a));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
}

expr mk_eq_symm(abstract_type_context & ctx, expr const & H) {
    if (is_app_of(H, get_eq_refl_name()))
        return H;
    expr p    = ctx.whnf(ctx.infer(H));
    lean_assert(is_eq(p));
    expr lhs  = app_arg(app_fn(p));
    expr rhs  = app_arg(p);
    expr A    = ctx.infer(lhs);
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
}

expr mk_eq_trans(abstract_type_context & ctx, expr const & H1, expr const & H2) {
    if (is_app_of(H1, get_eq_refl_name()))
        return H2;
    if (is_app_of(H2, get_eq_refl_name()))
        return H1;
    expr p1    = ctx.whnf(ctx.infer(H1));
    expr p2    = ctx.whnf(ctx.infer(H2));
    lean_assert(is_eq(p1) && is_eq(p2));
    expr lhs1  = app_arg(app_fn(p1));
    expr rhs1  = app_arg(p1);
    expr rhs2  = app_arg(p2);
    expr A     = ctx.infer(lhs1);
    level lvl  = get_level(ctx, A);
    return mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive,
                 expr const & x, expr const & y, expr const & xeqy, expr const & h) {
    expr A    = ctx.infer(x);
    level l1  = get_level(ctx, A);
    expr r    = mk_constant(get_eq_subst_name(), {l1});
    return mk_app({r, A, x, y, motive, xeqy, h});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive, expr const & xeqy, expr const & h) {
    expr xeqy_type = ctx.whnf(ctx.infer(xeqy));
    return mk_eq_subst(ctx, motive, app_arg(app_fn(xeqy_type)), app_arg(xeqy_type), xeqy, h);
}

expr mk_congr_arg(abstract_type_context & ctx, expr const & f, expr const & H) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi = ctx.relaxed_whnf(ctx.infer(f));
    expr A, B, lhs, rhs;
    lean_verify(is_eq(eq, A, lhs, rhs));
    lean_assert(is_arrow(pi));
    B = binding_body(pi);
    level lvl_1  = get_level(ctx, A);
    level lvl_2  = get_level(ctx, B);
    return ::lean::mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
}

expr mk_subsingleton_elim(abstract_type_context & ctx, expr const & h, expr const & x, expr const & y) {
    expr A  = ctx.infer(x);
    level l = get_level(ctx, A);
    expr r  = mk_constant(get_subsingleton_elim_name(), {l});
    return mk_app({r, A, h, x, y});
}

expr mk_heq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    expr B    = ctx.whnf(ctx.infer(rhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_heq_name(), {lvl}), A, lhs, B, rhs);
}

bool is_eq_rec_core(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_rec_name();
}

bool is_eq_rec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_rec_name();
}

bool is_eq_drec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_drec_name();
}

bool is_eq(expr const & e) {
    return is_app_of(e, get_eq_name(), 3);
}

bool is_eq(expr const & e, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    A   = app_arg(app_fn(app_fn(e)));
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq_a_a(expr const & e) {
    if (!is_eq(e))
        return false;
    expr lhs = app_arg(app_fn(e));
    expr rhs = app_arg(e);
    return lhs == rhs;
}

bool is_eq_a_a(abstract_type_context & ctx, expr const & e) {
    if (!is_eq(e))
        return false;
    expr lhs = app_arg(app_fn(e));
    expr rhs = app_arg(e);
    return ctx.is_def_eq(lhs, rhs);
}

bool is_heq(expr const & e) {
    return is_app_of(e, get_heq_name(), 4);
}

bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs) {
    if (is_heq(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 4);
        A = args[0]; lhs = args[1]; B = args[2]; rhs = args[3];
        return true;
    } else {
        return false;
    }
}

bool is_heq(expr const & e, expr & lhs, expr & rhs) {
    expr A, B;
    return is_heq(e, A, lhs, B, rhs);
}

expr mk_cast(abstract_type_context & ctx, expr const & H, expr const & e) {
    expr type = ctx.relaxed_whnf(ctx.infer(H));
    expr A, B;
    if (!is_eq(type, A, B))
        throw exception("cast failed, equality proof expected");
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_cast_name(), {lvl}), A, B, H, e);
}

expr mk_false() {
    return mk_constant(get_false_name());
}

expr mk_empty() {
    return mk_constant(get_empty_name());
}

bool is_false(expr const & e) {
    return is_constant(e) && const_name(e) == get_false_name();
}

bool is_empty(expr const & e) {
    return is_constant(e) && const_name(e) == get_empty_name();
}

expr mk_false_rec(abstract_type_context & ctx, expr const & f, expr const & t) {
    level t_lvl = get_level(ctx, t);
    return mk_app(mk_constant(get_false_rec_name(), {t_lvl}), t, f);
}

bool is_or(expr const & e) {
    return is_app_of(e, get_or_name(), 2);
}

bool is_or(expr const & e, expr & A, expr & B) {
    if (is_or(e)) {
        A = app_arg(app_fn(e));
        B = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_not(expr const & e, expr & a) {
    if (is_app_of(e, get_not_name(), 1)) {
        a = app_arg(e);
        return true;
    } else if (is_pi(e) && is_false(binding_body(e))) {
        a = binding_domain(e);
        return true;
    } else {
        return false;
    }
}

bool is_not_or_ne(expr const & e, expr & a) {
    if (is_not(e, a)) {
        return true;
    } else if (is_app_of(e, get_ne_name(), 3)) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        expr new_fn     = mk_constant(get_eq_name(), const_levels(fn));
        a               = mk_app(new_fn, args);
        return true;
    } else {
        return false;
    }
}

expr mk_not(expr const & e) {
    return mk_app(mk_constant(get_not_name()), e);
}

expr mk_absurd(abstract_type_context & ctx, expr const & t, expr const & e, expr const & not_e) {
    level t_lvl  = get_level(ctx, t);
    expr  e_type = ctx.infer(e);
    return mk_app(mk_constant(get_absurd_name(), {t_lvl}), e_type, t, e, not_e);
}

bool is_exists(expr const & e, expr & A, expr & p) {
    if (is_app_of(e, get_Exists_name(), 2)) {
        A = app_arg(app_fn(e));
        p = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_exists(expr const & e) {
    return is_app_of(e, get_Exists_name(), 2);
}

optional<expr> get_binary_op(expr const & e) {
    if (!is_app(e) || !is_app(app_fn(e)))
        return none_expr();
    return some_expr(app_fn(app_fn(e)));
}

optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2) {
    if (auto op = get_binary_op(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return some_expr(*op);
    } else {
        return none_expr();
    }
}

expr mk_nary_app(expr const & op, buffer<expr> const & nary_args) {
    return mk_nary_app(op, nary_args.size(), nary_args.data());
}

expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args) {
    lean_assert(num_nary_args >= 2);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    expr e = mk_app(op, nary_args[num_nary_args - 2], nary_args[num_nary_args - 1]);
    for (int i = num_nary_args - 3; i >= 0; --i) {
        e = mk_app(op, nary_args[i], e);
    }
    return e;
}

bool is_annotated_lamba(expr const & e) {
    return
        is_lambda(e) ||
        (is_annotation(e) && is_lambda(get_nested_annotation_arg(e)));
}

bool is_annotated_head_beta(expr const & t) {
    return is_app(t) && is_annotated_lamba(get_app_fn(t));
}

expr annotated_head_beta_reduce(expr const & t) {
    if (!is_annotated_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr f = get_app_rev_args(t, args);
        if (is_annotation(f))
            f = get_nested_annotation_arg(f);
        lean_assert(is_lambda(f));
        return annotated_head_beta_reduce(apply_beta(f, args.size(), args.data()));
    }
}

expr try_eta(expr const & e) {
    if (is_lambda(e)) {
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_free_var(app_fn(new_b), 0)) {
                return lower_free_vars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_free_var(app_fn(b), 0)) {
            return lower_free_vars(app_fn(b), 1);
        } else {
            return e;
        }
    } else {
        return e;
    }
}

template<bool Eta, bool Beta>
class eta_beta_reduce_fn : public replace_visitor {
public:
    virtual expr visit_app(expr const & e) override {
        expr e1 = replace_visitor::visit_app(e);
        if (Beta && is_head_beta(e1)) {
            return visit(head_beta_reduce(e1));
        } else {
            return e1;
        }
    }

    virtual expr visit_lambda(expr const & e) override {
        expr e1 = replace_visitor::visit_lambda(e);
        if (Eta) {
            while (true) {
                expr e2 = try_eta(e1);
                if (is_eqp(e1, e2))
                    return e1;
                else
                    e1 = e2;
            }
        } else {
            return e1;
        }
    }
};

expr beta_reduce(expr t) {
    return eta_beta_reduce_fn<false, true>()(t);
}

expr eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, false>()(t);
}

expr beta_eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, true>()(t);
}

expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k) {
    switch (k) {
    case implicit_infer_kind::Implicit: {
        bool strict = true;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::RelaxedImplicit: {
        bool strict = false;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::None:
        return type;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool get_constructor_rec_args(environment const & env, expr const & e, buffer<pair<expr, unsigned>> & rec_args) {
    type_checker ctx(env);
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn)) return false;
    optional<name> I_name = inductive::is_intro_rule(env, const_name(fn));
    if (!I_name) return false;
    expr type       = env.get(const_name(fn)).get_type();
    buffer<expr> tele;
    to_telescope(ctx, type, tele);
    if (tele.size() != args.size()) return false;
    for (unsigned i = 0; i < tele.size(); i++) {
        expr d = tele[i];
        buffer<expr> tele_tele;
        expr r  = to_telescope(ctx, mlocal_type(d), tele_tele);
        expr fn = get_app_fn(r);
        if (is_constant(fn, *I_name)) {
            rec_args.push_back(mk_pair(args[i], tele_tele.size()));
        }
    }
    return true;
}

static expr * g_bool = nullptr;
static expr * g_bool_tt = nullptr;
static expr * g_bool_ff = nullptr;

void initialize_bool() {
    g_bool = new expr(mk_constant(get_bool_name()));
    g_bool_ff = new expr(mk_constant(get_bool_ff_name()));
    g_bool_tt = new expr(mk_constant(get_bool_tt_name()));
}

void finalize_bool() {
    delete g_bool;
    delete g_bool_ff;
    delete g_bool_tt;
}

expr mk_bool() { return *g_bool; }
expr mk_bool_tt() { return *g_bool_tt; }
expr mk_bool_ff() { return *g_bool_ff; }
expr to_bool_expr(bool b) { return b ? mk_bool_tt() : mk_bool_ff(); }

name get_dep_recursor(environment const & env, name const & n) {
    if (is_inductive_predicate(env, n))
        return name(n, "drec");
    else
        return name(n, "rec");
}

name get_dep_cases_on(environment const & env, name const & n) {
    if (is_inductive_predicate(env, n))
        return name(n, "dcases_on");
    else
        return name(n, "cases_on");
}

static char const * g_aux_meta_rec_prefix = "_meta_aux";

name mk_aux_meta_rec_name(name const & n) {
    return name(n, g_aux_meta_rec_prefix);
}

optional<name> is_aux_meta_rec_name(name const & n) {
    if (!n.is_atomic() && n.is_string() && strcmp(n.get_string(), g_aux_meta_rec_prefix) == 0) {
        return optional<name>(n.get_prefix());
    } else {
        return optional<name>();
    }
}

optional<name> name_lit_to_name(expr const & name_lit) {
    if (is_constant(name_lit, get_name_anonymous_name()))
        return optional<name>(name());
    if (is_app_of(name_lit, get_name_mk_string_name(), 2)) {
        if (auto str = to_string(app_arg(app_fn(name_lit))))
        if (auto p   = name_lit_to_name(app_arg(name_lit)))
            return optional<name>(name(*p, str->c_str()));
    }
    return optional<name>();
}

static expr * g_tactic_unit = nullptr;

expr mk_tactic_unit() {
    return *g_tactic_unit;
}

static std::string * g_version_string = nullptr;
std::string const & get_version_string() { return *g_version_string; }

void initialize_library_util() {
    g_true           = new expr(mk_constant(get_true_name()));
    g_true_intro     = new expr(mk_constant(get_true_intro_name()));
    g_and            = new expr(mk_constant(get_and_name()));
    g_and_intro      = new expr(mk_constant(get_and_intro_name()));
    g_and_elim_left  = new expr(mk_constant(get_and_elim_left_name()));
    g_and_elim_right = new expr(mk_constant(get_and_elim_right_name()));
    g_tactic_unit    = new expr(mk_app(mk_constant(get_tactic_name(), {mk_level_zero()}), mk_constant(get_unit_name())));
    initialize_nat();
    initialize_int();
    initialize_char();
    initialize_bool();

    sstream out;

    out << LEAN_VERSION_MAJOR << "."
        << LEAN_VERSION_MINOR << "." << LEAN_VERSION_PATCH;
    if (std::strlen(LEAN_SPECIAL_VERSION_DESC) > 0) {
        out << ", " << LEAN_SPECIAL_VERSION_DESC;
    }
    if (std::strcmp(LEAN_GITHASH, "GITDIR-NOTFOUND") == 0) {
        if (std::strcmp(LEAN_PACKAGE_VERSION, "NOT-FOUND") != 0) {
            out << ", package " << LEAN_PACKAGE_VERSION;
        }
    } else {
        out << ", commit " << std::string(LEAN_GITHASH).substr(0, 12);
    }
    g_version_string = new std::string(out.str());
}

void finalize_library_util() {
    delete g_version_string;
    finalize_bool();
    finalize_int();
    finalize_nat();
    finalize_char();
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_elim_left;
    delete g_and_elim_right;
    delete g_tactic_unit;
}
}




// ========== documentation.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
class doc_entry {
    optional<name> m_decl_name;
    std::string    m_doc;
public:
    doc_entry(std::string const & doc):m_doc(doc) {}
    doc_entry(name const & decl_name, std::string const & doc):m_decl_name(decl_name), m_doc(doc) {}
    optional<name> const & get_decl_name() const { return m_decl_name; }
    std::string const & get_doc() const { return m_doc; }
};
environment add_module_doc_string(environment const & env, std::string doc);
environment add_doc_string(environment const & env, name const & n, std::string);
optional<std::string> get_doc_string(environment const & env, name const & n);
void get_module_doc_strings(environment const & env, buffer<doc_entry> & result);
void initialize_documentation();
void finalize_documentation();
}




// ========== documentation.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include <functional>
#include <cctype>
#include "util/sstream.h"
#include "library/module.h"
#include "library/documentation.h"

namespace lean {
struct documentation_ext : public environment_extension {
    /** Doc string for the current module being processed. It does not include imported doc strings. */
    list<doc_entry>       m_module_doc;
    /** Doc strings for declarations (including imported ones). We store doc_strings for declarations in the .olean files. */
    name_map<std::string> m_doc_string_map;
};

struct documentation_ext_reg {
    unsigned m_ext_id;
    documentation_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<documentation_ext>()); }
};

static documentation_ext_reg * g_ext = nullptr;
static documentation_ext const & get_extension(environment const & env) {
    return static_cast<documentation_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, documentation_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<documentation_ext>(ext));
}

struct doc_modification : public modification {
    LEAN_MODIFICATION("doc")

    name m_decl;
    std::string m_doc;

    doc_modification() {}
    doc_modification(name const & decl, std::string const & doc) : m_decl(decl), m_doc(doc) {}

    void perform(environment & env) const override {
        auto ext = get_extension(env);
        ext.m_doc_string_map.insert(m_decl, m_doc);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl << m_doc;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name decl; std::string doc;
        d >> decl >> doc;
        return std::make_shared<doc_modification>(decl, doc);
    }
};

static void remove_blank_lines_begin(std::string & s) {
    optional<std::string::iterator> found;
    for (auto it = s.begin(); it != s.end(); it++) {
        if (*it == '\n') {
            found = it + 1;
        } else if (!isspace(*it)) {
            break;
        }
    }
    if (found)
        s.erase(s.begin(), *found);
}

static void rtrim(std::string & s) {
    s.erase(std::find_if(s.rbegin(), s.rend(),
                         std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
}

static unsigned get_indentation(std::string const & s) {
    bool r_init = false;
    unsigned r  = 0;
    bool searching = true;
    unsigned i = 0;
    for (auto it = (const unsigned char*)s.data(), e = (const unsigned char*)s.data() + s.size(); it != e; ++it) {
        if (*it == '\n') {
            i = 0;
            searching = true;
        } else if (isspace(*it) && searching) {
            i++;
        } else if (searching) {
            searching = false;
            if (r_init) {
                r = std::min(r, i);
            } else {
                r      = i;
                r_init = true;
            }
        }
    }
    return r;
}

static std::string unindent(std::string const & s) {
    unsigned i = get_indentation(s);
    if (i > 0) {
        std::string r;
        unsigned j = 0;
        for (auto it = s.begin(); it != s.end(); it++) {
            if (*it == '\n') {
                j = 0;
                r += *it;
            } else if (j < i) {
                j++;
            } else {
                r += *it;
            }
        }
        return r;
    } else {
        return s;
    }
}

static std::string add_lean_suffix_to_code_blocks(std::string const & s) {
    std::string r;
    unsigned sz = s.size();
    unsigned i = 0;
    bool in_block = false;
    while (i < sz) {
        if (!in_block && s[i] == '`' && sz >= 4 && i < sz - 3 && s[i+1] == '`' && s[i+2] == '`' && isspace(s[i+3])) {
            r += "```lean";
            r += s[i+3];
            i += 4;
            in_block = true;
        } else if (in_block && s[i] == '`' && sz >= 3 && i < sz - 2 && s[i+1] == '`' && s[i+2] == '`') {
            r += "```";
            i += 3;
            in_block = false;
        } else {
            r += s[i];
            i++;
        }
    }
    if (in_block) {
        throw exception("invalid doc string, end of code block ``` expected");
    }
    return r;
}

static std::string process_doc(std::string s) {
    remove_blank_lines_begin(s);
    rtrim(s);
    s = unindent(s);
    return add_lean_suffix_to_code_blocks(s);
}

environment add_module_doc_string(environment const & env, std::string doc) {
    doc = process_doc(doc);
    auto ext = get_extension(env);
    ext.m_module_doc = cons(doc_entry(doc), ext.m_module_doc);
    return update(env, ext);
}

environment add_doc_string(environment const & env, name const & n, std::string doc) {
    doc = process_doc(doc);
    auto ext = get_extension(env);
    if (ext.m_doc_string_map.contains(n)) {
        throw exception(sstream() << "environment already contains a doc string for '" << n << "'");
    }
    ext.m_doc_string_map.insert(n, doc);
    ext.m_module_doc = cons(doc_entry(n, doc), ext.m_module_doc);
    auto new_env = update(env, ext);
    // TODO(gabriel,leo): why does this not update the module documentation?
    return module::add(new_env, std::make_shared<doc_modification>(n, doc));
}

optional<std::string> get_doc_string(environment const & env, name const & n) {
    auto ext = get_extension(env);
    if (auto r = ext.m_doc_string_map.find(n))
        return optional<std::string>(*r);
    else
        return optional<std::string>();
}

void get_module_doc_strings(environment const & env, buffer<doc_entry> & result) {
    auto ext = get_extension(env);
    to_buffer(ext.m_module_doc, result);
    std::reverse(result.begin(), result.end());
}

void initialize_documentation() {
    g_ext     = new documentation_ext_reg();
    doc_modification::init();
}

void finalize_documentation() {
    doc_modification::finalize();
    delete g_ext;
}
}




// ========== replace_visitor.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr_maps.h"

namespace lean {
/**
   \brief Base class for implementing operations that apply modifications
   on expressions.
   The default behavior is a NOOP, users must create subclasses and
   redefine the visit_* methods. */
class replace_visitor {
protected:
    typedef expr_bi_map<expr> cache;
    cache   m_cache;
    expr save_result(expr const & e, expr && r, bool shared);
    virtual expr visit_sort(expr const &);
    virtual expr visit_macro(expr const &);
    virtual expr visit_constant(expr const &);
    virtual expr visit_var(expr const &);
    virtual expr visit_mlocal(expr const &);
    virtual expr visit_meta(expr const &);
    virtual expr visit_local(expr const &);
    virtual expr visit_app(expr const &);
    virtual expr visit_binding(expr const &);
    virtual expr visit_lambda(expr const &);
    virtual expr visit_pi(expr const &);
    virtual expr visit_let(expr const & e);
    virtual expr visit(expr const &);
public:
    expr operator()(expr const & e) { return visit(e); }
    void clear() { m_cache.clear(); }
};
}




// ========== replace_visitor.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include "util/interrupt.h"
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/replace_visitor.h"

namespace lean {
expr replace_visitor::visit_sort(expr const & e) { lean_assert(is_sort(e)); return e; }
expr replace_visitor::visit_var(expr const & e) { lean_assert(is_var(e)); return e; }
expr replace_visitor::visit_constant(expr const & e) { lean_assert(is_constant(e)); return e; }
expr replace_visitor::visit_mlocal(expr const & e) {
    lean_assert(is_mlocal(e));
    return update_mlocal(e, visit(mlocal_type(e)));
}
expr replace_visitor::visit_meta(expr const & e) { return visit_mlocal(e); }
expr replace_visitor::visit_local(expr const & e) { return visit_mlocal(e); }
expr replace_visitor::visit_app(expr const & e) {
    lean_assert(is_app(e));
    expr new_fn  = visit(app_fn(e));
    expr new_arg = visit(app_arg(e));
    return update_app(e, new_fn, new_arg);
}
expr replace_visitor::visit_binding(expr const & e) {
    lean_assert(is_binding(e));
    expr new_d = visit(binding_domain(e));
    expr new_b = visit(binding_body(e));
    return update_binding(e, new_d, new_b);
}
expr replace_visitor::visit_lambda(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_pi(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_let(expr const & e) {
    lean_assert(is_let(e));
    expr new_t = visit(let_type(e));
    expr new_v = visit(let_value(e));
    expr new_b = visit(let_body(e));
    return update_let(e, new_t, new_v, new_b);
}
expr replace_visitor::visit_macro(expr const & e) {
    lean_assert(is_macro(e));
    buffer<expr> new_args;
    for (unsigned i = 0; i < macro_num_args(e); i++)
        new_args.push_back(visit(macro_arg(e, i)));
    return update_macro(e, new_args.size(), new_args.data());
}
expr replace_visitor::save_result(expr const & e, expr && r, bool shared) {
    if (shared)
        m_cache.insert(std::make_pair(e, r));
    return r;
}
expr replace_visitor::visit(expr const & e) {
    check_system("expression replacer");
    bool shared = false;
    if (is_shared(e)) {
        shared = true;
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
    }

    switch (e.kind()) {
    case expr_kind::Sort:      return save_result(e, visit_sort(e), shared);
    case expr_kind::Macro:     return save_result(e, visit_macro(e), shared);
    case expr_kind::Constant:  return save_result(e, visit_constant(e), shared);
    case expr_kind::Var:       return save_result(e, visit_var(e), shared);
    case expr_kind::Meta:      return save_result(e, visit_meta(e), shared);
    case expr_kind::Local:     return save_result(e, visit_local(e), shared);
    case expr_kind::App:       return save_result(e, visit_app(e), shared);
    case expr_kind::Lambda:    return save_result(e, visit_lambda(e), shared);
    case expr_kind::Pi:        return save_result(e, visit_pi(e), shared);
    case expr_kind::Let:       return save_result(e, visit_let(e), shared);
    }

    lean_unreachable(); // LCOV_EXCL_LINE
}
}




// ========== messages.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include "util/log_tree.h"
#include "util/message_definitions.h"
#include "util/parser_exception.h"

namespace lean {

enum message_severity { INFORMATION, WARNING, ERROR };

class message : public log_entry_cell {
    std::string        m_file_name;
    pos_info           m_pos;
    optional<pos_info> m_end_pos;
    message_severity   m_severity;
    std::string        m_caption, m_text;
public:
    message(std::string const & file_name, pos_info const & pos, optional<pos_info> const & end_pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        m_file_name(file_name), m_pos(pos), m_end_pos(end_pos),
        m_severity(severity), m_caption(caption), m_text(text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        m_file_name(file_name), m_pos(pos),
        m_severity(severity), m_caption(caption), m_text(text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & text) :
        message(file_name, pos, severity, std::string(), text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity) :
        message(file_name, pos, severity, std::string()) {}
    message(parser_exception const & ex);

    std::string get_file_name() const { return m_file_name; }
    pos_info get_pos() const { return m_pos; }
    optional<pos_info> get_end_pos() const { return m_end_pos; }
    message_severity get_severity() const { return m_severity; }
    std::string get_caption() const { return m_caption; }
    std::string get_text() const { return m_text; }
    location get_location() const { return {m_file_name, {m_pos, m_pos}}; }

    bool is_error() const { return m_severity >= ERROR; }
};

std::ostream & operator<<(std::ostream &, message const &);
void report_message(message const &);

bool is_error_message(log_entry const &);
task<bool> has_errors(log_tree::node const &);

}




// ========== messages.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/messages.h"
#include "frontends/lean/info_manager.h"
#include "util/task_builder.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), *ex.get_pos(),
                ERROR, ex.get_msg()) {}

std::ostream & operator<<(std::ostream & out, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        out << msg.get_file_name() << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: out << "warning: "; break;
            case ERROR:   out << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            out << msg.get_caption() << ":\n";
    }
    auto const & text = msg.get_text();
    out << text;
    if (!text.size() || text[text.size() - 1] != '\n')
        out << "\n";
    return out;
}

void report_message(message const & msg0) {
    auto & l = logtree();
    auto & loc = logtree().get_location();

    std::shared_ptr<message> msg;
    if (loc.m_file_name.empty()) {
        msg = std::make_shared<message>(msg0);
    } else {
        auto pos_ok = loc.m_range.m_begin <= msg0.get_pos() && msg0.get_pos() <= loc.m_range.m_end;
        msg = std::make_shared<message>(loc.m_file_name,
                                        pos_ok ? msg0.get_pos() : loc.m_range.m_begin,
                                        pos_ok ? msg0.get_end_pos() : optional<pos_info>(),
                                        msg0.get_severity(), msg0.get_caption(), msg0.get_text());
    }
    l.add(msg);
}

task<bool> has_errors(log_tree::node const & n) {
    return n.has_entry(is_error_message);
}

bool is_error_message(log_entry const & e) {
    if (auto msg = dynamic_cast<message const *>(e.get())) {
        return msg->is_error();
    }
    return false;
}

}




// ========== typed_expr.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
class expr;
/** \brief Create an expression definitionally equal to \c e, but it must have type \c t. */
expr mk_typed_expr(expr const & t, expr const & e);
/** \brief Return true iff \c e was created using #mk_typed_expr */
bool is_typed_expr(expr const & e);
/** \brief Return the type of a typed expression

    \remark get_typed_expr_type(mk_typed_expr(t, e)) == t
*/
expr get_typed_expr_type(expr const & e);
/** \brief Return the expression/denotation of a typed expression

    \remark get_typed_expr_type(mk_typed_expr(t, e)) == e
*/
expr get_typed_expr_expr(expr const & e);

void initialize_typed_expr();
void finalize_typed_expr();
}




// ========== typed_expr.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract_type_context.h"
#include "library/util.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_typed_expr_name = nullptr;
static std::string * g_typed_expr_opcode = nullptr;
static macro_definition * g_typed_expr = nullptr;

name const & get_typed_expr_name() { return *g_typed_expr_name; }
std::string const & get_typed_expr_opcode() { return *g_typed_expr_opcode; }

/** \brief This macro is used to "enforce" a given type to an expression.
    It is equivalent to

        definition typed_expr (A : Type) (a : A) := a

    We use a macro instead of the definition because we want to be able
    to use in any environment, even one that does not contain the
    definition such as typed_expr.

    The macro is also slightly for efficient because we don't need a
    universe parameter.
*/
class typed_expr_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid typed-expr, incorrect number of arguments");
    }
public:
    virtual name get_name() const { return get_typed_expr_name(); }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        check_macro(m);
        expr given_type = macro_arg(m, 0);
        if (!infer_only) {
            ctx.check(given_type, infer_only);
            expr inferred_type = ctx.check(macro_arg(m, 1), infer_only);
            if (!ctx.is_def_eq(inferred_type, given_type)) {
                throw_kernel_exception(ctx.env(), m, [=](formatter const & fmt) {
                    return format("type mismatch at term") + pp_type_mismatch(fmt, macro_arg(m, 1), inferred_type, given_type);
                });
            }
        }
        return given_type;
    }
    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 1));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_typed_expr_opcode());
    }
};

bool is_typed_expr(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_typed_expr;
}

expr mk_typed_expr(expr const & t, expr const & v) {
    expr args[2] = {t, v};
    return mk_macro(*g_typed_expr, 2, args);
}

expr get_typed_expr_type(expr const & e) { lean_assert(is_typed_expr(e)); return macro_arg(e, 0); }
expr get_typed_expr_expr(expr const & e) { lean_assert(is_typed_expr(e)); return macro_arg(e, 1); }

void initialize_typed_expr() {
    g_typed_expr_name = new name("typed_expr");
    g_typed_expr_opcode = new std::string("TyE");
    g_typed_expr = new macro_definition(new typed_expr_macro_definition_cell());
    register_macro_deserializer(*g_typed_expr_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_typed_expr(args[0], args[1]);
                                });
}

void finalize_typed_expr() {
    delete g_typed_expr;
    delete g_typed_expr_opcode;
    delete g_typed_expr_name;
}
}




// ========== export.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
void export_as_lowtext(std::ostream & out, environment const & env,
    optional<list<name>> const & decls);
void export_all_as_lowtext(std::ostream & out, environment const & env) {
    return export_as_lowtext(out, env, {});
}
}




// ========== export.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "frontends/lean/parser_config.h"
#include "kernel/quotient/quotient.h"
#include "kernel/expr_maps.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/unfold_macros.h"

namespace lean {
template<typename T>
using level_map = typename std::unordered_map<level, T, level_hash, level_eq>;

template<typename T>
using name_hmap = typename std::unordered_map<name, T, name_hash, name_eq>;


class exporter {
    std::ostream &               m_out;
    environment                  m_env;
    std::unordered_set<name, name_hash> m_exported;
    name_hmap<unsigned>          m_name2idx;
    level_map<unsigned>          m_level2idx;
    expr_bi_map<unsigned>        m_expr2idx;
    bool                         m_quotient_exported = false;

    unsigned export_name(name const & n) {
        auto it = m_name2idx.find(n);
        if (it != m_name2idx.end())
            return it->second;
        unsigned i;
        if (n.is_anonymous()) {
            lean_unreachable();
        } else if (n.is_string()) {
            unsigned p = export_name(n.get_prefix());
            i = static_cast<unsigned>(m_name2idx.size());
            m_out << i << " #NS " << p << " " << n.get_string() << "\n";
        } else {
            unsigned p = export_name(n.get_prefix());
            i = static_cast<unsigned>(m_name2idx.size());
            m_out << i << " #NI " << p << " " << n.get_numeral() << "\n";
        }
        m_name2idx[n] = i;
        return i;
    }

    unsigned export_level(level const & l) {
        auto it = m_level2idx.find(l);
        if (it != m_level2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l1, l2, n;
        switch (l.kind()) {
        case level_kind::Zero:
            lean_unreachable();
            break;
        case level_kind::Succ:
            l1 = export_level(succ_of(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #US " << l1 << "\n";
            break;
        case level_kind::Max:
            l1 = export_level(max_lhs(l));
            l2 = export_level(max_rhs(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::IMax:
            l1 = export_level(imax_lhs(l));
            l2 = export_level(imax_rhs(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UIM " << l1 << " " << l2 << "\n";
            break;
        case level_kind::Param:
            n = export_name(param_id(l));
            i = static_cast<unsigned>(m_level2idx.size());
            m_out << i << " #UP " << n << "\n";
            break;
        case level_kind::Meta:
            throw exception("invalid 'export', universe meta-variables cannot be exported");
        }
        m_level2idx[l] = i;
        return i;
    }

    void display_binder_info(binder_info const & bi) {
        if (bi.is_implicit())
            m_out << "#BI";
        else if (bi.is_strict_implicit())
            m_out << "#BS";
        else if (bi.is_inst_implicit())
            m_out << "#BC";
        else
            m_out << "#BD";
    }

    unsigned export_binding(expr const & e, char const * k) {
        unsigned n  = export_name(binding_name(e));
        unsigned e1 = export_expr(binding_domain(e));
        unsigned e2 = export_expr(binding_body(e));
        unsigned i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " " << k << " ";
        display_binder_info(binding_info(e));
        m_out << " " << n << " " << e1 << " " << e2 << "\n";
        return i;
    }

    unsigned export_const(expr const & e) {
        buffer<unsigned> ls;
        unsigned n = export_name(const_name(e));
        for (level const & l : const_levels(e))
            ls.push_back(export_level(l));
        unsigned i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #EC " << n;
        for (unsigned l : ls)
            m_out << " " << l;
        m_out << "\n";
        return i;
    }

    unsigned export_expr(expr const & e) {
        auto it = m_expr2idx.find(e);
        if (it != m_expr2idx.end())
            return it->second;
        unsigned i = 0;
        unsigned l, e1, e2;
        switch (e.kind()) {
        case expr_kind::Var:
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EV " << var_idx(e) << "\n";
            break;
        case expr_kind::Sort:
            l = export_level(sort_level(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #ES " << l << "\n";
            break;
        case expr_kind::Constant:
            i = export_const(e);
            break;
        case expr_kind::App:
            e1 = export_expr(app_fn(e));
            e2 = export_expr(app_arg(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EA " << e1 << " " << e2 << "\n";
            break;
        case expr_kind::Let: {
            auto n = export_name(let_name(e));
            e1 = export_expr(let_type(e));
            e2 = export_expr(let_value(e));
            auto e3 = export_expr(let_body(e));
            i = static_cast<unsigned>(m_expr2idx.size());
            m_out << i << " #EZ " << n << " " << e1 << " " << e2 << " " << e3 << "\n";
            break;
        }
        case expr_kind::Lambda:
            i = export_binding(e, "#EL");
            break;
        case expr_kind::Pi:
            i = export_binding(e, "#EP");
            break;
        case expr_kind::Meta:
            throw exception("invalid 'export', meta-variables cannot be exported");
        case expr_kind::Local:
            throw exception("invalid 'export', local constants cannot be exported");
        case expr_kind::Macro:
            throw exception("invalid 'export', macros cannot be exported");
        }
        m_expr2idx[e] = i;
        return i;
    }

    void export_dependencies(expr const & e) {
        for_each(e, [&](expr const & c, unsigned) {
                if (is_constant(c))
                    export_declaration(const_name(c));
                return true;
            });
    }

    void export_definition(declaration const & d) {
        unsigned n = export_name(d.get_name());
        export_dependencies(d.get_type());
        export_dependencies(d.get_value());
        auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
        auto t = export_expr(d.get_type());
        auto v = export_expr(d.get_value());
        m_out << "#DEF " << n << " " << t << " " << v;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << "\n";
    }

    void export_axiom(declaration const & d) {
        unsigned n = export_name(d.get_name());
        export_dependencies(d.get_type());
        auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
        auto t = export_expr(d.get_type());
        m_out << "#AX " << n << " " << t;
        for (unsigned p : ps)
            m_out << " " << p;
        m_out << "\n";
    }

    void export_declaration(name const & n) {
        if (!m_exported.count(n))
            export_declaration(m_env.get(n));
    }

    void export_declaration(declaration d) {
        // do not export meta declarations
        if (!d.is_trusted()) return;

        if (is_quotient_decl(m_env, d.get_name()))
            return export_quotient();
        if (inductive::is_inductive_decl(m_env, d.get_name()))
            return export_inductive(d.get_name());
        if (auto ind_type = inductive::is_intro_rule(m_env, d.get_name()))
            return export_inductive(*ind_type);
        if (auto ind_type = inductive::is_elim_rule(m_env, d.get_name()))
            return export_inductive(*ind_type);

        if (m_exported.count(d.get_name())) return;
        m_exported.insert(d.get_name());

        d = unfold_all_macros(m_env, d);

        if (d.is_definition()) {
            return export_definition(d);
        } else {
            return export_axiom(d);
        }
    }

    void export_inductive(name const & n) {
        if (m_exported.count(n)) return;
        m_exported.insert(n);

        auto decl = *inductive::is_inductive_decl(m_env, n);
        decl.m_type = unfold_all_macros(m_env, decl.m_type);
        decl.m_intro_rules = map(decl.m_intro_rules,
                                 [&] (inductive::intro_rule const & i) {
                                     return unfold_all_macros(m_env, i);
                                 });

        export_dependencies(decl.m_type);
        for (auto & c : decl.m_intro_rules)
            export_dependencies(c);

        for (auto & p : decl.m_level_params)
            export_name(p);
        export_name(decl.m_name);
        export_expr(decl.m_type);
        for (auto & c : decl.m_intro_rules) {
            export_name(inductive::intro_rule_name(c));
            export_expr(inductive::intro_rule_type(c));
        }

        m_out << "#IND " << decl.m_num_params << " "
              << export_name(decl.m_name) << " "
              << export_expr(decl.m_type) << " "
              << length(decl.m_intro_rules);
        for (auto & c : decl.m_intro_rules) {
            // intro rules are stored as local constants, we split them up so that
            // the type checkers do not need to implement local constants.
            m_out << " " << export_name(inductive::intro_rule_name(c))
                  << " " << export_expr(inductive::intro_rule_type(c));
        }
        for (name const & p : decl.m_level_params)
            m_out << " " << export_name(p);
        m_out << "\n";
    }

    void export_declarations() {
        m_env.for_each_declaration([&] (declaration const & d) {
                export_declaration(d);
            });
    }

    void export_quotient() {
        if (m_quotient_exported) return;
        m_quotient_exported = true;

        for (auto & n : quotient_required_decls())
            export_declaration(n);

        m_out << "#QUOT\n";
    }

    void export_notation(notation_entry const & entry) {
        if (entry.parse_only()) return;
        if (length(entry.get_transitions()) != 1) return;
        auto & t = head(entry.get_transitions());

        buffer<expr> args;
        auto & fn = get_app_rev_args(entry.get_expr(), args);

        char const * type = nullptr;
        if (args.size() == 1 && args[0] == mk_var(0)) {
            if (entry.is_nud()) {
                type = "#PREFIX";
            } else {
                type = "#POSTFIX";
            }
        } else if (!entry.is_nud() && args.size() == 2 && args[0] == mk_var(0) && args[1] == mk_var(1)) {
            type = "#INFIX";
        }

        if (type && is_constant(fn)) {
            auto fni = export_name(const_name(fn));
            auto prec_opt = get_expr_precedence(get_token_table(m_env), t.get_token().get_string());
            auto prec = prec_opt ? *prec_opt : 0;
            m_out << type << " " << fni << " " << prec << " " << t.get_pp_token().get_string() << "\n";
        }
    }

    void export_notation() {
        for (auto & entry : get_notation_entries(m_env)) {
            export_notation(entry);
        }
    }

public:
    exporter(std::ostream & out, environment const & env) : m_out(out), m_env(env) {}

    void operator()(optional<list<name>> const & decls) {
        m_name2idx[{}] = 0;
        m_level2idx[{}] = 0;
        if (has_quotient(m_env))
            export_quotient();
        if (decls) {
            for (auto & d : *decls)
                export_declaration(d);
        } else {
            export_declarations();
        }
        export_notation();
    }
};

void export_as_lowtext(std::ostream & out, environment const & env,
        optional<list<name>> const & decls) {
    exporter(out, env)(decls);
}
}




// ========== process.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>
#include <unordered_map>
#include "library/handle.h"
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean  {

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

struct child {
    virtual ~child() {};
    virtual handle_ref get_stdin() = 0;
    virtual handle_ref get_stdout() = 0;
    virtual handle_ref get_stderr() = 0;
    virtual unsigned wait() = 0;
};

class process {
    std::string m_proc_name;
    buffer<std::string> m_args;
    stdio m_stdout;
    stdio m_stdin;
    stdio m_stderr;
    optional<std::string> m_cwd;
    std::unordered_map<std::string, optional<std::string>> m_env;
    std::shared_ptr<child> spawn_core();
public:
    process(process const & proc) = default;
    process(std::string exe_name, stdio io_stdin, stdio io_stdout, stdio io_stderr);
    process & arg(std::string arg_str);
    process & set_cwd(std::string const & cwd);
    process & set_env(std::string const & var, optional<std::string> const & val);
    std::shared_ptr<child> spawn();
};
}




// ========== process.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#include <Fcntl.h>
#include <io.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>
#else
#include <unistd.h>
#include <sys/wait.h>
#endif

#include "library/process.h"
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean {

process::process(std::string n, stdio io_stdin, stdio io_stdout, stdio io_stderr):
    m_proc_name(n), m_stdout(io_stdout), m_stdin(io_stdin), m_stderr(io_stderr) {
    m_args.push_back(m_proc_name);
}

process & process::arg(std::string a) {
    m_args.push_back(a);
    return *this;
}

process & process::set_cwd(std::string const &cwd) {
    m_cwd = cwd;
    return *this;
}

process & process::set_env(std::string const & var, optional<std::string> const & val) {
    m_env[var] = val;
    return *this;
}

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)

struct windows_child : public child {
    handle_ref m_stdin;
    handle_ref m_stdout;
    handle_ref m_stderr;
    HANDLE m_process;

    windows_child(HANDLE p, handle_ref hstdin, handle_ref hstdout, handle_ref hstderr) :
            m_stdin(hstdin), m_stdout(hstdout), m_stderr(hstderr), m_process(p) {}

    ~windows_child() {
        CloseHandle(m_process);
    }

    handle_ref get_stdin() override { return m_stdin; }
    handle_ref get_stdout() override { return m_stdout; }
    handle_ref get_stderr() override { return m_stderr; }

    unsigned wait() override {
        DWORD exit_code;
        WaitForSingleObject(m_process, INFINITE);
        GetExitCodeProcess(m_process, &exit_code);
        return static_cast<unsigned>(exit_code);
    }
};

// static HANDLE to_win_handle(FILE * file) {
//     intptr_t handle = _get_osfhandle(fileno(file));
//     return reinterpret_cast<HANDLE>(handle);
// }

static FILE * from_win_handle(HANDLE handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle), _O_APPEND);
    return fdopen(fd, mode);
}

static HANDLE create_child_process(std::string cmd_name, optional<std::string> const & cwd,
    std::unordered_map<std::string, optional<std::string>> const & env,
    HANDLE hstdin, HANDLE hstdout, HANDLE hstderr);

// TODO(@jroesch): unify this code between platforms better.
static optional<pipe> setup_stdio(SECURITY_ATTRIBUTES * saAttr, HANDLE * handle, bool in, stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        lean_always_assert(DuplicateHandle(GetCurrentProcess(), *handle,
                                           GetCurrentProcess(), handle,
                                           0, TRUE, DUPLICATE_SAME_ACCESS));
        return optional<pipe>();
    case stdio::PIPED: {
        HANDLE readh;
        HANDLE writeh;
        if (!CreatePipe(&readh, &writeh, saAttr, 0))
            throw new exception("unable to create pipe");
        auto pipe = lean::pipe(readh, writeh);
        auto ours = in ? pipe.m_write_fd : pipe.m_read_fd;
        auto theirs = in ? pipe.m_read_fd : pipe.m_write_fd;
        lean_always_assert(SetHandleInformation(ours, HANDLE_FLAG_INHERIT, 0));
        *handle = theirs;
        return optional<lean::pipe>(pipe);
    }
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

// This code is adapted from: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682499(v=vs.85).aspx
std::shared_ptr<child> process::spawn_core() {
    HANDLE child_stdin = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE child_stdout = GetStdHandle(STD_OUTPUT_HANDLE);
    HANDLE child_stderr = GetStdHandle(STD_ERROR_HANDLE);

    SECURITY_ATTRIBUTES saAttr;

    // Set the bInheritHandle flag so pipe handles are inherited.
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    auto stdin_pipe = setup_stdio(&saAttr, &child_stdin, true, m_stdin);
    auto stdout_pipe = setup_stdio(&saAttr, &child_stdout, false, m_stdout);
    auto stderr_pipe = setup_stdio(&saAttr, &child_stderr, false, m_stderr);

    std::string command;

    // This needs some thought, on Windows we must pass a command string
    // which is a valid command, that is a fully assembled command to be executed.
    //
    // We must escape the arguments to preseving spacing and other characters,
    // we might need to revisit escaping here.
    bool once_through = false;
    for (auto arg : m_args) {
        if (once_through) {
            command += " \"";
        }
        command += arg;
        if (once_through) {
            command += "\"";
        }
        once_through = true;
    }

    // Create the child process.
    auto proc_handle =
        create_child_process(command, m_cwd, m_env, child_stdin, child_stdout, child_stderr);

    FILE * parent_stdin = nullptr, *parent_stdout = nullptr, *parent_stderr = nullptr;

    if (stdin_pipe) {
        CloseHandle(stdin_pipe->m_read_fd);
        parent_stdin = from_win_handle(stdin_pipe->m_write_fd, "w");
    }

    if (stdout_pipe) {
        CloseHandle(stdout_pipe->m_write_fd);
        parent_stdout = from_win_handle(stdout_pipe->m_read_fd, "r");
    }

    if (stderr_pipe) {
        CloseHandle(stderr_pipe->m_write_fd);
        parent_stderr = from_win_handle(stderr_pipe->m_read_fd, "r");
    }

    return std::make_shared<windows_child>(proc_handle,
        std::make_shared<handle>(parent_stdin, false),
        std::make_shared<handle>(parent_stdout, false),
        std::make_shared<handle>(parent_stderr, false));
}

static void set_env(std::string const & var, optional<std::string> const & val) {
    SetEnvironmentVariable(var.c_str(), val ? val->c_str() : NULL);
}

// Create a child process that uses the previously created pipes for STDIN and STDOUT.
static HANDLE create_child_process(std::string command, optional<std::string> const & cwd,
        std::unordered_map<std::string, optional<std::string>> const & env,
        HANDLE hstdin, HANDLE hstdout, HANDLE hstderr) {
    PROCESS_INFORMATION piProcInfo;
    STARTUPINFO siStartInfo;
    BOOL bSuccess = FALSE;

    // Set up members of the PROCESS_INFORMATION structure.
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // Set up members of the STARTUPINFO structure.
    // This structure specifies the STDIN and STDOUT handles for redirection.

    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
    siStartInfo.cb = sizeof(STARTUPINFO);
    siStartInfo.hStdError = hstderr;
    siStartInfo.hStdOutput = hstdout;
    siStartInfo.hStdInput = hstdin;
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

    // TODO(gabriel): this is thread-unsafe
    std::unordered_map<std::string, optional<std::string>> old_env_vars;
    for (auto & entry : env) {
        optional<std::string> old;
        if (auto old_val = getenv(entry.first.c_str()))
            old = std::string(old_val);
        old_env_vars[entry.first] = old;

        set_env(entry.first, entry.second);
    }

    // Create the child process.
    // std::cout << command << std::endl;
    bSuccess = CreateProcess(
        NULL,
        const_cast<char *>(command.c_str()), // command line
        NULL,                                // process security attributes
        NULL,                                // primary thread security attributes
        TRUE,                                // handles are inherited
        0,                                   // creation flags
        NULL,                                // use parent's environment
        cwd ? cwd->c_str() : NULL,           // current directory
        &siStartInfo,                        // STARTUPINFO pointer
        &piProcInfo);                        // receives PROCESS_INFORMATION

    for (auto & entry : old_env_vars) {
        set_env(entry.first, entry.second);
    }

    // If an error occurs, exit the application.
    if (!bSuccess) {
        throw exception("failed to start child process");
    } else {
        // Close handles to the child process and its primary thread.
        // Some applications might keep these handles to monitor the status
        // of the child process, for example.

        CloseHandle(piProcInfo.hThread);

        return piProcInfo.hProcess;
    }
}

#else

static optional<pipe> setup_stdio(stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        /* We should need to do nothing in this case */
        return optional<pipe>();
    case stdio::PIPED:
        return optional<pipe>(lean::pipe());
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

struct unix_child : public child {
    handle_ref m_stdin;
    handle_ref m_stdout;
    handle_ref m_stderr;
    int m_pid;

    unix_child(int pid, handle_ref hstdin, handle_ref hstdout, handle_ref hstderr) :
            m_stdin(hstdin), m_stdout(hstdout), m_stderr(hstderr), m_pid(pid) {}

    handle_ref get_stdin() override { return m_stdin; }
    handle_ref get_stdout() override { return m_stdout; }
    handle_ref get_stderr() override { return m_stderr; }

    unsigned wait() override {
        int status;
        waitpid(m_pid, &status, 0);
        if (WIFEXITED(status)) {
            return static_cast<unsigned>(WEXITSTATUS(status));
        } else {
            lean_assert(WIFSIGNALED(status));
            // use bash's convention
            return 128 + static_cast<unsigned>(WTERMSIG(status));
        }
    }
};

std::shared_ptr<child> process::spawn_core() {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe = setup_stdio(m_stdin);
    auto stdout_pipe = setup_stdio(m_stdout);
    auto stderr_pipe = setup_stdio(m_stderr);

    int pid = fork();

    if (pid == 0) {
        for (auto & entry : m_env) {
            if (auto val = entry.second) {
                setenv(entry.first.c_str(), val->c_str(), true);
            } else {
                unsetenv(entry.first.c_str());
            }
        }

        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        }

        if (m_cwd) {
            if (chdir(m_cwd->c_str()) < 0) {
                std::cerr << "could not change directory to " << *m_cwd << std::endl;
                exit(-1);
            }
        }

        buffer<char *> pargs;
        for (auto & arg : m_args)
            pargs.push_back(strdup(arg.c_str()));
        pargs.push_back(NULL);

        if (execvp(pargs[0], pargs.data()) < 0) {
            std::cerr << "could not execute external process" << std::endl;
            exit(-1);
        }
    } else if (pid == -1) {
        throw std::runtime_error("forking process failed: ...");
    }

    /* We want to setup the parent's view of the file descriptors. */
    FILE * parent_stdin = nullptr, * parent_stdout = nullptr, * parent_stderr = nullptr;

    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = fdopen(stdin_pipe->m_write_fd, "w");
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = fdopen(stdout_pipe->m_read_fd, "r");
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = fdopen(stderr_pipe->m_read_fd, "r");
    }

    return std::make_shared<unix_child>(pid,
         std::make_shared<handle>(parent_stdin, false),
         std::make_shared<handle>(parent_stdout, false),
         std::make_shared<handle>(parent_stderr, false));
}

#endif

std::shared_ptr<child> process::spawn() {
    if (m_stdout == stdio::INHERIT) {
        std::cout.flush();
    }
    return spawn_core();
}

}




// ========== unification_hint.h ==========

/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "library/expr_pair.h"
#include "library/io_state.h"
#include "library/head_map.h"
#include "util/priority_queue.h"

namespace lean {

/*
Users can declare unification hints using the following structures:

structure unification_constraint := {A : Type} (lhs : A) (rhs : A)
structure unification_hint := (pattern : unification_constraint) (constraints : list unification_constraint)

Example:

definition both_zero_of_add_eq_zero [unify] (n₁ n₂ : ℕ) (s₁ : has_add ℕ) (s₂ : has_zero ℕ) : unification_hint :=
  unification_hint.mk (unification_constraint.mk (@has_add.add ℕ s₁ n₁ n₂) (@has_zero.zero ℕ s₂))
    [unification_constraint.mk n₁ (@has_zero.zero ℕ s₂),
     unification_constraint.mk n₂ (@has_zero.zero ℕ s₂)]

creates the following unification hint:
m_lhs: add nat #1 #3 #2
m_rhs: zero nat #0
m_constraints: [(#3, zero nat #0), (#2, zero nat #0)]
m_num_vars: #4

Note that once we have an assignment to all variables from matching, we must substitute the assignments in the constraints.
*/
class unification_hint {
    expr m_lhs;
    expr m_rhs;

    list<expr_pair> m_constraints;
    unsigned m_num_vars;
public:
    expr get_lhs() const { return m_lhs; }
    expr get_rhs() const { return m_rhs; }
    list<expr_pair> get_constraints() const { return m_constraints; }
    unsigned get_num_vars() const { return m_num_vars; }

    unification_hint() {}
    unification_hint(expr const & lhs, expr const & rhs, list<expr_pair> const & constraints, unsigned num_vars);
    format pp(unsigned priority, formatter const & fmt) const;
};

struct unification_hint_cmp {
    int operator()(unification_hint const & uh1, unification_hint const & uh2) const;
};

typedef priority_queue<unification_hint, unification_hint_cmp> unification_hint_queue;
typedef rb_map<name_pair, unification_hint_queue, name_pair_quick_cmp> unification_hints;

unification_hints get_unification_hints(environment const & env);
void get_unification_hints(unification_hints const & hints, name const & n1, name const & n2, buffer<unification_hint> & uhints);

void get_unification_hints(environment const & env, name const & n1, name const & n2, buffer<unification_hint> & hints);

format pp_unification_hints(unification_hints const & hints, formatter const & fmt);

class type_context_old;
bool try_unification_hint(type_context_old & o, unification_hint const & hint, expr const & lhs, expr const & rhs);

void initialize_unification_hint();
void finalize_unification_hint();
}




// ========== unification_hint.cpp ==========

/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura
*/
#include <string>
#include "util/sexpr/format.h"
#include "kernel/expr.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/error_msgs.h"
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/unification_hint.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/expr_lt.h"
#include "library/scoped_ext.h"
#include "library/fun_info.h"
#include "library/annotation.h"
#include "library/type_context.h"

namespace lean {
unification_hint::unification_hint(expr const & lhs, expr const & rhs, list<expr_pair> const & constraints, unsigned num_vars):
    m_lhs(lhs), m_rhs(rhs), m_constraints(constraints), m_num_vars(num_vars) {}

int unification_hint_cmp::operator()(unification_hint const & uh1, unification_hint const & uh2) const {
    if (uh1.get_lhs() != uh2.get_lhs()) {
        return expr_quick_cmp()(uh1.get_lhs(), uh2.get_lhs());
    } else if (uh1.get_rhs() != uh2.get_rhs()) {
        return expr_quick_cmp()(uh1.get_rhs(), uh2.get_rhs());
    } else {
        auto it1 = uh1.get_constraints().begin();
        auto it2 = uh2.get_constraints().begin();
        auto end1 = uh1.get_constraints().end();
        auto end2 = uh2.get_constraints().end();
        for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
            if (unsigned cmp = expr_pair_quick_cmp()(*it1, *it2)) return cmp;
        }
        return 0;
    }
}

struct unification_hint_state {
    unification_hints m_hints;
    name_map<unsigned> m_decl_names_to_prio; // Note: redundant but convenient

    void validate_type(expr const & decl_type) {
        expr type = decl_type;
        while (is_pi(type)) type = binding_body(type);
        if (!is_app_of(type, get_unification_hint_name(), 0)) {
            throw exception("invalid unification hint, must return element of type `unification hint`");
        }
    }

    void register_hint(environment const & env, name const & decl_name, expr const & value, unsigned priority) {
        m_decl_names_to_prio.insert(decl_name, priority);
        type_context_old _ctx(env, options(), transparency_mode::All);
        tmp_type_context ctx(_ctx);
        expr e_hint = value;
        unsigned num_vars = 0;
        buffer<expr> tmp_mvars;
        while (is_lambda(e_hint)) {
            expr d = instantiate_rev(binding_domain(e_hint), tmp_mvars.size(), tmp_mvars.data());
            tmp_mvars.push_back(ctx.mk_tmp_mvar(d));
            e_hint = binding_body(e_hint);
            num_vars++;
        }

        if (!is_app_of(e_hint, get_unification_hint_mk_name(), 2)) {
            throw exception("invalid unification hint, body must be application of 'unification_hint.mk' to two arguments");
        }

        // e_hint := unification_hint.mk pattern constraints
        expr e_pattern = app_arg(app_fn(e_hint));
        expr e_constraints = app_arg(e_hint);

        // pattern := unification_constraint.mk _ lhs rhs
        expr e_pattern_lhs = app_arg(app_fn(e_pattern));
        expr e_pattern_rhs = app_arg(e_pattern);

        expr e_pattern_lhs_fn = get_app_fn(e_pattern_lhs);
        expr e_pattern_rhs_fn = get_app_fn(e_pattern_rhs);

        if (!is_constant(e_pattern_lhs_fn) || !is_constant(e_pattern_rhs_fn)) {
            throw exception("invalid unification hint, the heads of both sides of pattern must be constants");
        }

        if (quick_cmp(const_name(e_pattern_lhs_fn), const_name(e_pattern_rhs_fn)) > 0) {
            swap(e_pattern_lhs_fn, e_pattern_rhs_fn);
            swap(e_pattern_lhs, e_pattern_rhs);
        }

        name_pair key = mk_pair(const_name(e_pattern_lhs_fn), const_name(e_pattern_rhs_fn));

        buffer<expr_pair> constraints;
        unsigned eqidx = 1;
        while (is_app_of(e_constraints, get_list_cons_name(), 3)) {
            // e_constraints := cons _ constraint rest
            expr e_constraint = app_arg(app_fn(e_constraints));
            expr e_constraint_lhs = app_arg(app_fn(e_constraint));
            expr e_constraint_rhs = app_arg(e_constraint);
            constraints.push_back(mk_pair(e_constraint_lhs, e_constraint_rhs));
            e_constraints = app_arg(e_constraints);

            if (!ctx.is_def_eq(instantiate_rev(e_constraint_lhs, tmp_mvars.size(), tmp_mvars.data()),
                               instantiate_rev(e_constraint_rhs, tmp_mvars.size(), tmp_mvars.data()))) {
                throw exception(sstream() << "invalid unification hint, failed to unify constraint #" << eqidx);
            }
            eqidx++;
        }

        if (!is_app_of(e_constraints, get_list_nil_name(), 1)) {
            throw exception("invalid unification hint, must provide list of constraints explicitly");
        }

        if (!ctx.is_def_eq(instantiate_rev(e_pattern_lhs, tmp_mvars.size(), tmp_mvars.data()),
                           instantiate_rev(e_pattern_rhs, tmp_mvars.size(), tmp_mvars.data()))) {
            throw exception("invalid unification hint, failed to unify pattern after unifying constraints");
        }

        unification_hint hint(e_pattern_lhs, e_pattern_rhs, to_list(constraints), num_vars);
        unification_hint_queue q;
        if (auto const & q_ptr = m_hints.find(key)) q = *q_ptr;
        q.insert(hint, priority);
        m_hints.insert(key, q);
    }
};

struct unification_hint_entry {
    name m_decl_name;
    unsigned m_priority;
    unification_hint_entry(name const & decl_name, unsigned priority):
        m_decl_name(decl_name), m_priority(priority) {}
};

struct unification_hint_config {
    typedef unification_hint_entry entry;
    typedef unification_hint_state state;

    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        declaration decl = env.get(e.m_decl_name);
        s.validate_type(decl.get_type());
        s.register_hint(env, e.m_decl_name, decl.get_value(), e.m_priority);
    }
    static const char * get_serialization_key() { return "UNIFICATION_HINT"; }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_decl_name << e.m_priority;
    }
    static entry read_entry(deserializer & d) {
        name decl_name; unsigned prio;
        d >> decl_name >> prio;
        return entry(decl_name, prio);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(hash(e.m_decl_name.hash(), e.m_priority));
    }
};

typedef scoped_ext<unification_hint_config> unification_hint_ext;

environment add_unification_hint(environment const & env, io_state const & ios, name const & decl_name, unsigned prio,
                                 bool persistent) {
    if (!env.get(decl_name).is_definition())
        throw exception(sstream() << "invalid unification hint, '" << decl_name << "' must be a definition");
    return unification_hint_ext::add_entry(env, ios, unification_hint_entry(decl_name, prio), persistent);
}

unification_hints get_unification_hints(environment const & env) {
    return unification_hint_ext::get_state(env).m_hints;
}

void get_unification_hints(unification_hints const & hints, name const & n1, name const & n2, buffer<unification_hint> & uhints) {
    if (quick_cmp(n1, n2) > 0) {
        if (auto const * q_ptr = hints.find(mk_pair(n2, n1)))
            q_ptr->to_buffer(uhints);
    } else {
        if (auto const * q_ptr = hints.find(mk_pair(n1, n2)))
            q_ptr->to_buffer(uhints);
    }
}

void get_unification_hints(environment const & env, name const & n1, name const & n2, buffer<unification_hint> & uhints) {
    unification_hints hints = unification_hint_ext::get_state(env).m_hints;
    get_unification_hints(hints, n1, n2, uhints);
}

/* Pretty-printing */

// TODO(dhs): I may not be using all the formatting functions correctly.
format unification_hint::pp(unsigned prio, formatter const & fmt) const {
    format r;
    if (prio != LEAN_DEFAULT_PRIORITY)
        r += paren(format(prio)) + space();
    format r1 = fmt(get_lhs()) + space() + format("=?=") + pp_indent_expr(fmt, get_rhs());
    r1 += space() + lcurly();
    r += group(r1);
    bool first = true;
    for (expr_pair const & p : m_constraints) {
        if (first) {
            first = false;
        } else {
            r += comma() + space();
        }
        r += fmt(p.first) + space() + format("=?=") + space() + fmt(p.second);
    }
    r += rcurly();
    return r;
}

format pp_unification_hints(unification_hints const & hints, formatter const & fmt) {
    format r;
    r += format("unification hints") + colon() + line();
    hints.for_each([&](name_pair const & names, unification_hint_queue const & q) {
            q.for_each([&](unification_hint const & hint) {
                    r += lp() + format(names.first) + comma() + space() + format(names.second) + rp() + space();
                    r += hint.pp(*q.get_prio(hint), fmt) + line();
                });
        });
    return r;
}

class unification_hint_fn {
    type_context_old &           m_owner;
    unification_hint const & m_hint;
    buffer<optional<expr>>   m_assignment;

    expr apply_assignment(expr const & e) {
        return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
                if (offset >= get_free_var_range(m))
                    return some_expr(m); // expression m does not contain free variables with idx >= s1
                if (is_var(m)) {
                    unsigned vidx = var_idx(m);
                    if (vidx >= offset) {
                        unsigned h = offset + m_assignment.size();
                        if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                            if (auto v = m_assignment[vidx - offset])
                                return some_expr(*v);
                        }
                        return some_expr(m);
                    }
                }
                return none_expr();
            });
    }

    bool match_app(expr const & p, expr const & e) {
        buffer<expr> p_args, e_args;
        expr const & p_fn = get_app_args(p, p_args);
        expr const & e_fn = get_app_args(e, e_args);
        if (p_args.size() != e_args.size())
            return false;
        fun_info finfo = get_fun_info(m_owner, e_fn, e_args.size());
        unsigned i = 0;
        buffer<unsigned> postponed;
        for (param_info const & pinfo : finfo.get_params_info()) {
            if (!pinfo.is_implicit() && !pinfo.is_inst_implicit()) {
                if (!match(p_args[i], e_args[i])) {
                    return false;
                }
            } else {
                postponed.push_back(i);
            }
            i++;
        }
        for (; i < p_args.size(); i++) {
            if (!match(p_args[i], e_args[i])) {
                return false;
            }
        }
        if (!match(p_fn, e_fn))
            return false;
        for (unsigned i : postponed) {
            expr new_p_arg = apply_assignment(p_args[i]);
            if (closed(new_p_arg)) {
                if (!m_owner.is_def_eq(new_p_arg, e_args[i])) {
                    return false;
                }
            } else {
                if (!match(new_p_arg, e_args[i]))
                    return false;
            }
        }
        return true;
    }

    bool match(expr const & pattern, expr const & e) {
        if (m_owner.is_mvar(e) && m_owner.is_assigned(e)) {
            return match(pattern, m_owner.instantiate_mvars(e));
        }
        if (is_annotation(e)) {
            return match(pattern, get_annotation_arg(e));
        }
        unsigned idx;
        switch (pattern.kind()) {
        case expr_kind::Var:
            idx = var_idx(pattern);
            if (!m_assignment[idx]) {
                m_assignment[idx] = some_expr(e);
                return true;
            } else {
                return m_owner.is_def_eq(*m_assignment[idx], e);
            }
        case expr_kind::Constant:
            return
                is_constant(e) &&
                const_name(pattern) == const_name(e) &&
                m_owner.is_def_eq(const_levels(pattern), const_levels(e));
        case expr_kind::Sort:
            return is_sort(e) && m_owner.is_def_eq(sort_level(pattern), sort_level(e));
        case expr_kind::Pi:    case expr_kind::Lambda:
        case expr_kind::Macro: case expr_kind::Let:
            // Remark: we do not traverse inside of binders.
            return pattern == e;
        case expr_kind::App:
            return
                is_app(e) &&
                match(app_fn(pattern), app_fn(e)) &&
                match(app_arg(pattern), app_arg(e));
        case expr_kind::Local: case expr_kind::Meta:
            lean_unreachable();
        }
        lean_unreachable();
    }

public:
    unification_hint_fn(type_context_old & o, unification_hint const & hint):
        m_owner(o), m_hint(hint) {
        m_assignment.resize(m_hint.get_num_vars());
    }

    bool operator()(expr const & lhs, expr const & rhs) {
        if (!match(m_hint.get_lhs(), lhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "LHS does not match\n";);
            return false;
        } else if (!match(m_hint.get_rhs(), rhs)) {
            lean_trace(name({"type_context", "unification_hint"}), tout() << "RHS does not match\n";);
            return false;
        } else {
            auto instantiate_assignment_fn = [&](expr const & e, unsigned offset) {
                if (is_var(e)) {
                    unsigned idx = var_idx(e) + offset;
                    if (idx < m_assignment.size() && m_assignment[idx])
                        return m_assignment[idx];
                }
                return none_expr();
            };
            buffer<expr_pair> constraints;
            to_buffer(m_hint.get_constraints(), constraints);
            for (expr_pair const & p : constraints) {
                expr new_lhs = replace(p.first, instantiate_assignment_fn);
                expr new_rhs = replace(p.second, instantiate_assignment_fn);
                bool success = m_owner.is_def_eq(new_lhs, new_rhs);
                lean_trace(name({"type_context", "unification_hint"}),
                           scope_trace_env scope(m_owner.env(), m_owner);
                           tout() << new_lhs << " =?= " << new_rhs << "..."
                           << (success ? "success" : "failed") << "\n";);
                if (!success) return false;
            }
            lean_trace(name({"type_context", "unification_hint"}),
                       tout() << "hint successfully applied\n";);
            return true;
        }
    }
};

bool try_unification_hint(type_context_old & o, unification_hint const & hint, expr const & lhs, expr const & rhs) {
    return unification_hint_fn(o, hint)(lhs, rhs);
}

void initialize_unification_hint() {
    unification_hint_ext::initialize();

    register_system_attribute(basic_attribute("unify", "unification hint", add_unification_hint));
}

void finalize_unification_hint() {
    unification_hint_ext::finalize();
}
}




// ========== unique_id.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "util/pair.h"

namespace lean {
class unique_id {
    unsigned m_thread_id;
    unsigned m_id;
    unique_id(unsigned i1, unsigned i2):m_thread_id(i1), m_id(i2) {}
    friend unique_id mk_unique_id();
    friend bool operator==(unique_id const & t1, unique_id const & t2) {
        return t1.m_thread_id == t2.m_thread_id && t1.m_id == t2.m_id;
    }
public:
    /* Use `mk_unique_id()`, this constructor produces and invalid id.
       It can be used to represent uninitialized ids. */
    unique_id();
    bool is_valid() const;
};

inline bool operator!=(unique_id const & t1, unique_id const & t2) {
    return !(t1 == t2);
}

/* Create a global unique id (modulo reset_thread_local).

   Assumptions:
   - We do not create more than 2^32 - 1 threads.
     This is fine because we create a small set of threads
     when we start the process, and then we create only tasks.

   - Each thread does not create more than 2^32 ids.
     This is fine because we reset the thread local counters
     after each \c reset_thread_local operation.

   That being said, if the assumptions above are violated
   \c mk_unique_id throws an exception */
unique_id mk_unique_id();

void initialize_unique_id();
void finalize_unique_id();
}




// ========== unique_id.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <limits>
#include "util/thread.h"
#include "util/exception.h"
#include "library/unique_id.h"

namespace lean {
static unsigned g_next_thread_id       = 0;
static mutex *  g_next_thread_id_guard = nullptr;

LEAN_THREAD_VALUE(unsigned, g_thread_id, std::numeric_limits<unsigned>::max());
LEAN_THREAD_VALUE(unsigned, g_next_idx, 0);

unique_id::unique_id():
    m_thread_id(std::numeric_limits<unsigned>::max()),
    m_id(0) {
}

bool unique_id::is_valid() const {
    return m_thread_id != std::numeric_limits<unsigned>::max();
}

unique_id mk_unique_id() {
    if (g_thread_id == std::numeric_limits<unsigned>::max()) {
        lock_guard<mutex> lock(*g_next_thread_id_guard);
        g_thread_id = g_next_thread_id;
        g_next_thread_id++;
        if (g_next_thread_id == std::numeric_limits<unsigned>::max()) {
            g_next_thread_id--;
            throw exception("failed to generate unique id, too many threads");
        }
    }
    unique_id r(g_thread_id, g_next_idx);
    g_next_idx++;
    if (g_next_idx == std::numeric_limits<unsigned>::max()) {
        g_next_idx--;
        throw exception("failed to generate unique unique id, too many ids have been generated");
    }
    return r;
}

void initialize_unique_id() {
    g_next_thread_id_guard = new mutex();
    register_thread_local_reset_fn([]() { g_next_idx = 0; });
}

void finalize_unique_id() {
    delete g_next_thread_id_guard;
}
}




// ========== mt_task_queue.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <deque>
#include <vector>
#include <unordered_set>
#include <map>
#include <functional>
#include "util/task.h"

namespace lean {

#if defined(LEAN_MULTI_THREAD)

class mt_task_queue : public task_queue {
    mutex m_mutex;
    std::map<unsigned, std::deque<gtask>> m_queue;
    std::unordered_set<gtask> m_waiting;
    condition_variable m_queue_added, m_queue_changed;
    void notify_queue_changed();

    bool m_shutting_down = false;
    condition_variable m_shut_down_cv;

    struct worker_info {
        std::unique_ptr<lthread> m_thread;
        gtask m_current_task;
    };
    std::vector<std::shared_ptr<worker_info>> m_workers;
    void spawn_worker();

    unsigned m_sleeping_workers = 0;
    int m_required_workers;
    condition_variable m_wake_up_worker;

    gtask dequeue();
    void enqueue(gtask const &);

    bool check_deps(gtask const &);
    void submit_core(gtask const &, unsigned);
    void bump_prio(gtask const &, unsigned);
    void cancel_core(gtask const &);
    bool empty_core();

    void handle_finished(gtask const &);

    struct mt_sched_info : public scheduling_info {
        unsigned m_prio;
        std::vector<gtask> m_reverse_deps;
        std::shared_ptr<condition_variable> m_has_finished;

        mt_sched_info(unsigned prio) : m_prio(prio) {}

        template <class Fn> void wait(unique_lock<mutex> &, Fn &&);
        void notify();
    };
    mt_sched_info & get_sched_info(gtask const & t) {
        return static_cast<mt_sched_info &>(*get_data(t)->m_sched_info);
    }

    unsigned & get_prio(gtask const & t) { return get_sched_info(t).m_prio; }
    gtask_imp * get_imp(gtask const & t) { return get_data(t)->m_imp.get(); }

    unsigned get_default_prio();

public:
    mt_task_queue(unsigned num_workers);
    ~mt_task_queue();

    void wait_for_finish(gtask const & t) override;
    void fail_and_dispose(gtask const &t) override;

    void submit(gtask const & t, unsigned prio) override;
    void submit(gtask const & t) override;

    void evacuate() override;

    void join() override;
};

#endif

}




// ========== mt_task_queue.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <algorithm>
#include <vector>
#include "library/mt_task_queue.h"
#include "util/interrupt.h"
#include "util/flet.h"

#if defined(LEAN_MULTI_THREAD)
namespace lean {

LEAN_THREAD_PTR(gtask, g_current_task);
struct scoped_current_task : flet<gtask *> {
    scoped_current_task(gtask * t) : flet(g_current_task, t) {}
};

template <class T>
struct scoped_add {
    T & m_ref;
    T m_delta;
    scoped_add(T & ref, T delta) : m_ref(ref), m_delta(delta) {
        m_ref += m_delta;
    }
    ~scoped_add() {
        m_ref -= m_delta;
    }
};

mt_task_queue::mt_task_queue(unsigned num_workers) : m_required_workers(num_workers) {}

mt_task_queue::~mt_task_queue() {
    unique_lock<mutex> lock(m_mutex);
    m_queue_changed.wait(lock, [=] { return empty_core(); });
    m_shutting_down = true;
    m_queue_added.notify_all();
    m_queue_changed.notify_all();
    m_wake_up_worker.notify_all();
    m_shut_down_cv.wait(lock, [=] { return m_workers.empty(); });
}


template <class Fn>
void mt_task_queue::mt_sched_info::wait(unique_lock<mutex> & lock, Fn && fn) {
    if (!m_has_finished)
        m_has_finished = std::make_shared<condition_variable>();
    auto has_finished = m_has_finished;
    has_finished->wait(lock, fn);
}

void mt_task_queue::mt_sched_info::notify() {
    if (m_has_finished) m_has_finished->notify_all();
}

bool mt_task_queue::empty_core() {
    for (auto & w : m_workers) {
        if (w->m_current_task)
            return false;
    }
    return m_queue.empty() && m_waiting.empty();
}

void mt_task_queue::notify_queue_changed() {
    m_queue_changed.notify_all();
}

constexpr chrono::milliseconds g_worker_max_idle_time = chrono::milliseconds(1000);

void mt_task_queue::spawn_worker() {
    lean_always_assert(!m_shutting_down);
    auto this_worker = std::make_shared<worker_info>();
    m_workers.push_back(this_worker);
    m_required_workers--;
    this_worker->m_thread.reset(new lthread([this, this_worker]() {
        save_stack_info(false);

        unique_lock<mutex> lock(m_mutex);
        while (true) {
            if (m_shutting_down) {
                break;
            }
            if (m_required_workers < 0) {
                scoped_add<int> inc_required(m_required_workers, +1);
                scoped_add<unsigned> inc_sleeping(m_sleeping_workers, +1);
                if (m_wake_up_worker.wait_for(lock, g_worker_max_idle_time,
                                              [&] { return m_required_workers >= 1 || m_shutting_down; })) {
                    continue;
                } else {
                    break;
                }
            }
            if (m_queue.empty()) {
                if (m_queue_added.wait_for(lock, g_worker_max_idle_time,
                                           [&] { return !m_queue.empty() || m_shutting_down; })) {
                    continue;
                } else {
                    break;
                }
            }

            auto t = dequeue();
            if (get_state(t).load() != task_state::Queued) continue;

            get_state(t) = task_state::Running;
            reset_heartbeat();
            reset_thread_local();
            {
                flet<gtask> _(this_worker->m_current_task, t);
                scoped_current_task scope_cur_task(&t);
                notify_queue_changed();
                lock.unlock();
                execute(t);
                lock.lock();
            }
            reset_heartbeat();

            handle_finished(t);

            notify_queue_changed();
        }

        // We need to run the finalizers while the lock is held,
        // otherwise we risk a race condition at the end of the program.
        // We would finalize in the thread, while we call the finalize() function.
        run_thread_finalizers();
        run_post_thread_finalizers();

        m_workers.erase(std::find(m_workers.begin(), m_workers.end(), this_worker));
        m_required_workers++;
        m_shut_down_cv.notify_all();
    }));
}

void mt_task_queue::handle_finished(gtask const & t) {
    lean_always_assert(get_state(t).load() > task_state::Running);
    lean_always_assert(get_data(t));

    if (!get_data(t)->m_sched_info)
        return;  // task has never been submitted

    m_waiting.erase(t);
    get_sched_info(t).notify();

    for (auto & rdep : get_sched_info(t).m_reverse_deps) {
        switch (get_state(rdep).load()) {
            case task_state::Waiting: case task_state::Queued:
                if (check_deps(rdep)) {
                    m_waiting.erase(rdep);
                    if (get_state(rdep).load() < task_state::Running) {
                        lean_always_assert(get_data(rdep));
                        // TODO(gabriel): we need to give up the lock on m_mutex for this
                        if (false && get_data(rdep)->m_flags.m_eager_execution) {
                            get_state(rdep) = task_state::Running;
                            execute(rdep);
                            handle_finished(rdep);
                        } else {
                            enqueue(rdep);
                        }
                    }
                }
                break;
            case task_state::Failed:
                // TODO(gabriel): removed failed tasks from reverse dependency lists?
                m_waiting.erase(rdep);
                break;
            case task_state::Success:
                // this can happen if a task occurs in more than one reverse dependency list,
                // or gets submitted more than once
                break;
            default: lean_unreachable();
        }
    }

    clear(t);
}

void mt_task_queue::submit(gtask const & t, unsigned prio) {
    if (!t || get_state(t).load() >= task_state::Running) return;
    unique_lock<mutex> lock(m_mutex);
    submit_core(t, prio);
}
void mt_task_queue::submit_core(gtask const & t, unsigned prio) {
    if (!t) return;
    switch (get_state(t).load()){
        case task_state::Created:
            get_data(t)->m_sched_info.reset(new mt_sched_info(prio));
            if (check_deps(t)) {
                if (get_state(t).load() < task_state::Running) {
                    // TODO(gabriel): we need to give up the lock on m_mutex for this
                    if (false && get_data(t)->m_flags.m_eager_execution) {
                        get_state(t) = task_state::Running;
                        execute(t);
                        handle_finished(t);
                    } else {
                        enqueue(t);
                    }
                }
            } else {
                get_state(t) = task_state::Waiting;
                m_waiting.insert(t);
                notify_queue_changed();
            }
            break;
        case task_state::Waiting: case task_state::Queued:
            bump_prio(t, prio);
            break;
        case task_state::Running: case task_state::Failed: case task_state::Success:
            break;
    }
    lean_always_assert(get_state(t).load() >= task_state::Waiting);
}

void mt_task_queue::bump_prio(gtask const & t, unsigned new_prio) {
    switch (get_state(t).load()) {
        case task_state::Queued:
            if (new_prio < get_prio(t)) {
                auto prio = get_prio(t);
                auto &q = m_queue[prio];
                auto it = std::find(q.begin(), q.end(), t);
                lean_always_assert(it != q.end());
                q.erase(it);
                if (q.empty()) m_queue.erase(prio);

                get_prio(t) = std::min(get_prio(t), new_prio);
                check_deps(t);
                enqueue(t);
            }
            break;
        case task_state::Waiting:
            if (new_prio < get_prio(t)) {
                get_prio(t) = std::min(get_prio(t), new_prio);
                check_deps(t);
            }
            break;
        case task_state::Running: case task_state::Failed: case task_state::Success:
            break;
        default: lean_unreachable();
    }
}

bool mt_task_queue::check_deps(gtask const & t) {
    check_stack("mt_task_queue::check_deps");
    lean_always_assert(get_data(t));

    buffer<gtask> deps;
    try {
        get_data(t)->m_imp->get_dependencies(deps);
    } catch (...) {}

    auto prio = get_prio(t);
    for (auto & dep : deps) {
        if (dep) {
            submit_core(dep, prio);
            bump_prio(dep, prio);
        }
    }

    for (auto & dep : deps) {
        if (!dep) continue;
        switch (get_state(dep).load()) {
            case task_state::Waiting: case task_state::Queued: case task_state::Running:
                lean_always_assert(get_imp(dep));
                get_sched_info(dep).m_reverse_deps.push_back(t);
                return false;
            case task_state::Success:
                break;
            case task_state::Failed:
                break;
            default: lean_unreachable();
        }
    }
    return true;
}

void mt_task_queue::wait_for_finish(gtask const & t) {
    if (!t || get_state(t).load() > task_state::Running) return;
    unique_lock<mutex> lock(m_mutex);
    submit_core(t, get_default_prio());
    if (get_state(t).load() <= task_state::Running) {
        int additionally_required_workers = 0;
        if (g_current_task) {
            additionally_required_workers++;
            if (m_sleeping_workers == 0) {
                spawn_worker();
            } else {
                m_wake_up_worker.notify_one();
            }
        }
        scoped_add<int> inc_required(m_required_workers, additionally_required_workers);
        get_sched_info(t).wait(lock, [&] {
            return get_state(t).load() > task_state::Running;
        });
    }
    switch (get_state(t).load()) {
        case task_state::Failed: case task_state::Success: return;
        default: throw exception("invalid task state");
    }
}

void mt_task_queue::cancel_core(gtask const & t) {
    if (!t) return;
    switch (get_state(t).load()) {
        case task_state::Waiting:
            m_waiting.erase(t);
            /* fall-thru */
        case task_state::Created: case task_state::Queued:
            fail(t, std::make_exception_ptr(cancellation_exception()));
            handle_finished(t);
            return;
        default: return;
    }
}
void mt_task_queue::fail_and_dispose(gtask const & t) {
    if (!t) return;
    unique_lock<mutex> lock(m_mutex);
    cancel_core(t);
}

void mt_task_queue::join() {
    unique_lock<mutex> lock(m_mutex);
    m_queue_changed.wait(lock, [=] { return empty_core(); });
}

gtask mt_task_queue::dequeue() {
    lean_always_assert(!m_queue.empty());
    auto it = m_queue.begin();
    auto & highest_prio = it->second;
    lean_always_assert(!highest_prio.empty());
    auto result = std::move(highest_prio.front());
    highest_prio.pop_front();
    if (highest_prio.empty()) {
        m_queue.erase(it);
    }
    return result;
}

void mt_task_queue::enqueue(gtask const & t) {
    lean_always_assert(get_state(t).load() < task_state::Running);
    lean_always_assert(get_imp(t));
    get_state(t) = task_state::Queued;
    m_queue[get_prio(t)].push_back(t);
    if (m_required_workers > 0) {
        spawn_worker();
    } else {
        m_queue_added.notify_one();
    }
    notify_queue_changed();
}

void mt_task_queue::evacuate() {
    unique_lock<mutex> lock(m_mutex);
    for (auto & q : m_queue) for (auto & t : q.second) cancel_core(t);

    buffer<gtask> to_cancel; // copy because of iterator invalidation
    for (auto & t : m_waiting) to_cancel.push_back(t);
    for (auto & t : to_cancel) cancel_core(t);
}

void mt_task_queue::submit(gtask const & t) {
    submit(t, get_default_prio());
}

unsigned mt_task_queue::get_default_prio() {
    if (g_current_task && get_imp(*g_current_task)) {
        return get_prio(*g_current_task);
    } else {
        return 0;
    }
}

}
#endif




// ========== projection.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Auxiliary information attached to projections. This information
    is used to simplify projection over constructor (efficiently).

    That is, given a projection pr_i associated with the constructor mk
    where A are parameters, we want to implement the following reduction
    efficiently. The idea is to avoid unfolding pr_i.

       pr_i A (mk A f_1 ... f_n) ==> f_i

    We also use this information in the rewriter/simplifier.
*/
struct projection_info {
    name     m_constructor;   // mk in the rule above
    unsigned m_nparams;       // number of parameters of the inductive datatype
    unsigned m_i;             // i in the rule above
    bool     m_inst_implicit; // true if it is the projection of a "class"

    projection_info() {}
    projection_info(name const & c, unsigned nparams, unsigned i, bool inst_implicit):
        m_constructor(c), m_nparams(nparams), m_i(i), m_inst_implicit(inst_implicit) {}
};

/** \brief Mark \c p as a projection in the given environment and store that
    \c mk is the constructor associated with it, \c nparams is the number of parameters, and
    \c i says that \c p is the i-th projection.
*/
environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i,
                                 bool inst_implicit);

/** \brief If \c p is a projection in the given environment, then return the information
    associated with it (constructor, number of parameters, and index).
    If \c p is not a projection, then return nullptr.
*/
projection_info const * get_projection_info(environment const & env, name const & p);

inline bool is_projection(environment const & env, name const & n) {
    return get_projection_info(env, n) != nullptr;
}

/** \brief Return the mapping from projection name to associated information */
name_map<projection_info> const & get_projection_info_map(environment const & env);

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure_like(environment const & env, name const & S);

void initialize_projection();
void finalize_projection();
}




// ========== projection.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/projection.h"
#include "library/module.h"
#include "library/kernel_serializer.h"

namespace lean {
/** \brief This environment extension stores information about all projection functions
    defined in an environment object.
*/
struct projection_ext : public environment_extension {
    name_map<projection_info> m_info;
    projection_ext() {}
};

struct projection_ext_reg {
    unsigned m_ext_id;
    projection_ext_reg() {
        m_ext_id = environment::register_extension(std::make_shared<projection_ext>());
    }
};

static projection_ext_reg * g_ext = nullptr;
static projection_ext const & get_extension(environment const & env) {
    return static_cast<projection_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, projection_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<projection_ext>(ext));
}

struct proj_modification : public modification {
    LEAN_MODIFICATION("proj")

    name m_proj;
    projection_info m_info;

    proj_modification() {}
    proj_modification(name const & proj, projection_info const & info) : m_proj(proj), m_info(info) {}

    void perform(environment & env) const override {
        projection_ext ext = get_extension(env);
        ext.m_info.insert(m_proj, m_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_proj << m_info.m_constructor << m_info.m_nparams << m_info.m_i << m_info.m_inst_implicit;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name p, mk; unsigned nparams, i; bool inst_implicit;
        d >> p >> mk >> nparams >> i >> inst_implicit;
        return std::make_shared<proj_modification>(p, projection_info(mk, nparams, i, inst_implicit));
    }
};

environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i, bool inst_implicit) {
    return module::add_and_perform(env, std::make_shared<proj_modification>(
            p, projection_info(mk, nparams, i, inst_implicit)));
}

projection_info const * get_projection_info(environment const & env, name const & p) {
    projection_ext const & ext = get_extension(env);
    return ext.m_info.find(p);
}

name_map<projection_info> const & get_projection_info_map(environment const & env) {
    return get_extension(env).m_info;
}

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure_like(environment const & env, name const & S) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, S);
    if (!decl) return false;
    return length(decl->m_intro_rules) == 1 && *inductive::get_num_indices(env, S) == 0;
}

void initialize_projection() {
    g_ext      = new projection_ext_reg();
    proj_modification::init();
}

void finalize_projection() {
    proj_modification::finalize();
    delete g_ext;
}
}




// ========== app_builder.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <unordered_map>
#include "kernel/environment.h"
#include "library/relation_manager.h"
#include "library/reducible.h"
#include "library/type_context.h"

namespace lean {
class app_builder_exception : public exception {
public:
    // We may provide more information in the future.
    app_builder_exception():
        exception("app_builder_exception, more information can be obtained using command "
                  "`set_option trace.app_builder true`") {}
};

/** \brief Create an application (d.{_ ... _} _ ... _ args[0] ... args[nargs-1]).
    The missing arguments and universes levels are inferred using type inference.

    \remark The method throwns an app_builder_exception if: not all arguments can be inferred;
    or constraints are created during type inference; or an exception is thrown
    during type inference.

    \remark This methods uses just higher-order pattern matching.

    \remark if the transparency mode is not provided, then mk_app will use Semireducible
    if the ctx.mode() is Reducible or None.
*/
expr mk_app(type_context_old & ctx, name const & c, unsigned nargs, expr const * args,
            optional<transparency_mode> const & md = optional<transparency_mode>());

inline expr mk_app(type_context_old & ctx, name const & c, std::initializer_list<expr> const & args,
                   optional<transparency_mode> const & md = optional<transparency_mode>()) {
    return mk_app(ctx, c, args.size(), args.begin(), md);
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1) {
    return mk_app(ctx, c, {a1});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2) {
    return mk_app(ctx, c, {a1, a2});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2, expr const & a3) {
    return mk_app(ctx, c, {a1, a2, a3});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2, expr const & a3, expr const & a4) {
    return mk_app(ctx, c, {a1, a2, a3, a4});
}

expr mk_app(type_context_old & ctx, name const & c, unsigned mask_sz, bool const * mask, expr const * args);

/** \brief Shortcut for mk_app(c, total_nargs, mask, expl_nargs), where
    \c mask starts with total_nargs - expl_nargs false's followed by expl_nargs true's
    \pre total_nargs >= expl_nargs */
expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args);

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, std::initializer_list<expr> const & args) {
    return mk_app(ctx, c, total_nargs, args.size(), args.begin());
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1) {
    return mk_app(ctx, c, total_nargs, {a1});
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1, expr const & a2) {
    return mk_app(ctx, c, total_nargs, {a1, a2});
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1, expr const & a2, expr const & a3) {
    return mk_app(ctx, c, total_nargs, {a1, a2, a3});
}

/** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
expr mk_rel(type_context_old & ctx, name const & n, expr const & lhs, expr const & rhs);
expr mk_eq(type_context_old & ctx, expr const & lhs, expr const & rhs);
expr mk_iff(type_context_old & ctx, expr const & lhs, expr const & rhs);
expr mk_heq(type_context_old & ctx, expr const & lhs, expr const & rhs);

/** \brief Similar a reflexivity proof for the given relation */
expr mk_refl(type_context_old & ctx, name const & relname, expr const & a);
expr mk_eq_refl(type_context_old & ctx, expr const & a);
expr mk_iff_refl(type_context_old & ctx, expr const & a);
expr mk_heq_refl(type_context_old & ctx, expr const & a);

/** \brief Similar a symmetry proof for the given relation */
expr mk_symm(type_context_old & ctx, name const & relname, expr const & H);
expr mk_eq_symm(type_context_old & ctx, expr const & H);
expr mk_eq_symm(type_context_old & ctx, expr const & a, expr const & b, expr const & H);
expr mk_iff_symm(type_context_old & ctx, expr const & H);
expr mk_heq_symm(type_context_old & ctx, expr const & H);

/** \brief Similar a transitivity proof for the given relation */
expr mk_trans(type_context_old & ctx, name const & relname, expr const & H1, expr const & H2);
expr mk_eq_trans(type_context_old & ctx, expr const & H1, expr const & H2);
expr mk_eq_trans(type_context_old & ctx, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2);
expr mk_iff_trans(type_context_old & ctx, expr const & H1, expr const & H2);
expr mk_heq_trans(type_context_old & ctx, expr const & H1, expr const & H2);

/** \brief Create a (non-dependent) eq.rec application.
    C is the motive. The expected types for C, H1 and H2 are
    C : A -> Type
    H1 : C a
    H2 : a = b
    The resultant application is
    @eq.rec A a C H1 b H2 */
expr mk_eq_rec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2);

/** \brief Create a (dependent) eq.drec application.
    C is the motive. The expected types for C, H1 and H2 are
    C : Pi (x : A), a = x -> Type
    H1 : C a (eq.refl a)
    H2 : a = b
    The resultant application is
    @eq.drec A a C H1 b H2 */
expr mk_eq_drec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2);

expr mk_eq_of_heq(type_context_old & ctx, expr const & H);
expr mk_heq_of_eq(type_context_old & ctx, expr const & H);

expr mk_congr_arg(type_context_old & ctx, expr const & f, expr const & H, bool skip_arrow_test = false);
expr mk_congr_fun(type_context_old & ctx, expr const & H, expr const & a);
expr mk_congr(type_context_old & ctx, expr const & H1, expr const & H2, bool skip_arrow_test = false);

expr mk_funext(type_context_old & ctx, expr const & lam_pf);

/** \brief Given a reflexive relation R, and a proof H : a = b,
    build a proof for (R a b) */
expr lift_from_eq(type_context_old & ctx, name const & R, expr const & H);

/** \brief not p -> (p <-> false) */
expr mk_iff_false_intro(type_context_old & ctx, expr const & H);
/** \brief p -> (p <-> true) */
expr mk_iff_true_intro(type_context_old & ctx, expr const & H);
/** \brief (p <-> false) -> not p */
expr mk_not_of_iff_false(type_context_old & ctx, expr const & H);
/** \brief (p <-> true) -> p */
expr mk_of_iff_true(type_context_old & ctx, expr const & H);
/** \brief (true <-> false) -> false */
expr mk_false_of_true_iff_false(type_context_old & ctx, expr const & H);
/** \brief (true = false) -> false */
expr mk_false_of_true_eq_false(type_context_old & ctx, expr const & H);

/** \brief not p -> (p = false) */
expr mk_eq_false_intro(type_context_old & ctx, expr const & H);
/** \brief p -> (p = true) */
expr mk_eq_true_intro(type_context_old & ctx, expr const & H);
/** not(p <-> q) -> not(p = q) */
expr mk_neq_of_not_iff(type_context_old & ctx, expr const & H);

expr mk_of_eq_true(type_context_old & ctx, expr const & H);
expr mk_not_of_eq_false(type_context_old & ctx, expr const & H);

expr mk_not(type_context_old & ctx, expr const & H);

/** p -> not p -> b */
expr mk_absurd(type_context_old & ctx, expr const & Hp, expr const & Hnp, expr const & b);

expr mk_partial_add(type_context_old & ctx, expr const & A);
expr mk_partial_mul(type_context_old & ctx, expr const & A);
expr mk_zero(type_context_old & ctx, expr const & A);
expr mk_one(type_context_old & ctx, expr const & A);
expr mk_partial_left_distrib(type_context_old & ctx, expr const & A);
expr mk_partial_right_distrib(type_context_old & ctx, expr const & A);

expr mk_ss_elim(type_context_old & ctx, expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e);

/** \brief False elimination */
expr mk_false_rec(type_context_old & ctx, expr const & c, expr const & H);

/* (if c then t else e) */
expr mk_ite(type_context_old & ctx, expr const & c, expr const & t, expr const & e);

/* (@id type h) */
expr mk_id(type_context_old & ctx, expr const & type, expr const & h);
/* (id h) */
expr mk_id(type_context_old & ctx, expr const & h);

/* (id_rhs h) */
expr mk_id_rhs(type_context_old & ctx, expr const & h);

/* (id_delta h) */
expr mk_id_delta(type_context_old & ctx, expr const & h);

expr mk_iff_mp(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_iff_mpr(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_eq_mp(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_eq_mpr(type_context_old & ctx, expr const & h1, expr const & h2);

void initialize_app_builder();
void finalize_app_builder();
}




// ========== app_builder.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/name_map.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/idx_metavar.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/cache_helper.h"
#include "library/app_builder.h"
#include "library/relation_manager.h"

namespace lean {
static void trace_fun(name const & n) {
    tout() << "failed to create an '" << n << "'-application";
}

static void trace_failure(name const & n, unsigned nargs, char const * msg) {
    lean_trace("app_builder",
               trace_fun(n); tout() << " with " << nargs << ", " << msg << "\n";);
}

static void trace_failure(name const & n, char const * msg) {
    lean_trace("app_builder",
               trace_fun(n); tout() << ", " << msg << "\n";);
}

#define lean_app_builder_trace_core(ctx, code) lean_trace("app_builder", scope_trace_env _scope1(ctx.env(), ctx); code)
#define lean_app_builder_trace(code) lean_app_builder_trace_core(m_ctx, code)

static unsigned get_nargs(unsigned mask_sz, bool const * mask) {
    unsigned nargs = 0;
    for (unsigned i = 0; i < mask_sz; i++) {
        if (mask[i])
            nargs++;
    }
    return nargs;
}

class app_builder_cache {
    struct entry {
        unsigned             m_num_umeta;
        unsigned             m_num_emeta;
        expr                 m_app;
        list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
        list<expr>           m_expl_args; // metavars for explicit arguments
        /*
          IMPORTANT: for m_inst_args we store the arguments in reverse order.
          For example, the first element in the list indicates whether the last argument
          is an instance implicit argument or not. If it is not none, then the element
          is the associated metavariable

          m_expl_args are also stored in reverse order
        */
    };

    struct key {
        name       m_name;
        unsigned   m_num_expl;
        unsigned   m_hash;
        // If nil, then the mask is composed of the last m_num_expl arguments.
        // If nonnil, then the mask is NOT of the form [false*, true*]
        list<bool> m_mask;

        key(name const & c, unsigned n):
            m_name(c), m_num_expl(n),
            m_hash(::lean::hash(c.hash(), n)) {
        }

        key(name const & c, list<bool> const & m):
            m_name(c), m_num_expl(length(m)) {
            m_hash = ::lean::hash(c.hash(), m_num_expl);
            m_mask = m;
            for (bool b : m) {
                if (b)
                    m_hash = ::lean::hash(m_hash, 17u);
                else
                    m_hash = ::lean::hash(m_hash, 31u);
            }
        }

        bool check_invariant() const {
            lean_assert(empty(m_mask) || length(m_mask) == m_num_expl);
            return true;
        }

        unsigned hash() const { return m_hash; }
        friend bool operator==(key const & k1, key const & k2) {
            return k1.m_name == k2.m_name && k1.m_num_expl == k2.m_num_expl && k1.m_mask == k2.m_mask;
        }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.hash(); }
    };

    typedef std::unordered_map<key, entry, key_hash_fn> map;

    environment          m_env;
    map                  m_map;
    friend class app_builder;
public:
    app_builder_cache(environment const & env):
        m_env(env) {
    }

    environment const & env() const { return m_env; }
};

typedef cache_compatibility_helper<app_builder_cache> app_builder_cache_helper;

/* CACHE_RESET: YES */
MK_THREAD_LOCAL_GET_DEF(app_builder_cache_helper, get_abch);

/** Return an app_builder_cache for the transparency_mode in ctx, and compatible with the environment. */
app_builder_cache & get_app_builder_cache_for(type_context_old const & ctx) {
    return get_abch().get_cache_for(ctx);
}

static level get_level_ap(type_context_old & ctx, expr const & A) {
    try {
        return get_level(ctx, A);
    } catch (exception &) {
        lean_app_builder_trace_core(ctx, tout() << "failed to infer universe level for type " << A << "\n";);
        throw app_builder_exception();
    }
}

/** \brief Helper for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type.{1}
        real    : Type.{1}
        vec.{l} : Pi (A : Type.{l}) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        builder.mk_app(rel, f, g)
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g
*/
class app_builder {
    type_context_old &      m_ctx;
    app_builder_cache & m_cache;
    typedef app_builder_cache::key   key;
    typedef app_builder_cache::entry entry;

    environment const & env() const { return m_ctx.env(); }

    levels mk_metavars(declaration const & d, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = m_ctx.relaxed_whnf(instantiate_type_univ_params(d, lvls));
        while (is_pi(type)) {
            expr mvar = m_ctx.mk_tmp_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = m_ctx.relaxed_whnf(instantiate(binding_body(type), mvar));
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned nargs) {
        key k(c, nargs);
        lean_assert(k.check_invariant());
        auto it = m_cache.m_map.find(k);
        if (it == m_cache.m_map.end()) {
            if (auto d = env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mvars, inst_args);
                if (nargs > mvars.size())
                    return optional<entry>(); // insufficient number of arguments
                entry e;
                e.m_num_umeta = d->get_num_univ_params();
                e.m_num_emeta = mvars.size();
                e.m_app       = ::lean::mk_app(mk_constant(c, lvls), mvars);
                e.m_inst_args = reverse_to_list(inst_args.begin(), inst_args.end());
                e.m_expl_args = reverse_to_list(mvars.begin() + mvars.size() - nargs, mvars.end());
                m_cache.m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    levels mk_metavars(declaration const & d, unsigned arity, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = instantiate_type_univ_params(d, lvls);
        for (unsigned i = 0; i < arity; i++) {
            type   = m_ctx.relaxed_whnf(type);
            if (!is_pi(type)) {
                trace_failure(d.get_name(), arity, "too many arguments");
                throw app_builder_exception();
            }
            expr mvar = m_ctx.mk_tmp_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = instantiate(binding_body(type), mvar);
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned mask_sz, bool const * mask) {
        key k(c, to_list(mask, mask+mask_sz));
        lean_assert(k.check_invariant());
        auto it = m_cache.m_map.find(k);
        if (it == m_cache.m_map.end()) {
            if (auto d = env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mask_sz, mvars, inst_args);
                entry e;
                e.m_num_umeta = d->get_num_univ_params();
                e.m_num_emeta = mvars.size();
                e.m_app       = ::lean::mk_app(mk_constant(c, lvls), mvars);
                e.m_inst_args = reverse_to_list(inst_args.begin(), inst_args.end());
                list<expr> expl_args;
                for (unsigned i = 0; i < mask_sz; i++) {
                    if (mask[i])
                        expl_args = cons(mvars[i], expl_args);
                }
                e.m_expl_args = expl_args;
                m_cache.m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    bool check_all_assigned(entry const & e) {
        lean_assert(e.m_num_emeta == length(e.m_inst_args));
        // recall that the flags at e.m_inst_args are stored in reverse order.
        // For example, the first flag in the list indicates whether the last argument
        // is an instance implicit argument or not.
        unsigned i = e.m_num_emeta;
        for (optional<expr> const & inst_arg : e.m_inst_args) {
            lean_assert(i > 0);
            --i;
            if (!m_ctx.get_tmp_mvar_assignment(i)) {
                if (inst_arg) {
                    expr type = m_ctx.instantiate_mvars(mlocal_type(*inst_arg));
                    if (auto v = m_ctx.mk_class_instance(type)) {
                        if (!m_ctx.is_def_eq(*inst_arg, *v)) {
                            // failed to assign instance
                            return false;
                        }
                    } else {
                        // failed to generate instance
                        return false;
                    }
                } else {
                    // unassined metavar
                    return false;
                }
            }
        }
        for (unsigned i = 0; i < e.m_num_umeta; i++) {
            if (!m_ctx.get_tmp_uvar_assignment(i))
                return false;
        }
        return true;
    }

    void init_ctx_for(entry const & e) {
        m_ctx.ensure_num_tmp_mvars(e.m_num_umeta, e.m_num_emeta);
    }

    void trace_unify_failure(name const & n, unsigned i, expr const & m, expr const & v) {
        lean_app_builder_trace(
            trace_fun(n);
            tout () << ", failed to solve unification constraint for #" << (i+1)
            << " argument (" << m_ctx.instantiate_mvars(m_ctx.infer(m)) << " =?= "
            << m_ctx.instantiate_mvars(m_ctx.infer(v)) << ")\n";);
    }

    void trace_inst_failure(expr const & A, char const * n) {
        lean_app_builder_trace(tout() << "failed to build instance of '" << n << "' for " << A << "\n";);
    }

public:
    app_builder(type_context_old & ctx):m_ctx(ctx), m_cache(get_app_builder_cache_for(ctx)) {}

    level get_level(expr const & A) {
        return get_level_ap(m_ctx, A);
    }

    expr mk_app(name const & c, unsigned nargs, expr const * args) {
        lean_assert(std::all_of(args, args + nargs, [](expr const & arg) { return !has_idx_metavar(arg); }))
        type_context_old::tmp_mode_scope scope(m_ctx);
        optional<entry> e = get_entry(c, nargs);
        if (!e) {
            trace_failure(c, "failed to retrieve declaration");
            throw app_builder_exception();
        }
        init_ctx_for(*e);
        unsigned i = nargs;
        for (auto m : e->m_expl_args) {
            if (i == 0) {
                trace_failure(c, "too many explicit arguments");
                throw app_builder_exception();
            }
            --i;
            if (!m_ctx.is_def_eq(m, args[i])) {
                trace_unify_failure(c, i, m, args[i]);
                throw app_builder_exception();
            }
        }
        if (!check_all_assigned(*e)) {
            trace_failure(c, "there are missing implicit arguments");
            throw app_builder_exception();
        }
        return m_ctx.instantiate_mvars(e->m_app);
    }

    expr mk_app(name const & c, std::initializer_list<expr> const & args) {
        return mk_app(c, args.size(), args.begin());
    }

    expr mk_app(name const & c, expr const & a1) {
        return mk_app(c, {a1});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2) {
        return mk_app(c, {a1, a2});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, {a1, a2, a3});
    }

    expr mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
        type_context_old::tmp_mode_scope scope(m_ctx);
        unsigned nargs = get_nargs(mask_sz, mask);
        optional<entry> e = get_entry(c, mask_sz, mask);
        if (!e) {
            trace_failure(c, "failed to retrieve declaration");
            throw app_builder_exception();
        }
        init_ctx_for(*e);
        unsigned i    = mask_sz;
        unsigned j    = nargs;
        list<expr> it = e->m_expl_args;
        while (i > 0) {
            --i;
            if (mask[i]) {
                --j;
                expr const & m = head(it);
                if (!m_ctx.is_def_eq(m, args[j])) {
                    trace_unify_failure(c, j, m, args[j]);
                    throw app_builder_exception();
                }
                it = tail(it);
            }
        }
        if (!check_all_assigned(*e)) {
            trace_failure(c, "there are missing implicit arguments");
            throw app_builder_exception();
        }
        return m_ctx.instantiate_mvars(e->m_app);
    }

    /** \brief Shortcut for mk_app(c, total_nargs, mask, expl_nargs), where
        \c mask starts with total_nargs - expl_nargs false's followed by expl_nargs true's
        \pre total_nargs >= expl_nargs */
    expr mk_app(name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args) {
        lean_assert(total_nargs >= expl_nargs);
        buffer<bool> mask;
        mask.resize(total_nargs - expl_nargs, false);
        mask.resize(total_nargs, true);
        return mk_app(c, mask.size(), mask.data(), expl_args);
    }

    expr mk_app(name const & c, unsigned total_nargs, std::initializer_list<expr> const & args) {
        return mk_app(c, total_nargs, args.size(), args.begin());
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1) {
        return mk_app(c, total_nargs, {a1});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2) {
        return mk_app(c, total_nargs, {a1, a2});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, total_nargs, {a1, a2, a3});
    }

    /** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
    expr mk_rel(name const & n, expr const & lhs, expr const & rhs) {
        if (n == get_eq_name()) {
            return mk_eq(lhs, rhs);
        } else if (n == get_iff_name()) {
            return mk_iff(lhs, rhs);
        } else if (auto info = get_relation_info(env(), n)) {
            buffer<bool> mask;
            for (unsigned i = 0; i < info->get_arity(); i++) {
                mask.push_back(i == info->get_lhs_pos() || i == info->get_rhs_pos());
            }
            expr args[2] = {lhs, rhs};
            return mk_app(n, info->get_arity(), mask.data(), args);
        } else {
            // for unregistered relations assume lhs and rhs are the last two arguments.
            expr args[2] = {lhs, rhs};
            return mk_app(n, 2, args);
        }
    }

    expr mk_eq(expr const & a, expr const & b) {
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_name(), {lvl}), A, a, b);
    }

    expr mk_iff(expr const & a, expr const & b) {
        return ::lean::mk_app(mk_constant(get_iff_name()), a, b);
    }

    expr mk_heq(expr const & a, expr const & b) {
        expr A    = m_ctx.infer(a);
        expr B    = m_ctx.infer(b);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_heq_name(), {lvl}), A, a, B, b);
    }

    /** \brief Similar a reflexivity proof for the given relation */
    expr mk_refl(name const & relname, expr const & a) {
        if (relname == get_eq_name()) {
            return mk_eq_refl(a);
        } else if (relname == get_iff_name()) {
            return mk_iff_refl(a);
        } else if (relname == get_heq_name()) {
            return mk_heq_refl(a);
        } else if (auto info = get_refl_extra_info(env(), relname)) {
            return mk_app(info->m_name, 1, &a);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build reflexivity proof, '" << relname
                << "' is not registered as a reflexive relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_refl(expr const & a) {
        expr A     = m_ctx.infer(a);
        level lvl  = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
    }
    expr mk_iff_refl(expr const & a) {
        return ::lean::mk_app(mk_constant(get_iff_refl_name()), a);
    }
    expr mk_heq_refl(expr const & a) {
        expr A     = m_ctx.infer(a);
        level lvl  = get_level(A);
        return ::lean::mk_app(mk_constant(get_heq_refl_name(), {lvl}), A, a);
    }

    /** \brief Similar a symmetry proof for the given relation */
    expr mk_symm(name const & relname, expr const & H) {
        if (relname == get_eq_name()) {
            return mk_eq_symm(H);
        } else if (relname == get_iff_name()) {
            return mk_iff_symm(H);
        } else if (relname == get_heq_name()) {
            return mk_heq_symm(H);
        } else if (auto info = get_symm_extra_info(env(), relname)) {
            return mk_app(info->m_name, 1, &H);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build symmetry proof, '" << relname
                << "' is not registered as a symmetric relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_symm(expr const & H) {
        if (is_app_of(H, get_eq_refl_name()))
            return H;
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.symm, equality expected:\n" << p << "\n";);
            throw app_builder_exception();
        }
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
    }
    expr mk_eq_symm(expr const & a, expr const & b, expr const & H) {
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, a, b, H);
    }
    expr mk_iff_symm(expr const & H) {
        expr p    = m_ctx.infer(H);
        expr lhs, rhs;
        if (is_iff(p, lhs, rhs)) {
            return ::lean::mk_app(mk_constant(get_iff_symm_name()), lhs, rhs, H);
        } else {
            return mk_app(get_iff_symm_name(), {H});
        }
    }
    expr mk_heq_symm(expr const & H) {
        expr p     = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, B, b;
        if (!is_heq(p, A, a, B, b)) {
            lean_app_builder_trace(tout() << "failed to build heq.symm, heterogeneous equality expected:\n" << p << "\n";);
            throw app_builder_exception();
        }
        level lvl = get_level(A);
        return ::lean::mk_app({mk_constant(get_heq_symm_name(), {lvl}), A, B, a, b, H});
    }

    /** \brief Similar a transitivity proof for the given relation */
    expr mk_trans(name const & relname, expr const & H1, expr const & H2) {
        if (relname == get_eq_name()) {
            return mk_eq_trans(H1, H2);
        } else if (relname == get_iff_name()) {
            return mk_iff_trans(H1, H2);
        } else if (relname == get_heq_name()) {
            return mk_heq_trans(H1, H2);
        } else if (auto info = get_trans_extra_info(env(), relname, relname)) {
            expr args[2] = {H1, H2};
            return mk_app(info->m_name, 2, args);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build symmetry proof, '" << relname
                << "' is not registered as a transitive relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_trans(expr const & H1, expr const & H2) {
        if (is_app_of(H1, get_eq_refl_name()))
            return H2;
        if (is_app_of(H2, get_eq_refl_name()))
            return H1;
        expr p1    = m_ctx.relaxed_whnf(m_ctx.infer(H1));
        expr p2    = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs1, rhs1, lhs2, rhs2;
        if (!is_eq(p1, A, lhs1, rhs1) || !is_eq(p2, lhs2, rhs2)) {
            lean_app_builder_trace(
                tout() << "failed to build eq.trans, equality expected:\n"
                << p1 << "\n" << p2 << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
    }
    expr mk_eq_trans(expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) {
        if (is_app_of(H1, get_eq_refl_name()))
            return H2;
        if (is_app_of(H2, get_eq_refl_name()))
            return H1;
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, a, b, c, H1, H2});
    }
    expr mk_iff_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx.infer(H1);
        expr p2    = m_ctx.infer(H2);
        expr lhs1, rhs1, lhs2, rhs2;
        if (is_iff(p1, lhs1, rhs1) && is_iff(p2, lhs2, rhs2)) {
            return ::lean::mk_app({mk_constant(get_iff_trans_name()), lhs1, rhs1, rhs2, H1, H2});
        } else {
            return mk_app(get_iff_trans_name(), {H1, H2});
        }
    }
    expr mk_heq_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx.relaxed_whnf(m_ctx.infer(H1));
        expr p2    = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A1, a1, B1, b1, A2, a2, B2, b2;
        if (!is_heq(p1, A1, a1, B1, b1) || !is_heq(p2, A2, a2, B2, b2)) {
            lean_app_builder_trace(
                tout() << "failed to build heq.trans, heterogeneous equality expected:\n"
                << p1 << "\n" << p2 << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A1);
        return ::lean::mk_app({mk_constant(get_heq_trans_name(), {lvl}), A1, B1, B2, a1, b1, b2, H1, H2});
    }

    expr mk_eq_rec(expr const & motive, expr const & H1, expr const & H2) {
        if (is_constant(get_app_fn(H2), get_eq_refl_name()))
            return H1;
        expr p       = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.rec, equality proof expected:\n" << H2 << "\n";);
            throw app_builder_exception();
        }
        level A_lvl = get_level(A);
        expr mtype  = m_ctx.relaxed_whnf(m_ctx.infer(motive));
        if (!is_pi(mtype) || !is_sort(binding_body(mtype))) {
            lean_app_builder_trace(tout() << "failed to build eq.rec, invalid motive:\n" << motive << "\n";);
            throw app_builder_exception();
        }
        level l_1    = sort_level(binding_body(mtype));
        name const & eqrec = get_eq_rec_name();
        return ::lean::mk_app({mk_constant(eqrec, {l_1, A_lvl}), A, lhs, motive, H1, rhs, H2});
    }

    expr mk_eq_drec(expr const & motive, expr const & H1, expr const & H2) {
        if (is_constant(get_app_fn(H2), get_eq_refl_name()))
            return H1;
        expr p       = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.drec, equality proof expected:\n" << H2 << "\n";);
            throw app_builder_exception();
        }
        level A_lvl = get_level(A);
        expr mtype  = m_ctx.relaxed_whnf(m_ctx.infer(motive));
        if (!is_pi(mtype) || !is_pi(binding_body(mtype)) || !is_sort(binding_body(binding_body(mtype)))) {
            lean_app_builder_trace(tout() << "failed to build eq.drec, invalid motive:\n" << motive << "\n";);
            throw app_builder_exception();
        }
        level l_1    = sort_level(binding_body(binding_body(mtype)));
        name const & eqrec = get_eq_drec_name();
        return ::lean::mk_app({mk_constant(eqrec, {l_1, A_lvl}), A, lhs, motive, H1, rhs, H2});
    }

    expr mk_eq_of_heq(expr const & H) {
        if (is_constant(get_app_fn(H), get_heq_of_eq_name()))
            return app_arg(H);
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, B, b;
        if (!is_heq(p, A, a, B, b)) {
            lean_app_builder_trace(tout() << "failed to build eq_of_heq, heterogeneous equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_of_heq_name(), {lvl}), A, a, b, H});
    }

    expr mk_heq_of_eq(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_of_heq_name()))
            return app_arg(H);
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, b;
        if (!is_eq(p, A, a, b)) {
            lean_app_builder_trace(tout() << "failed to build heq_of_eq equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_heq_of_eq_name(), {lvl}), A, a, b, H});
    }

    /** \brief Given a reflexive relation R, and a proof H : a = b,
        build a proof for (R a b) */
    expr lift_from_eq(name const & R, expr const & H) {
        if (R == get_eq_name())
            return H;
        expr H_type = m_ctx.relaxed_whnf(m_ctx.infer(H));
        // H_type : @eq A a b
        expr A, a, b;
        if (!is_eq(H_type, A, a, b)) {
            lean_app_builder_trace(tout() << "failed to build lift_of_eq equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        type_context_old::tmp_locals locals(m_ctx);
        expr x         = locals.push_local(name("A"), A);
        // motive := fun x : A, a ~ x
        expr motive    = locals.mk_lambda(mk_rel(R, a, x));
        // minor : a ~ a
        expr minor     = mk_refl(R, a);
        return mk_eq_rec(motive, minor, H);
    }

    expr mk_partial_add(expr const & A) {
        level lvl = get_level(A);
        auto A_has_add = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_add_name(), {lvl}), A));
        if (!A_has_add) {
            trace_inst_failure(A, "has_add");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_add_add_name(), {lvl}), A, *A_has_add);
    }

    expr mk_partial_mul(expr const & A) {
        level lvl = get_level(A);
        auto A_has_mul = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_mul_name(), {lvl}), A));
        if (!A_has_mul) {
            trace_inst_failure(A, "has_mul");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_mul_mul_name(), {lvl}), A, *A_has_mul);
    }

    expr mk_zero(expr const & A) {
        level lvl = get_level(A);
        auto A_has_zero = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_zero_name(), {lvl}), A));
        if (!A_has_zero) {
            trace_inst_failure(A, "has_zero");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_zero_zero_name(), {lvl}), A, *A_has_zero);
    }

    expr mk_one(expr const & A) {
        level lvl = get_level(A);
        auto A_has_one = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_one_name(), {lvl}), A));
        if (!A_has_one) {
            trace_inst_failure(A, "has_one");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_one_one_name(), {lvl}), A, *A_has_one);
    }

    expr mk_partial_left_distrib(expr const & A) {
        level lvl = get_level(A);
        auto A_distrib = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_distrib_name(), {lvl}), A));
        if (!A_distrib) {
            trace_inst_failure(A, "distrib");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_left_distrib_name(), {lvl}), A, *A_distrib);
    }

    expr mk_partial_right_distrib(expr const & A) {
        level lvl = get_level(A);
        auto A_distrib = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_distrib_name(), {lvl}), A));
        if (!A_distrib) {
            trace_inst_failure(A, "distrib");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_right_distrib_name(), {lvl}), A, *A_distrib);
    }

    expr mk_ss_elim(expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e) {
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_subsingleton_elim_name(), {lvl}), A, ss_inst, old_e, new_e);
    }

    expr mk_false_rec(expr const & c, expr const & H) {
        level c_lvl = get_level(c);
        return ::lean::mk_app(mk_constant(get_false_rec_name(), {c_lvl}), c, H);
    }

    expr mk_congr_arg(expr const & f, expr const & H, bool skip_arrow_test) {
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr pi = m_ctx.relaxed_whnf(m_ctx.infer(f));
        expr A, B, lhs, rhs;
        if (!is_eq(eq, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build congr_arg, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        if (!skip_arrow_test && !is_arrow(pi)) {
            lean_app_builder_trace(tout() << "failed to build congr_arg, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        }
        B = binding_body(pi);
        level lvl_1  = get_level(A);
        level lvl_2  = get_level(B);
        return ::lean::mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
    }

    expr mk_eq_true_intro(expr const & H) {
        expr p = m_ctx.infer(H);
        return ::lean::mk_app(mk_constant(get_eq_true_intro_name()), p, H);
    }

    expr mk_eq_false_intro(expr const & H) {
        expr not_p = m_ctx.relaxed_whnf(m_ctx.infer(H));
        if (!is_pi(not_p)) {
            lean_app_builder_trace(tout() << "failed to build eq_false_intro, negation expected:\n" << not_p << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_eq_false_intro_name()), binding_domain(not_p), H);
    }

    expr mk_of_eq_true(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_true_intro_name())) {
            // of_eq_true (eq_true_intro H) == H
            return app_arg(H);
        }
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr lhs, rhs;
        if (!is_eq(eq, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build of_eq_true, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_of_eq_true_name()), lhs, H);
    }

    expr mk_not_of_eq_false(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_false_intro_name())) {
            // not_of_eq_false (eq_false_intro H) == H
            return app_arg(H);
        }
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr lhs, rhs;
        if (!is_eq(eq, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build not_of_eq_false, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_not_of_eq_false_name()), lhs, H);
    }
};

expr mk_app(type_context_old & ctx, name const & c, unsigned nargs, expr const * args, optional<transparency_mode> const & md) {
    if (md) {
        type_context_old::transparency_scope _s1(ctx, *md);
        type_context_old::zeta_scope         _s2(ctx, true);
        return app_builder(ctx).mk_app(c, nargs, args);
    } else if (!is_at_least_semireducible(ctx.mode())) {
        type_context_old::transparency_scope _s1(ctx, transparency_mode::Semireducible);
        type_context_old::zeta_scope _s2(ctx, true);
        return app_builder(ctx).mk_app(c, nargs, args);
    } else {
        return app_builder(ctx).mk_app(c, nargs, args);
    }
}

expr mk_app(type_context_old & ctx, name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
    return app_builder(ctx).mk_app(c, mask_sz, mask, args);
}

expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args) {
    return app_builder(ctx).mk_app(c, total_nargs, expl_nargs, expl_args);
}

expr mk_rel(type_context_old & ctx, name const & n, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_rel(n, lhs, rhs);
}

expr mk_eq(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_eq(lhs, rhs);
}

expr mk_iff(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_iff(lhs, rhs);
}

expr mk_heq(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_heq(lhs, rhs);
}

expr mk_refl(type_context_old & ctx, name const & relname, expr const & a) {
    return app_builder(ctx).mk_refl(relname, a);
}

expr mk_eq_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_eq_refl(a);
}

expr mk_iff_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_iff_refl(a);
}

expr mk_heq_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_heq_refl(a);
}

expr mk_symm(type_context_old & ctx, name const & relname, expr const & H) {
    return app_builder(ctx).mk_symm(relname, H);
}

expr mk_eq_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_symm(H);
}

expr mk_eq_symm(type_context_old & ctx, expr const & a, expr const & b, expr const & H) {
    return app_builder(ctx).mk_eq_symm(a, b, H);
}

expr mk_iff_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_iff_symm(H);
}

expr mk_heq_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_heq_symm(H);
}

expr mk_trans(type_context_old & ctx, name const & relname, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_trans(relname, H1, H2);
}

expr mk_eq_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_trans(H1, H2);
}

expr mk_eq_trans(type_context_old & ctx, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_trans(a, b, c, H1, H2);
}

expr mk_iff_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_iff_trans(H1, H2);
}

expr mk_heq_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_heq_trans(H1, H2);
}

expr mk_eq_rec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_rec(C, H1, H2);
}

expr mk_eq_drec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_drec(C, H1, H2);
}

expr mk_eq_of_heq(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_of_heq(H);
}

expr mk_heq_of_eq(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_heq_of_eq(H);
}

expr mk_congr_arg(type_context_old & ctx, expr const & f, expr const & H, bool skip_arrow_test) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi = ctx.relaxed_whnf(ctx.infer(f));
    expr A, B, lhs, rhs;
    if (!is_eq(eq, A, lhs, rhs)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_arg, equality expected:\n" << eq << "\n";);
        throw app_builder_exception();
    }
    if (!is_arrow(pi)) {
        if (!skip_arrow_test || !is_pi(pi)) {
            lean_app_builder_trace_core(ctx, tout() << "failed to build congr_arg, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        } else {
            B = instantiate(binding_body(pi), lhs);
        }
    } else {
        B = binding_body(pi);
    }
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, B);
    return mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
}

expr mk_congr_fun(type_context_old & ctx, expr const & H, expr const & a) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi, lhs, rhs;
    if (!is_eq(eq, pi, lhs, rhs)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_fun, equality expected:\n" << eq << "\n";);
        throw app_builder_exception();
    }
    pi = ctx.relaxed_whnf(pi);
    if (!is_pi(pi)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_fun, function expected:\n" << pi << "\n";);
        throw app_builder_exception();
    }
    expr A       = binding_domain(pi);
    expr B       = mk_lambda(binding_name(pi), binding_domain(pi), binding_body(pi), binding_info(pi));
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, mk_app(B, a));
    return mk_app({mk_constant(get_congr_fun_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, H, a});
}

expr mk_congr(type_context_old & ctx, expr const & H1, expr const & H2, bool skip_arrow_test) {
    expr eq1 = ctx.relaxed_whnf(ctx.infer(H1));
    expr eq2 = ctx.relaxed_whnf(ctx.infer(H2));
    expr pi, lhs1, rhs1;
    if (!is_eq(eq1, pi, lhs1, rhs1)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr, equality expected:\n" << eq1 << "\n";);
        throw app_builder_exception();
    }
    expr lhs2, rhs2;
    if (!is_eq(eq2, lhs2, rhs2)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr, equality expected:\n" << eq2 << "\n";);
        throw app_builder_exception();
    }
    pi = ctx.relaxed_whnf(pi);
    expr A, B;
    if (!is_arrow(pi)) {
        if (!skip_arrow_test || !is_pi(pi)) {
            lean_app_builder_trace_core(ctx, tout() << "failed to build congr, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        } else {
            B = instantiate(binding_body(pi), lhs2);
        }
    } else {
        B = binding_body(pi);
    }
    A            = binding_domain(pi);
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, B);
    return mk_app({mk_constant(get_congr_name(), {lvl_1, lvl_2}), A, B, lhs1, rhs1, lhs2, rhs2, H1, H2});
}

expr mk_funext(type_context_old & ctx, expr const & lam_pf) {
    // TODO(dhs): efficient version
    return mk_app(ctx, get_funext_name(), lam_pf);
}

expr lift_from_eq(type_context_old & ctx, name const & R, expr const & H) {
    return app_builder(ctx).lift_from_eq(R, H);
}

expr mk_iff_false_intro(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_iff_false_intro_name(), {H});
}

expr mk_iff_true_intro(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_iff_true_intro_name(), {H});
}

expr mk_eq_false_intro(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_false_intro(H);
}

expr mk_eq_true_intro(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_true_intro(H);
}

expr mk_not_of_eq_false(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_not_of_eq_false(H);
}

expr mk_of_eq_true(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_of_eq_true(H);
}

expr mk_neq_of_not_iff(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_neq_of_not_iff_name(), {H});
}

expr mk_not_of_iff_false(type_context_old & ctx, expr const & H) {
    if (is_constant(get_app_fn(H), get_iff_false_intro_name())) {
        // not_of_iff_false (iff_false_intro H) == H
        return app_arg(H);
    }
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_not_of_iff_false_name(), 2, {H});
}

expr mk_of_iff_true(type_context_old & ctx, expr const & H) {
    if (is_constant(get_app_fn(H), get_iff_true_intro_name())) {
        // of_iff_true (iff_true_intro H) == H
        return app_arg(H);
    }
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_of_iff_true_name(), {H});
}

expr mk_false_of_true_iff_false(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_false_of_true_iff_false_name(), {H});
}

expr mk_false_of_true_eq_false(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_false_of_true_eq_false_name(), {H});
}

expr mk_not(type_context_old & ctx, expr const & H) {
    // TODO(dhs): implement custom version if bottleneck.
    return mk_app(ctx, get_not_name(), {H});
}

expr mk_absurd(type_context_old & ctx, expr const & Hp, expr const & Hnp, expr const & b) {
    return mk_app(ctx, get_absurd_name(), {b, Hp, Hnp});
}

expr mk_partial_add(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_add(A);
}

expr mk_partial_mul(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_mul(A);
}

expr mk_zero(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_zero(A);
}

expr mk_one(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_one(A);
}

expr mk_partial_left_distrib(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_left_distrib(A);
}

expr mk_partial_right_distrib(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_right_distrib(A);
}

expr mk_ss_elim(type_context_old & ctx, expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e) {
    return app_builder(ctx).mk_ss_elim(A, ss_inst, old_e, new_e);
}

expr mk_false_rec(type_context_old & ctx, expr const & c, expr const & H) {
    return app_builder(ctx).mk_false_rec(c, H);
}

expr mk_ite(type_context_old & ctx, expr const & c, expr const & t, expr const & e) {
    bool mask[5] = {true, false, false, true, true};
    expr args[3] = {c, t, e};
    return mk_app(ctx, get_ite_name(), 5, mask, args);
}

expr mk_id(type_context_old & ctx, expr const & type, expr const & h) {
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_name(), {lvl}), type, h);
}

expr mk_id(type_context_old & ctx, expr const & h) {
    return mk_id(ctx, ctx.infer(h), h);
}

expr mk_id_rhs(type_context_old & ctx, expr const & h) {
    expr type = ctx.infer(h);
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_rhs_name(), {lvl}), type, h);
}

expr mk_id_delta(type_context_old & ctx, expr const & h) {
    expr type = ctx.infer(h);
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_delta_name(), {lvl}), type, h);
}

static bool is_eq_trans(expr const & h, expr & h1, expr & h2) {
    if (is_app_of(h, get_eq_trans_name(), 6)) {
        h1 = app_arg(app_fn(h));
        h2 = app_arg(h);
        return true;
    } else {
        return false;
    }
}

static bool is_propext(expr const & h, expr & h1) {
    if (is_app_of(h, get_propext_name(), 3)) {
        h1 = app_arg(h);
        return true;
    } else {
        return false;
    }
}

static bool is_eq_self_iff_true(expr const & h, expr & t) {
    if (is_app_of(h, get_eq_self_iff_true_name(), 2)) {
        t = app_arg(h);
        return true;
    } else {
        return false;
    }
}

expr mk_eq_mpr(type_context_old & ctx, expr const & h1, expr const & h2) {
    /*
       eq.mpr (eq.trans H (propext (@eq_self_iff_true t))) h2
       ==>
       eq.mpr H (eq.refl t)

       Remark: note that (h2 : true)
    */
    expr H, P, E, t;
    if (is_eq_trans(h1, H, P) && is_propext(P, E) && is_eq_self_iff_true(E, t)) {
        return mk_app(ctx, get_eq_mpr_name(), H, mk_eq_refl(ctx, t));
    }
    return mk_app(ctx, get_eq_mpr_name(), h1, h2);
}

expr mk_iff_mpr(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_iff_mpr_name(), h1, h2);
}

expr mk_eq_mp(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_eq_mp_name(), h1, h2);
}

expr mk_iff_mp(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_iff_mp_name(), h1, h2);
}

void initialize_app_builder() {
    register_trace_class("app_builder");
    register_thread_local_reset_fn([]() { get_abch().clear(); });
}
void finalize_app_builder() {}
}




// ========== expr_unsigned_map.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"

namespace lean {
/* pair (expression, unsigned int) with cached hash code */
struct expr_unsigned {
    expr         m_expr;
    unsigned     m_nargs;
    unsigned     m_hash;
    expr_unsigned(expr const & fn, unsigned nargs):
        m_expr(fn), m_nargs(nargs), m_hash(hash(m_expr.hash(), m_nargs)) {}
};

struct expr_unsigned_hash_fn {
    unsigned operator()(expr_unsigned const & k) const { return k.m_hash; }
};

struct expr_unsigned_eq_fn {
    bool operator()(expr_unsigned const & k1, expr_unsigned const & k2) const {
        return k1.m_expr == k2.m_expr && k1.m_nargs == k2.m_nargs;
    }
};

/* mapping from (expr, unsigned) -> T */
template<typename T>
using expr_unsigned_map = typename std::unordered_map<expr_unsigned, T, expr_unsigned_hash_fn, expr_unsigned_eq_fn>;
}




// ========== user_recursors.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Information for a user defined recursor */
class recursor_info {
    name                     m_recursor;
    name                     m_type_name;
    list<unsigned>           m_universe_pos; // position of the recursor universe level parameters.
    bool                     m_dep_elim;
    bool                     m_recursive;
    unsigned                 m_num_args; // total number of arguments
    unsigned                 m_major_pos;
    // if param is <none>, then it should be resolved by type class resolution
    list<optional<unsigned>> m_params_pos;  // position of the recursor parameters in the major premise
    list<unsigned>           m_indices_pos; // position of the recursor indices in the major premise
    list<bool>               m_produce_motive; // "bit-map" indicating whether the i-th element is true, if
                                               // the i-th minor premise produces the motive

public:
    recursor_info(name const & r, name const & I, list<unsigned> const & univ_pos,
                  bool dep_elim, bool is_rec, unsigned num_args, unsigned major_pos,
                  list<optional<unsigned>> const & params_pos, list<unsigned> const & indices_pos,
                  list<bool> const & produce_motive);
    recursor_info();

    /** \brief Return a list containing the position of the recursor universe parameters in the major premise.
        The value get_motive_univ_idx() is used to identify the position of the motive universe. */
    list<unsigned> const & get_universe_pos() const { return m_universe_pos; }

    static unsigned get_motive_univ_idx() { return static_cast<unsigned>(-1); }

    name const & get_name() const { return m_recursor; }
    name const & get_type_name() const { return m_type_name; }
    unsigned get_num_args() const { return m_num_args; }
    unsigned get_num_params() const { return length(m_params_pos); }
    unsigned get_num_indices() const { return length(m_indices_pos); }
    unsigned get_motive_pos() const { return get_num_params(); }
    unsigned get_first_index_pos() const { return m_major_pos - get_num_indices(); }
    unsigned get_major_pos() const { return m_major_pos; }
    list<optional<unsigned>> const & get_params_pos() const { return m_params_pos; }
    /** \brief Return position of the recursor indices in the major premise. */
    list<unsigned> const & get_indices_pos() const { return m_indices_pos; }
    list<bool> const & get_produce_motive() const { return m_produce_motive; }
    bool has_dep_elim() const { return m_dep_elim; }
    bool is_recursive() const { return m_recursive; }
    bool is_minor(unsigned pos) const;
    unsigned get_num_minors() const;

    void write(serializer & s) const;
    static recursor_info read(deserializer & d);
};

environment add_user_recursor(environment const & env, name const & r, optional<unsigned> const & major_pos,
                              bool persistent);
recursor_info get_recursor_info(environment const & env, name const & r);
list<name> get_recursors_for(environment const & env, name const & I);
bool is_user_defined_recursor(environment const & env, name const & r);

class has_recursors_pred {
    name_map<list<name>>    m_type2recursors;
public:
    has_recursors_pred(environment const & env);
    bool operator()(name const & n) const { return m_type2recursors.contains(n); }
};

void initialize_user_recursors();
void finalize_user_recursors();
}




// ========== user_recursors.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "kernel/find_fn.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/attribute_manager.h"

namespace lean {
bool recursor_info::is_minor(unsigned pos) const {
    if (pos <= get_motive_pos())
        return false;
    if (get_first_index_pos() <= pos && pos <= m_major_pos)
        return false;
    return true;
}

unsigned recursor_info::get_num_minors() const {
    unsigned r = m_num_args;
    lean_assert(r >= get_motive_pos() + 1);
    r -= (get_motive_pos() + 1);
    lean_assert(m_major_pos >= get_first_index_pos());
    lean_assert(r >= m_major_pos - get_first_index_pos() + 1);
    r -= (m_major_pos - get_first_index_pos() + 1);
    return r;
}

recursor_info::recursor_info(name const & r, name const & I, list<unsigned> const & univ_pos,
                             bool dep_elim, bool is_rec, unsigned num_args, unsigned major_pos,
                             list<optional<unsigned>> const & params_pos, list<unsigned> const & indices_pos,
                             list<bool> const & produce_motive):
    m_recursor(r), m_type_name(I), m_universe_pos(univ_pos), m_dep_elim(dep_elim), m_recursive(is_rec),
    m_num_args(num_args), m_major_pos(major_pos), m_params_pos(params_pos), m_indices_pos(indices_pos),
    m_produce_motive(produce_motive) {}
recursor_info::recursor_info() {}

void recursor_info::write(serializer & s) const {
    s << m_recursor << m_type_name << m_dep_elim << m_recursive << m_num_args << m_major_pos;
    write_list(s, m_universe_pos);
    write_list(s, m_params_pos);
    write_list(s, m_indices_pos);
    write_list(s, m_produce_motive);
}

recursor_info recursor_info::read(deserializer & d) {
    recursor_info info;
    d >> info.m_recursor >> info.m_type_name >> info.m_dep_elim >> info.m_recursive
      >> info.m_num_args >> info.m_major_pos;
    info.m_universe_pos   = read_list<unsigned>(d);
    info.m_params_pos     = read_list<optional<unsigned>>(d);
    info.m_indices_pos    = read_list<unsigned>(d);
    info.m_produce_motive = read_list<bool>(d);
    return info;
}

static void throw_invalid_motive(expr const & C) {
    throw exception(sstream() << "invalid user defined recursor, motive '" << C
                    << "' must have a type of the form (C : Pi (i : B A), I A i -> Type), "
                    "where A is (possibly empty) sequence of bound variables (aka parameters), "
                    "(i : B A) is a (possibly empty) telescope (aka indices), "
                    "and I is a constant");
}

recursor_info mk_recursor_info(environment const & env, name const & r, optional<unsigned> const & _given_major_pos) {
    /* The has_given_major_pos/given_major_pos hack is used to workaround a g++ false warning.
       Note that the pragma
          #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
       doesn't fix the problem here since the uninitialized variable is reported in an inlined buffer method.
       I think it would be even hackier to put the pragma at buffer.h */
    bool has_given_major_pos = static_cast<bool>(_given_major_pos);
    unsigned given_major_pos = 0;
    if (_given_major_pos) given_major_pos = *_given_major_pos;
    if (auto I = inductive::is_elim_rule(env, r)) {
        unsigned num_univ_params = env.get(*I).get_num_univ_params();
        list<unsigned> universe_pos = mk_list_range(0, num_univ_params);
        if (env.get(name(*I, "rec")).get_num_univ_params() != num_univ_params)
            universe_pos = cons(recursor_info::get_motive_univ_idx(), universe_pos);
        bool is_rec                = is_recursive_datatype(env, *I);
        unsigned major_pos         = *inductive::get_elim_major_idx(env, r);
        unsigned num_indices       = *inductive::get_num_indices(env, *I);
        unsigned num_params        = *inductive::get_num_params(env, *I);
        unsigned num_minors        = *inductive::get_num_minor_premises(env, *I);
        unsigned num_args          = num_params + 1 /* motive */ + num_minors + num_indices + 1 /* major */;
        list<bool> produce_motive;
        for (unsigned i = 0; i < num_minors; i++)
            produce_motive = cons(true, produce_motive);
        list<optional<unsigned>> params_pos = map2<optional<unsigned>>(mk_list_range(0, num_params),
                                                                       [](unsigned i) { return optional<unsigned>(i); });
        list<unsigned> indices_pos = mk_list_range(num_params, num_params + num_indices);
        return recursor_info(r, *I, universe_pos, inductive::has_dep_elim(env, *I), is_rec,
                             num_args, major_pos, params_pos, indices_pos, produce_motive);
    } else if (is_aux_recursor(env, r) &&
               (strcmp(r.get_string(), "cases_on") == 0 ||
                strcmp(r.get_string(), "dcases_on") == 0 ||
                strcmp(r.get_string(), "drec_on") == 0 ||
                strcmp(r.get_string(), "rec_on") == 0   ||
                strcmp(r.get_string(), "brec_on") == 0)) {
        name I = r.get_prefix();
        unsigned num_indices  = *inductive::get_num_indices(env, I);
        unsigned num_params   = *inductive::get_num_params(env, I);
        has_given_major_pos   = true;
        given_major_pos       = num_params + 1 /* motive */ + num_indices;
    }
    declaration d = env.get(r);
    type_checker tc(env);
    buffer<expr> tele;
    expr rtype    = to_telescope(tc, d.get_type(), tele);
    buffer<expr> C_args;
    expr C        = get_app_args(rtype, C_args);
    if (!is_local(C) || !std::all_of(C_args.begin(), C_args.end(), is_local)) {
        throw exception("invalid user defined recursor, result type must be of the form (C t), "
                        "where C is a bound variable, and t is a (possibly empty) sequence of bound variables");
    }

    // Compute number of parameters.
    // We assume a parameter is anything that occurs before the motive.
    unsigned num_params  = 0;
    for (expr const & x : tele) {
        if (mlocal_name(x) == mlocal_name(C))
            break;
        num_params++;
    }

    // Locate major premise, and check whether the recursor supports dependent elimination or not.
    expr major;
    unsigned major_pos = 0;
    bool dep_elim;
    if (has_given_major_pos) {
        if (given_major_pos >= tele.size())
            throw exception(sstream() << "invalid user defined recursor, invalid major premise position, "
                            "recursor has only " << tele.size() << "arguments");
        major_pos = given_major_pos;
        major     = tele[major_pos];
        if (!C_args.empty() && tc.is_def_eq(C_args.back(), major))
            dep_elim = true;
        else
            dep_elim = false;
    } else if (C_args.empty()) {
        throw exception(sstream() << "invalid user defined recursor, '" << r << "' does not support dependent elimination, "
                        << "and position of the major premise was not specified "
                        << "(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
    } else {
        major    = C_args.back();
        dep_elim = true;
        for (expr const & x : tele) {
            if (tc.is_def_eq(x, major))
                break;
            major_pos++;
        }
    }

    // Number of indices
    unsigned num_indices = C_args.size();
    if (dep_elim)
        num_indices--; // when we have dependent elimination, the last element is the major premise.
    if (major_pos < num_indices)
        throw exception(sstream() << "invalid user defined recursor, indices must occur before major premise '"
                        << major << "'");

    buffer<expr> I_args;
    expr I = get_app_args(mlocal_type(major), I_args);
    if (!is_constant(I)) {
        throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                        << "' must be for the form (I ...), where I is a constant");
    }

    // Store position of the recursor parameters in the major premise.
    buffer<optional<unsigned>> params_pos;
    for (unsigned i = 0; i < num_params; i++) {
        expr const & A = tele[i];
        unsigned j = 0;
        for (; j < I_args.size(); j++) {
            if (tc.is_def_eq(I_args[j], A))
                break;
        }
        if (j == I_args.size()) {
            if (local_info(tele[i]).is_inst_implicit()) {
                params_pos.push_back(optional<unsigned>());
            } else {
                throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                                << "' does not contain the recursor parameter '" << A << "'");
            }
        } else {
            params_pos.push_back(optional<unsigned>(j));
        }
    }

    // Store position of the recursor indices in the major premise
    buffer<unsigned> indices_pos;
    for (unsigned i = major_pos - num_indices; i < major_pos; i++) {
        expr const & idx = tele[i];
        unsigned j = 0;
        for (; j < I_args.size(); j++) {
            if (tc.is_def_eq(I_args[j], idx))
                break;
        }
        if (j == I_args.size()) {
            throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                            << "' does not contain the recursor index '" << idx << "'");
        }
        indices_pos.push_back(j);
    }


    buffer<expr> C_tele;
    expr C_rtype  = to_telescope(tc, mlocal_type(C), C_tele);
    if (!is_sort(C_rtype) || C_tele.size() != C_args.size()) {
        throw_invalid_motive(C);
    }

    level motive_lvl = sort_level(C_rtype);
    // Remark: if we are in the standard environment, then the motive may be a proposition, and be fixed at 0.
    // The following pragma is for avoiding gcc bogus warning
    if (!is_zero(motive_lvl)) {
        if (!is_param(motive_lvl)) {
            throw exception("invalid user defined recursor, "
                            "motive result sort must be Prop or Type.{l} where l is a universe parameter");
        }
    }

    // A universe parameter must occur in the major premise or in the motive
    buffer<unsigned> univ_param_pos;
    for (name const & p : d.get_univ_params()) {
        if (!is_zero(motive_lvl) && param_id(motive_lvl) == p) {
            univ_param_pos.push_back(recursor_info::get_motive_univ_idx());
        } else {
            bool found = false;
            unsigned i = 0;
            for (level const & l : const_levels(I)) {
                if (is_param(l) && param_id(l) == p) {
                    univ_param_pos.push_back(i);
                    found = true;
                    break;
                }
                i++;
            }
            if (!found) {
                throw exception(sstream() << "invalid user defined recursor, major premise '"
                                << major << "' does not contain universe parameter '" << p << "'");
            }
        }
    }

    buffer<bool> produce_motive;
    unsigned nparams  = params_pos.size();
    unsigned nindices = indices_pos.size();
    bool is_rec       = false;
    for (unsigned i = nparams+1; i < tele.size(); i++) {
        if (i < major_pos - nindices || i > major_pos) {
            // i is a minor premise
            buffer<expr> minor_args;
            expr res = get_app_fn(to_telescope(tc, mlocal_type(tele[i]), minor_args));
            if (!is_rec) {
                for (expr const & minor_arg : minor_args) {
                    lean_assert(is_local(minor_arg));
                    if (find(mlocal_type(minor_arg), [&](expr const & e, unsigned) {
                                return is_local(e) && mlocal_name(C) == mlocal_name(e);
                            })) {
                        is_rec = true;
                        break;
                    }
                }
            }
            if (is_local(res) && mlocal_name(C) == mlocal_name(res)) {
                produce_motive.push_back(true);
            } else {
                produce_motive.push_back(false);
            }
        }
    }

    return recursor_info(r, const_name(I), to_list(univ_param_pos), dep_elim, is_rec, tele.size(), major_pos,
                         to_list(params_pos), to_list(indices_pos), to_list(produce_motive));
}

struct recursor_state {
    name_map<recursor_info> m_recursors;
    name_map<list<name>>    m_type2recursors;

    void insert(recursor_info const & info) {
        m_recursors.insert(info.get_name(), info);
        if (auto l = m_type2recursors.find(info.get_type_name())) {
            m_type2recursors.insert(info.get_type_name(),
                                    cons(info.get_name(),
                                         filter(*l, [&](name const & n) { return n != info.get_name(); })));
        } else {
            m_type2recursors.insert(info.get_type_name(), to_list(info.get_name()));
        }
    }
};

struct recursor_config {
    typedef recursor_state  state;
    typedef recursor_info   entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e);
    }
    static const char * get_serialization_key() { return "UREC"; }
    static void  write_entry(serializer & s, entry const & e) {
        e.write(s);
    }
    static entry read_entry(deserializer & d) {
        return recursor_info::read(d);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.get_name().hash());
    }
};

template class scoped_ext<recursor_config>;
typedef scoped_ext<recursor_config> recursor_ext;

environment add_user_recursor(environment const & env, name const & r, optional<unsigned> const & major_pos,
                              bool persistent) {
    if (inductive::is_elim_rule(env, r))
        throw exception(sstream() << "invalid user defined recursor, '" << r << "' is a builtin recursor");
    recursor_info info = mk_recursor_info(env, r, major_pos);
    return recursor_ext::add_entry(env, get_dummy_ios(), info, persistent);
}

recursor_info get_recursor_info(environment const & env, name const & r) {
    if (auto info = recursor_ext::get_state(env).m_recursors.find(r))
        return *info;
    return mk_recursor_info(env, r, optional<unsigned>());
}

list<name> get_recursors_for(environment const & env, name const & I) {
    if (auto l = recursor_ext::get_state(env).m_type2recursors.find(I))
        return *l;
    else
        return list<name>();
}

bool is_user_defined_recursor(environment const & env, name const & r) {
    return recursor_ext::get_state(env).m_recursors.find(r) != nullptr;
}

has_recursors_pred::has_recursors_pred(environment const & env):
    m_type2recursors(recursor_ext::get_state(env).m_type2recursors) {}

static indices_attribute const & get_recursor_attribute() {
    return static_cast<indices_attribute const &>(get_system_attribute("recursor"));
}

void initialize_user_recursors() {
    recursor_ext::initialize();
    register_system_attribute(indices_attribute("recursor", "user defined recursor",
                                                [](environment const & env, io_state const &, name const & n, unsigned,
                                                   bool persistent) {
                                                    auto const & data = *get_recursor_attribute().get(env, n);
                                                    if (data.m_idxs && tail(data.m_idxs))
                                                        throw exception(sstream()
                                                                                << "invalid [recursor] declaration, expected at most one parameter");
                                                    return add_user_recursor(env, n, head_opt(data.m_idxs), persistent);
                                                }));
}

void finalize_user_recursors() {
    recursor_ext::finalize();
}
}




// ========== arith_instance.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/numerics/mpq.h"
#include "library/type_context.h"

namespace lean {
/*
   Given a type `α`, this structure stores instances and partial
   applications for arithmetic-related instances.  The data is
   constructed "on demand" by the helper class `arith_instance`.

   The current design allows multiple `arith_instance` to share
   the same `arith_instance_info` IF they are all in the same
   execution thread.

   This code is currently used by
   - norm_num (numeric normalizer)
     Remark: the proofs created by `norm_num` try to use the most general
     structure for applying each auxiliary lemma. In retrospect, I think this is overkill.
     In practice, `norm_num` is used only for: `semiring`, `linear_ordered_semiring`, `ring`, `linear_ordered_ring`,
     `field`, `linerar_ordered_field`. Moreover, we want to use the unbundled approach for structures
     such as `monoid` and `group`.

   - It was also used by mpq_macro (which is used only by the SMT2 frontend)
     Remark: the SMT2 frontend was originally built to test the performance of
     a blast tactic that Leo and Daniel were developing. This tactic does not
     exist anymore. Moreover, SMT2 benchmarks are far from ideal for testing
     a system like Lean. AFAICT, nobody uses the SMT2 frontend.
     So, we have deleted `mpq_macro` and the SMT2 frontend. Motivation: less stuff to maintain.

   Plan:

   - Reduce the number of structures used by `norm_num`. We just need to change
     the lemmas used by `norm_num` and adjust the C++ code. An additional motivation
     is that we can replace semi-bundled type classes such as `monoid` and `group` with
     unbundled type classes such as `is_monoid` and `is_group` that are parametrized
     by operations too.
*/
class arith_instance_info {
    friend class arith_instance;
    expr   m_type;
    levels m_levels;

    /* Partial applications */
    optional<expr> m_zero, m_one;
    optional<expr> m_add, m_sub, m_neg;
    optional<expr> m_mul, m_div, m_inv;
    optional<expr> m_lt, m_le;
    optional<expr> m_bit0, m_bit1;

    /* Structures */
    optional<expr> m_partial_order;
    optional<expr> m_add_comm_semigroup;
    optional<expr> m_monoid, m_add_monoid;
    optional<expr> m_add_group, m_add_comm_group;
    optional<expr> m_distrib, m_mul_zero_class;
    optional<expr> m_semiring, m_linear_ordered_semiring;
    optional<expr> m_ring, m_linear_ordered_ring;
    optional<expr> m_field;
public:
    arith_instance_info(expr const & type, level const & lvl):m_type(type), m_levels(lvl) {}
};

typedef std::shared_ptr<arith_instance_info> arith_instance_info_ptr;
arith_instance_info_ptr mk_arith_instance_info(expr const & type, level const & lvl);

class arith_instance {
    type_context_old *          m_ctx;
    arith_instance_info_ptr m_info;

    expr mk_structure(name const & s, optional<expr> & r);
    expr mk_op(name const & op, name const & s, optional<expr> & r);

    expr mk_pos_num(mpz const & n);

public:
    arith_instance(type_context_old & ctx, arith_instance_info_ptr const & info):m_ctx(&ctx), m_info(info) {}
    arith_instance(type_context_old & ctx, expr const & type, level const & level);
    arith_instance(type_context_old & ctx, expr const & type);
    arith_instance(arith_instance_info_ptr const & info):m_ctx(nullptr), m_info(info) {}
    arith_instance(type_context_old & ctx):m_ctx(&ctx) {}

    void set_info(arith_instance_info_ptr const & info) { m_info = info; }
    /* The following method creates a fresh `arith_instance_info` for the given type.

       Missing optimization: it should do nothing if `type` is and `m_info->m_type`
       are equal. */
    void set_type(expr const & type);

    expr const & get_type() const { return m_info->m_type; }
    levels const & get_levels() const { return m_info->m_levels; }

    bool is_nat();

    expr mk_zero();
    expr mk_one();
    expr mk_add();
    expr mk_sub();
    expr mk_neg();
    expr mk_mul();
    expr mk_div();
    expr mk_inv();
    expr mk_lt();
    expr mk_le();

    expr mk_bit0();
    expr mk_bit1();

    expr mk_has_zero() { return app_arg(mk_zero()); }
    expr mk_has_one() { return app_arg(mk_one()); }
    expr mk_has_add() { return app_arg(mk_add()); }
    expr mk_has_sub() { return app_arg(mk_sub()); }
    expr mk_has_neg() { return app_arg(mk_neg()); }
    expr mk_has_mul() { return app_arg(mk_mul()); }
    expr mk_has_div() { return app_arg(mk_div()); }
    expr mk_has_inv() { return app_arg(mk_inv()); }
    expr mk_has_lt() { return app_arg(mk_lt()); }
    expr mk_has_le() { return app_arg(mk_le()); }

    expr mk_partial_order();
    expr mk_add_comm_semigroup();
    expr mk_monoid();
    expr mk_add_monoid();
    expr mk_add_group();
    expr mk_add_comm_group();
    expr mk_distrib();
    expr mk_mul_zero_class();
    expr mk_semiring();
    expr mk_linear_ordered_semiring();
    expr mk_ring();
    expr mk_linear_ordered_ring();
    expr mk_field();

    expr mk_num(mpz const & n);
    expr mk_num(mpq const & n);

    optional<mpq> eval(expr const & e);
};
};




// ========== arith_instance.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/arith_instance.h"
#include "library/num.h"

namespace lean {
// TODO(Leo): pre compute arith_instance_info for nat, int and real

arith_instance_info_ptr mk_arith_instance_info(expr const & type, level const & lvl) {
    return std::make_shared<arith_instance_info>(type, lvl);
}

arith_instance::arith_instance(type_context_old & ctx, expr const & type, level const & level):
    m_ctx(&ctx), m_info(mk_arith_instance_info(type, level)) {}

arith_instance::arith_instance(type_context_old & ctx, expr const & type):
    m_ctx(&ctx) {
    set_type(type);
}

void arith_instance::set_type(expr const & type) {
    if (optional<level> lvl = dec_level(get_level(*m_ctx, type)))
        m_info = mk_arith_instance_info(type, *lvl);
    else
        throw exception("failed to infer universe level");
}

expr arith_instance::mk_op(name const & op, name const & s, optional<expr> & r) {
    if (r) return *r;
    if (m_ctx) {
        expr inst_type = mk_app(mk_constant(s, m_info->m_levels), m_info->m_type);
        if (auto inst = m_ctx->mk_class_instance(inst_type)) {
            r = mk_app(mk_constant(op, m_info->m_levels), m_info->m_type, *inst);
            return *r;
        }
    }
    throw exception(sstream() << "failed to synthesize '" << s << "'");
}

expr arith_instance::mk_structure(name const & s, optional<expr> & r) {
    if (r) return *r;
    if (m_ctx) {
        expr inst_type = mk_app(mk_constant(s, m_info->m_levels), m_info->m_type);
        if (auto inst = m_ctx->mk_class_instance(inst_type)) {
            r = *inst;
            return *r;
        }
    }
    throw exception(sstream() << "failed to synthesize '" << s << "'");
}

expr arith_instance::mk_bit1() {
    if (!m_info->m_bit1)
        m_info->m_bit1 = mk_app(mk_constant(get_bit1_name(), m_info->m_levels), m_info->m_type, mk_has_one(), mk_has_add());
    return *m_info->m_bit1;
}

expr arith_instance::mk_zero() { return mk_op(get_has_zero_zero_name(), get_has_zero_name(), m_info->m_zero); }
expr arith_instance::mk_one() { return mk_op(get_has_one_one_name(), get_has_one_name(), m_info->m_one); }
expr arith_instance::mk_add() { return mk_op(get_has_add_add_name(), get_has_add_name(), m_info->m_add); }
expr arith_instance::mk_sub() { return mk_op(get_has_sub_sub_name(), get_has_sub_name(), m_info->m_sub); }
expr arith_instance::mk_neg() { return mk_op(get_has_neg_neg_name(), get_has_neg_name(), m_info->m_neg); }
expr arith_instance::mk_mul() { return mk_op(get_has_mul_mul_name(), get_has_mul_name(), m_info->m_mul); }
expr arith_instance::mk_div() { return mk_op(get_has_div_div_name(), get_has_div_name(), m_info->m_div); }
expr arith_instance::mk_inv() { return mk_op(get_has_inv_inv_name(), get_has_inv_name(), m_info->m_inv); }
expr arith_instance::mk_lt() { return mk_op(get_has_lt_lt_name(), get_has_lt_name(), m_info->m_lt); }
expr arith_instance::mk_le() { return mk_op(get_has_le_le_name(), get_has_le_name(), m_info->m_le); }

expr arith_instance::mk_bit0() { return mk_op(get_bit0_name(), get_has_add_name(), m_info->m_bit0); }

expr arith_instance::mk_partial_order() { return mk_structure(get_partial_order_name(), m_info->m_partial_order); }
expr arith_instance::mk_add_comm_semigroup() { return mk_structure(get_add_comm_semigroup_name(), m_info->m_add_comm_semigroup); }
expr arith_instance::mk_monoid() { return mk_structure(get_monoid_name(), m_info->m_monoid); }
expr arith_instance::mk_add_monoid() { return mk_structure(get_add_monoid_name(), m_info->m_add_monoid); }
expr arith_instance::mk_add_group() { return mk_structure(get_add_group_name(), m_info->m_add_group); }
expr arith_instance::mk_add_comm_group() { return mk_structure(get_add_comm_group_name(), m_info->m_add_comm_group); }
expr arith_instance::mk_distrib() { return mk_structure(get_distrib_name(), m_info->m_distrib); }
expr arith_instance::mk_mul_zero_class() { return mk_structure(get_mul_zero_class_name(), m_info->m_mul_zero_class); }
expr arith_instance::mk_semiring() { return mk_structure(get_semiring_name(), m_info->m_semiring); }
expr arith_instance::mk_linear_ordered_semiring() { return mk_structure(get_linear_ordered_semiring_name(), m_info->m_linear_ordered_semiring); }
expr arith_instance::mk_ring() { return mk_structure(get_ring_name(), m_info->m_ring); }
expr arith_instance::mk_linear_ordered_ring() { return mk_structure(get_linear_ordered_ring_name(), m_info->m_linear_ordered_ring); }
expr arith_instance::mk_field() { return mk_structure(get_field_name(), m_info->m_field); }

expr arith_instance::mk_pos_num(mpz const & n) {
    lean_assert(n > 0);
    if (n == 1)
        return mk_one();
    else if (n % mpz(2) == 1)
        return mk_app(mk_bit1(), mk_pos_num(n/2));
    else
        return mk_app(mk_bit0(), mk_pos_num(n/2));
}

expr arith_instance::mk_num(mpz const & n) {
    if (n < 0) {
        return mk_app(mk_neg(), mk_pos_num(0 - n));
    } else if (n == 0) {
        return mk_zero();
    } else {
        return mk_pos_num(n);
    }
}

expr arith_instance::mk_num(mpq const & q) {
    mpz numer = q.get_numerator();
    mpz denom = q.get_denominator();
    lean_assert(denom >= 0);
    if (denom == 1 || numer == 0) {
        return mk_num(numer);
    } else if (numer > 0) {
        return mk_app(mk_div(), mk_num(numer), mk_num(denom));
    } else {
        return mk_app(mk_neg(), mk_app(mk_div(), mk_num(neg(numer)), mk_num(denom)));
    }
}

bool arith_instance::is_nat() {
    return is_constant(m_info->m_type, get_nat_name());
}

optional<mpq> arith_instance::eval(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f)) {
        throw exception("cannot find num of nonconstant");
    } else if (const_name(f) == get_has_add_add_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))
            return optional<mpq>(*r1 + *r2);
    } else if (const_name(f) == get_has_mul_mul_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))
            return optional<mpq>(*r1 * *r2);
    } else if (const_name(f) == get_has_sub_sub_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))  {
            if (is_nat() && *r2 > *r1)
                return optional<mpq>(0);
            else
                return optional<mpq>(*r1 - *r2);
        }
    } else if (const_name(f) == get_has_div_div_name() && args.size() == 4) {
        if (auto r1 = eval(args[2]))
        if (auto r2 = eval(args[3]))  {
            if (is_nat())
                return optional<mpq>(); // not supported yet
            else if (*r2 == 0)
                return optional<mpq>(); // division by zero, add support for x/0 = 0
            else
                return optional<mpq>(*r1 / *r2);
        }
    } else if (const_name(f) == get_has_neg_neg_name() && args.size() == 3) {
        if (auto r1 = eval(args[2]))
            return optional<mpq>(neg(*r1));
    } else if (auto r = to_num(e)) {
        return optional<mpq>(*r);
    }
    return optional<mpq>();
}
}




// ========== num.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/numerics/mpz.h"
#include "kernel/environment.h"

namespace lean {
bool is_const_app(expr const &, name const &, unsigned);

/** \brief Return true iff the given expression encodes a numeral. */
bool is_num(expr const & e);

/** \brief Return true iff is_num(e) or \c e is of the form (- e') where to_num(e') */
bool is_signed_num(expr const & e);

bool is_zero(expr const & e);
bool is_one(expr const & e);
optional<expr> is_bit0(expr const & e);
optional<expr> is_bit1(expr const & e);
optional<expr> is_neg(expr const & e);

/** \brief Return true iff \c n is zero, one, bit0 or bit1 */
bool is_numeral_const_name(name const & n);

/** Unfold \c e it is is_zero, is_one, is_bit0 or is_bit1 application */
optional<expr> unfold_num_app(environment const & env, expr const & e);

/** \brief If the given expression encodes a numeral, then convert it back to mpz numeral.
    \see from_num */
optional<mpz> to_num(expr const & e);

/** \brief Return true iff n is zero/one/has_zero.zero/has_one.one.
    These constants are used to encode numerals, and some tactics may have to treat them in a special way.

    \remark This kind of hard-coded solution is not ideal. One alternative solution is to have yet another
    annotation to let user mark constants that should be treated in a different way by some tactics. */
bool is_num_leaf_constant(name const & n);

/** \brief Encode \c n as an expression using bit0/bit1/one/zero constants */
expr to_nat_expr(mpz const & n);

void initialize_num();
void finalize_num();
}




// ========== num.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/num.h"
#include "library/util.h"
#include "library/constants.h"

namespace lean {
bool is_const_app(expr const & e, name const & n, unsigned nargs) {
    expr const & f = get_app_fn(e);
    return is_constant(f) && const_name(f) == n && get_app_num_args(e) == nargs;
}

bool is_zero(expr const & e) {
    return
        is_const_app(e, get_has_zero_zero_name(), 2) ||
        is_constant(e, get_nat_zero_name());
}

bool is_one(expr const & e) {
    return
        is_const_app(e, get_has_one_one_name(), 2) ||
        (is_const_app(e, get_nat_succ_name(), 1) && is_zero(app_arg(e)));
}

optional<expr> is_bit0(expr const & e) {
    if (!is_const_app(e, get_bit0_name(), 3))
        return none_expr();
    return some_expr(app_arg(e));
}

optional<expr> is_bit1(expr const & e) {
    if (!is_const_app(e, get_bit1_name(), 4))
        return none_expr();
    return some_expr(app_arg(e));
}

optional<expr> is_neg(expr const & e) {
    if (!is_const_app(e, get_has_neg_neg_name(), 3))
        return none_expr();
    return some_expr(app_arg(e));
}

optional<expr> unfold_num_app(environment const & env, expr const & e) {
    if (is_zero(e) || is_one(e) || is_bit0(e) || is_bit1(e)) {
        return unfold_app(env, e);
    } else {
        return none_expr();
    }
}

bool is_numeral_const_name(name const & n) {
    return n == get_has_zero_zero_name() || n == get_has_one_one_name() || n == get_bit0_name() || n == get_bit1_name();
}

static bool is_num(expr const & e, bool first) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (!is_constant(f))
      return false;
    if (const_name(f) == get_has_one_one_name())
        return args.size() == 2;
    else if (const_name(f) == get_has_zero_zero_name())
        return first && args.size() == 2;
    else if (const_name(f) == get_nat_zero_name())
        return first && args.size() == 0;
    else if (const_name(f) == get_bit0_name())
        return args.size() == 3 && is_num(args[2], false);
    else if (const_name(f) == get_bit1_name())
        return args.size() == 4 && is_num(args[3], false);
    return false;
}

bool is_num(expr const & e) {
    return is_num(e, true);
}

bool is_signed_num(expr const & e) {
    if (is_num(e))
        return true;
    else if (auto r = is_neg(e))
        return is_num(*r);
    else
        return false;
}

static optional<mpz> to_num(expr const & e, bool first) {
    if (is_zero(e)) {
        return first ? some(mpz(0)) : optional<mpz>();
    } else if (is_one(e)) {
        return some(mpz(1));
    } else if (auto a = is_bit0(e)) {
        if (auto r = to_num(*a, false))
            return some(2*(*r));
    } else if (auto a = is_bit1(e)) {
        if (auto r = to_num(*a, false))
            return some(2*(*r)+1);
    } else if (first) {
        if (auto a = is_neg(e)) {
            if (auto r = to_num(*a, false))
                return some(neg(*r));
        }
    }
    return optional<mpz>();
}

optional<mpz> to_num(expr const & e) {
    return to_num(e, true);
}

bool is_num_leaf_constant(name const & n) {
    return
        n == get_has_zero_zero_name() ||
        n == get_has_one_one_name();
}

expr to_nat_expr_core(mpz const & n) {
    lean_assert(n >= 0);
    if (n == 1)
        return mk_nat_one();
    else if (n % mpz(2) == 0)
        return mk_nat_bit0(to_nat_expr(n / 2));
    else
        return mk_nat_bit1(to_nat_expr(n / 2));
}

expr to_nat_expr(mpz const & n) {
    if (n == 0)
        return mk_nat_zero();
    else
        return to_nat_expr_core(n);
}

void initialize_num() {}
void finalize_num() {}
}




// ========== exception.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/sstream.h"
#include "kernel/ext_exception.h"
#include "kernel/scope_pos_info_provider.h"

namespace lean {
class generic_exception : public ext_exception {
protected:
    optional<pos_info> m_pos;
    pp_fn              m_pp_fn;
public:
    generic_exception(char const * msg, optional<pos_info> const & p, pp_fn const & fn):
        ext_exception(msg), m_pos(p), m_pp_fn(fn) {}
    generic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn):
        generic_exception(msg, get_pos_info(m), fn) {}
    generic_exception(optional<pos_info> const & p, pp_fn const & fn):
            ext_exception(), m_pos(p), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, pp_fn const & fn):
        ext_exception(), m_pos(get_pos_info(m)), m_pp_fn(fn) {}
    generic_exception(optional<expr> const & m, char const * msg);
    generic_exception(optional<expr> const & m, sstream const & strm):generic_exception(m, strm.str().c_str()) {}
    explicit generic_exception(char const * msg):generic_exception(none_expr(), msg) {}
    explicit generic_exception(sstream const & strm):generic_exception(none_expr(), strm) {}
    generic_exception(expr const & m, char const * msg):generic_exception(some_expr(m), msg) {}
    generic_exception(expr const & m, sstream const & strm):generic_exception(some_expr(m), strm) {}
    generic_exception(expr const & m, pp_fn const & fn):generic_exception(some_expr(m), fn) {}

    virtual optional<pos_info> get_pos() const override { return m_pos; }
    virtual format pp(formatter const & fmt) const override { return m_pp_fn(fmt); }
    virtual throwable * clone() const override { return new generic_exception(m_msg.c_str(), m_pos, m_pp_fn); }
    virtual void rethrow() const override { throw *this; }
};

class nested_exception : public generic_exception {
protected:
    std::shared_ptr<throwable>          m_exception;
public:
    nested_exception(optional<pos_info> const & p, pp_fn const & fn, throwable const & ex):
            generic_exception(p, fn), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, pp_fn const & fn, throwable const & ex):
        generic_exception(m, fn), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, char const * msg, throwable const & ex):
        generic_exception(m, msg), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    nested_exception(optional<expr> const & m, sstream const & strm, throwable const & ex):
        generic_exception(m, strm), m_exception(std::shared_ptr<throwable>(ex.clone())) {}
    explicit nested_exception(char const * msg, throwable const & ex):
        nested_exception(none_expr(), msg, ex) {}
    explicit nested_exception(format const & fmt, throwable const & ex):
        nested_exception(none_expr(), [=](formatter const &) { return fmt; }, ex) {}
    explicit nested_exception(sstream const & strm, throwable const & ex):
        nested_exception(none_expr(), strm, ex) {}
    virtual ~nested_exception() noexcept {}

    virtual optional<pos_info> get_pos() const override;
    virtual format pp(formatter const & fmt) const override;
    virtual throwable * clone() const override;
    virtual void rethrow() const override { throw *this; }
};

/* Similar to nested_exception but get_pos returns none
   even if nested exception has position information. */
class nested_exception_without_pos : public nested_exception {
    nested_exception_without_pos(pp_fn const & fn, throwable const & ex):
        nested_exception(none_expr(), fn, ex) {}
public:
    nested_exception_without_pos(char const * msg, throwable const & ex):
        nested_exception(msg, ex) {}
    virtual optional<pos_info> get_pos() const override { return optional<pos_info>(); }
    virtual throwable * clone() const override { return new nested_exception_without_pos(m_pp_fn, *m_exception); }
    virtual void rethrow() const override { throw *this; }
};

/** \brief Lean exception occurred when parsing file. */
class parser_nested_exception : public exception {
    std::shared_ptr<throwable>          m_exception;
public:
    parser_nested_exception(std::shared_ptr<throwable> const & ex): exception("parser exception"), m_exception(ex) {}
    virtual ~parser_nested_exception() {}
    virtual throwable * clone() const override { return new parser_nested_exception(m_exception); }
    virtual void rethrow() const override { throw *this; }
    virtual char const * what() const noexcept override { return m_exception->what(); }
    throwable const & get_exception() const { return *(m_exception.get()); }
};
}




// ========== exception.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/exception.h"

namespace lean {
static pp_fn mk_pp_fn(char const * msg) {
    std::string msg_str = msg;
    return [=](formatter const &) { return format(msg_str); }; // NOLINT
}

generic_exception::generic_exception(optional<expr> const & m, char const * msg):
    generic_exception(msg, m, mk_pp_fn(msg)) {}

optional<pos_info> nested_exception::get_pos() const {
    if (m_pos)
        return m_pos;
    else if (ext_exception * ex = dynamic_cast<ext_exception *>(m_exception.get()))
        return ex->get_pos();
    else
        return {};
}

format nested_exception::pp(formatter const & fmt) const {
    format r = m_pp_fn(fmt);
    r += line() + format("nested exception message:") + line();
    if (ext_exception * ex = dynamic_cast<ext_exception *>(m_exception.get())) {
        r += ex->pp(fmt);
    } else {
        r += format(m_exception->what());
    }
    return r;
}

throwable * nested_exception::clone() const {
    return new nested_exception(m_pos, m_pp_fn, *m_exception);
}
}




// ========== private.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/optional.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief This is an auxiliary function used to simulate private declarations. Whenever we want to create a "private"
   declaration, this module creates an internal "hidden" name that is not accessible to users.
   In principle, users can access the internal names if they want by applying themselves the procedure used to create
   the "hidden" names.

   The optional \c base_hash can be used to influence the "hidden" name associated with \c n.

   The mapping between \c n and the "hidden" name is saved  in the .olean files.
*/
pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & base_hash);

/**
    \brief Return the user name associated with the hidden name \c n.

    \remark The "user name" is the argument provided to \c add_private_name, and "hidden name" is the name returned
    by \c add_private_name.
*/
optional<name> hidden_to_user_name(environment const & env, name const & n);

bool is_private(environment const & env, name const & n);

pair<environment, name> mk_private_prefix(environment const & env, name const & n, optional<unsigned> const & base_hash);

/* Create a private name based on \c c and get_pos_info_provider(), and register it using \c add_private_name */
pair<environment, name> mk_private_name(environment const & env, name const & c);

/* Create a private prefix that is going to be use to generate many private names.
   This function registers the private prefix in the environment. */
pair<environment, name> mk_private_prefix(environment const & env, optional<unsigned> const & extra_hash);

/* Similar to the previous function, but generate an extra_hash using get_pos_info_provider */
pair<environment, name> mk_private_prefix(environment const & env);

/* Register a \c n as the name for private name \c prv_n. \c prv_n must have been constructed using
   a prefix returned by \c mk_private_prefix. */
environment register_private_name(environment const & env, name const & n, name const & prv_n);

/* Return true iff a prefix of `n` is registered as a private prefix in the given environment. */
bool has_private_prefix(environment const & env, name const & n);

/* Return some name iff a prefix of `n` is registered as a private prefix in the given environment. */
optional<name> get_private_prefix(environment const & env, name const & n);

void initialize_private();
void finalize_private();
}




// ========== private.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/hash.h"
#include "util/sstream.h"
#include "library/private.h"
#include "library/module.h"
#include "library/fingerprint.h"

namespace lean {
struct private_ext : public environment_extension {
    unsigned       m_counter;
    name_map<name> m_inv_map;  // map: hidden-name -> user-name
    /* We store private prefixes to make sure register_private_name is used correctly.
       This information does not need to be stored in .olean files. */
    name_set       m_private_prefixes;
    private_ext():m_counter(0) {}
};

struct private_ext_reg {
    unsigned m_ext_id;
    private_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<private_ext>()); }
};

static private_ext_reg * g_ext = nullptr;
static private_ext const & get_extension(environment const & env) {
    return static_cast<private_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, private_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<private_ext>(ext));
}

static name * g_private = nullptr;

struct private_modification : public modification {
    LEAN_MODIFICATION("prv")

    name m_name, m_real;

    private_modification() {}
    private_modification(name const & n, name const & h) : m_name(n), m_real(h) {}

    void perform(environment & env) const override {
        private_ext ext = get_extension(env);
        // we restore only the mapping hidden-name -> user-name (for pretty printing purposes)
        ext.m_inv_map.insert(m_real, m_name);
        ext.m_counter++;
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_name << m_real;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n, h;
        d >> n >> h;
        return std::make_shared<private_modification>(n, h);
    }
};

/* Make sure the mapping "hidden-name r ==> user-name n" is preserved when we close sections and
   export .olean files. */
static environment preserve_private_data(environment const & env, name const & r, name const & n) {
    return module::add(env, std::make_shared<private_modification>(n, r));
}

static name mk_private_name_core(environment const & env, name const & n, optional<unsigned> const & extra_hash) {
    private_ext const & ext = get_extension(env);
    unsigned h              = hash(n.hash(), ext.m_counter);
    uint64   f              = get_fingerprint(env);
    h                       = hash(h, static_cast<unsigned>(f >> 32));
    h                       = hash(h, static_cast<unsigned>(f));
    if (extra_hash)
        h = hash(h, *extra_hash);
    return name(*g_private, h) + n;
}

pair<environment, name> add_private_name(environment const & env, name const & n, optional<unsigned> const & extra_hash) {
    name r          = mk_private_name_core(env, n, extra_hash);
    private_ext ext = get_extension(env);
    ext.m_inv_map.insert(r, n);
    ext.m_counter++;
    environment new_env = update(env, ext);
    new_env = preserve_private_data(new_env, r, n);
    return mk_pair(new_env, r);
}

static unsigned mk_extra_hash_using_pos() {
    unsigned h = 31;
    if (auto pinfo = get_pos_info_provider()) {
        h = hash(pinfo->get_some_pos().first, pinfo->get_some_pos().second);
        char const * fname = pinfo->get_file_name();
        h = hash_str(strlen(fname), fname, h);
    }
    return h;
}

pair<environment, name> mk_private_name(environment const & env, name const & c) {
    return add_private_name(env, c, optional<unsigned>(mk_extra_hash_using_pos()));
}

pair<environment, name> mk_private_prefix(environment const & env, optional<unsigned> const & extra_hash) {
    name r          = mk_private_name_core(env, name(), extra_hash);
    private_ext ext = get_extension(env);
    ext.m_private_prefixes.insert(r);
    ext.m_counter++;
    environment new_env = update(env, ext);
    return mk_pair(new_env, r);
}

pair<environment, name> mk_private_prefix(environment const & env) {
    return mk_private_prefix(env, optional<unsigned>(mk_extra_hash_using_pos()));
}

static optional<name> get_private_prefix(private_ext const & ext, name n) {
    while (true) {
        if (ext.m_private_prefixes.contains(n))
            return optional<name>(n);
        if (n.is_atomic())
            return optional<name>();
        n = n.get_prefix();
    }
}

/* Return true iff a prefix of `n` is registered as a private prefix in `ext` */
static bool has_private_prefix(private_ext const & ext, name n) {
    return static_cast<bool>(get_private_prefix(ext, n));
}

optional<name> get_private_prefix(environment const & env, name const & n) {
    private_ext const & ext = get_extension(env);
    return get_private_prefix(ext, n);
}

bool has_private_prefix(environment const & env, name const & n) {
    private_ext const & ext = get_extension(env);
    return has_private_prefix(ext, n);
}

environment register_private_name(environment const & env, name const & n, name const & prv_n) {
    private_ext ext = get_extension(env);
    if (!has_private_prefix(ext, prv_n)) {
        /* TODO(Leo): consider using an assertion */
        throw exception(sstream() << "failed to register private name '" << prv_n << "', prefix has not been registered");
    }
    ext.m_inv_map.insert(prv_n, n);
    environment new_env = update(env, ext);
    return preserve_private_data(new_env, prv_n, n);
}

optional<name> hidden_to_user_name(environment const & env, name const & n) {
    auto it = get_extension(env).m_inv_map.find(n);
    return it ? optional<name>(*it) : optional<name>();
}

bool is_private(environment const & env, name const & n) {
    return static_cast<bool>(hidden_to_user_name(env, n));
}

void initialize_private() {
    g_ext     = new private_ext_reg();
    g_private = new name("_private");
    private_modification::init();
}

void finalize_private() {
    private_modification::finalize();
    delete g_private;
    delete g_ext;
}
}




// ========== expr_lt.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "util/rb_map.h"
#include "library/local_context.h"

namespace lean {
/** \brief Total order on expressions.

    \remark If \c use_hash is true, then we use the hash_code to
    partially order expressions. Setting use_hash to false is useful
    for testing the code.

    \remark If lctx is not nullptr, then we use the local_decl index to compare local constants.
*/
bool is_lt(expr const & a, expr const & b, bool use_hash, local_context const * lctx = nullptr);
/** \brief Similar to is_lt, but universe level parameter names are ignored. */
bool is_lt_no_level_params(expr const & a, expr const & b);
inline bool is_hash_lt(expr const & a, expr const & b) { return is_lt(a, b, true); }
inline bool operator<(expr const & a, expr const & b)  { return is_lt(a, b, true); }
inline bool operator>(expr const & a, expr const & b)  { return is_lt(b, a, true); }
inline bool operator<=(expr const & a, expr const & b) { return !is_lt(b, a, true); }
inline bool operator>=(expr const & a, expr const & b) { return !is_lt(a, b, true); }
struct expr_quick_cmp { int operator()(expr const & e1, expr const & e2) const { return is_lt(e1, e2, true) ? -1 : (e1 == e2 ? 0 : 1); } };
struct expr_cmp_no_level_params { int operator()(expr const & e1, expr const & e2) const; };

template<typename T>
using rb_expr_map = rb_map<expr, T, expr_quick_cmp>;

typedef rb_tree<expr, expr_quick_cmp> rb_expr_tree;
}




// ========== expr_lt.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"
#include "library/expr_lt.h"

namespace lean {
bool is_lt(expr const & a, expr const & b, bool use_hash, local_context const * lctx) {
    if (is_eqp(a, b))                    return false;
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    if (use_hash) {
        if (a.hash() < b.hash())         return true;
        if (a.hash() > b.hash())         return false;
    }
    if (a == b)                          return false;
    switch (a.kind()) {
    case expr_kind::Var:
        return var_idx(a) < var_idx(b);
    case expr_kind::Constant:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return is_lt(const_levels(a), const_levels(b), use_hash);
    case expr_kind::App:
        if (app_fn(a) != app_fn(b))
            return is_lt(app_fn(a), app_fn(b), use_hash, lctx);
        else
            return is_lt(app_arg(a), app_arg(b), use_hash, lctx);
    case expr_kind::Lambda: case expr_kind::Pi:
        if (binding_domain(a) != binding_domain(b))
            return is_lt(binding_domain(a), binding_domain(b), use_hash, lctx);
        else
            return is_lt(binding_body(a), binding_body(b), use_hash, lctx);
    case expr_kind::Let:
        if (let_type(a) != let_type(b))
            return is_lt(let_type(a), let_type(b), use_hash, lctx);
        else if (let_value(a) != let_value(b))
            return is_lt(let_value(a), let_value(b), use_hash, lctx);
        else
            return is_lt(let_body(a), let_body(b), use_hash, lctx);
    case expr_kind::Sort:
        return is_lt(sort_level(a), sort_level(b), use_hash);
    case expr_kind::Local:
        if (lctx) {
            if (auto d1 = lctx->find_local_decl(a))
            if (auto d2 = lctx->find_local_decl(b))
                return d1->get_idx() < d2->get_idx();
        }
        /* fall-thru */
    case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt(mlocal_type(a), mlocal_type(b), use_hash, lctx);
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (macro_arg(a, i) != macro_arg(b, i))
                return is_lt(macro_arg(a, i), macro_arg(b, i), use_hash, lctx);
        }
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_lt_no_level_params(level const & a, level const & b) {
    if (is_eqp(a, b))              return false;
    if (kind(a) != kind(b)) {
        if (kind(a) == level_kind::Param || kind(b) == level_kind::Param)
            return false;
        return kind(a) < kind(b);
    }
    switch (kind(a)) {
    case level_kind::Zero:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Param:
        return false;
    case level_kind::Meta:
        return meta_id(a) < meta_id(b);
    case level_kind::Max:
        if (is_lt_no_level_params(max_lhs(a), max_lhs(b)))
            return true;
        else if (is_lt_no_level_params(max_lhs(b), max_lhs(a)))
            return false;
        else
            return is_lt_no_level_params(max_rhs(a), max_rhs(b));
    case level_kind::IMax:
        if (is_lt_no_level_params(imax_lhs(a), imax_lhs(b)))
            return true;
        else if (is_lt_no_level_params(imax_lhs(b), imax_lhs(a)))
            return false;
        else
            return is_lt_no_level_params(imax_rhs(a), imax_rhs(b));
    case level_kind::Succ:
        return is_lt_no_level_params(succ_of(a), succ_of(b));
    }
    lean_unreachable();
}

bool is_lt_no_level_params(levels const & as, levels const & bs) {
    if (is_nil(as))
        return !is_nil(bs);
    else if (is_nil(bs))
        return false;
    else if (is_lt_no_level_params(car(as), car(bs)))
        return true;
    else if (is_lt_no_level_params(car(bs), car(as)))
        return false;
    else
        return is_lt_no_level_params(cdr(as), cdr(bs));
}

bool is_lt_no_level_params(expr const & a, expr const & b) {
    if (is_eqp(a, b))                    return false;
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    switch (a.kind()) {
    case expr_kind::Var:
        return var_idx(a) < var_idx(b);
    case expr_kind::Constant:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return is_lt_no_level_params(const_levels(a), const_levels(b));
    case expr_kind::App:
        if (is_lt_no_level_params(app_fn(a), app_fn(b)))
            return true;
        else if (is_lt_no_level_params(app_fn(b), app_fn(a)))
            return false;
        else
            return is_lt_no_level_params(app_arg(a), app_arg(b));
    case expr_kind::Lambda: case expr_kind::Pi:
        if (is_lt_no_level_params(binding_domain(a), binding_domain(b)))
            return true;
        else if (is_lt_no_level_params(binding_domain(b), binding_domain(a)))
            return false;
        else
            return is_lt_no_level_params(binding_body(a), binding_body(b));
    case expr_kind::Let:
        if (is_lt_no_level_params(let_type(a), let_type(b)))
            return true;
        else if (is_lt_no_level_params(let_type(b), let_type(a)))
            return false;
        else if (is_lt_no_level_params(let_value(a), let_value(b)))
            return true;
        else if (is_lt_no_level_params(let_value(b), let_value(a)))
            return false;
        else
            return is_lt_no_level_params(let_body(a), let_body(b));
    case expr_kind::Sort:
        return is_lt_no_level_params(sort_level(a), sort_level(b));
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt_no_level_params(mlocal_type(a), mlocal_type(b));
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (is_lt_no_level_params(macro_arg(a, i), macro_arg(b, i)))
                return true;
            else if (is_lt_no_level_params(macro_arg(b, i), macro_arg(a, i)))
                return false;
        }
        return false;
    }
    lean_unreachable();
}

int expr_cmp_no_level_params::operator()(expr const & e1, expr const & e2) const {
    if (is_lt_no_level_params(e1, e2))
        return -1;
    else if (is_lt_no_level_params(e2, e1))
        return 1;
    else
        return 0;
}
}




// ========== module.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include <utility>
#include <vector>
#include "util/serializer.h"
#include "util/optional.h"
#include "kernel/pos_info_provider.h"
#include "kernel/inductive/inductive.h"
#include "library/io_state.h"
#include "util/task.h"

namespace lean {
class corrupted_file_exception : public exception {
public:
    corrupted_file_exception(std::string const & fname);
};

struct module_name {
    name               m_name;
    optional<unsigned> m_relative;
    module_name() {}
    module_name(name const & n, unsigned k):m_name(n), m_relative(k) {}
    explicit module_name(name const & n):m_name(n) {}
};

struct modification;

using modification_list = std::vector<std::shared_ptr<modification const>>;
struct loaded_module {
    std::string m_module_name;
    std::vector<module_name> m_imports;
    modification_list m_modifications;
    task<bool> m_uses_sorry;

    task<environment> m_env;
};
using module_loader = std::function<std::shared_ptr<loaded_module const> (std::string const &, module_name const &)>;
module_loader mk_olean_loader(std::vector<std::string> const &);
module_loader mk_dummy_loader();

/** \brief Return the list of declarations performed in the current module */
list<name> const & get_curr_module_decl_names(environment const & env);
/** \brief Return the list of universes declared in the current module */
list<name> const & get_curr_module_univ_names(environment const & env);
/** \brief Return the list of modules directly imported by the current module */
std::vector<module_name> get_curr_module_imports(environment const & env);

/** \brief Return an environment based on \c env, where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.
    The environment \c env is usually an empty environment.
*/
environment
import_modules(environment const & env,
               std::string const & current_mod, std::vector<module_name> const & ref,
               module_loader const & mod_ldr);

using module_id = std::string;

struct import_error {
    module_id m_mod;
    module_name m_import;
    std::exception_ptr m_ex;
};
environment
import_modules(environment const & env,
               std::string const & current_mod, std::vector<module_name> const & ref,
               module_loader const & mod_ldr, buffer<import_error> & errors);

/** \brief Return the .olean file where decl_name was defined. The result is none if the declaration
    was not defined in an imported file. */
optional<std::string> get_decl_olean(environment const & env, name const & decl_name);

/** \brief Return position (line and column number) where the given declaration was defined. */
optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name);

/** \brief Associate the given position with the given declaration. The information is not saved on
    .olean files. We use this function for attaching position information to temporary functions. */
environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos);

/** \brief Store/Export module using \c env. */
loaded_module export_module(environment const & env, std::string const & mod_name);
void write_module(loaded_module const & mod, std::ostream & out);

std::shared_ptr<loaded_module const> cache_preimported_env(
        loaded_module &&, environment const & initial_env,
        std::function<module_loader()> const & mk_mod_ldr);

/** \brief Check whether we should try to load the given .olean file according to its header and Lean version. */
bool is_candidate_olean_file(std::string const & file_name);

struct olean_data {
    std::vector<module_name> m_imports;
    std::string m_serialized_modifications;
    bool m_uses_sorry;
};
olean_data parse_olean(std::istream & in, std::string const & file_name, bool check_hash = true);
modification_list parse_olean_modifications(std::string const & serialized_modifications, std::string const & file_name);
void import_module(modification_list const & modifications, std::string const & file_name, environment & env);

struct modification {
public:
    virtual ~modification() {}
    virtual const char * get_key() const = 0;
    virtual void perform(environment &) const = 0;
    virtual void serialize(serializer &) const = 0;
    virtual void get_task_dependencies(buffer<gtask> &) const {}

    // Used to check for sorrys.
    virtual void get_introduced_exprs(std::vector<task<expr>> &) const {}
};

#define LEAN_MODIFICATION(k) \
  static void init() { \
    register_module_object_reader(k, module_modification_reader(deserialize)); \
  } \
  static void finalize() {} \
  const char * get_key() const override { return k; }

using module_modification_reader = std::function<std::shared_ptr<modification const>(deserializer &)>;

/** \brief Register a module object reader. The key \c k is used to identify the class of objects
    that can be read by the given reader.
*/
void register_module_object_reader(std::string const & k, module_modification_reader && r);

namespace module {
/** \brief Add a function that should be invoked when the environment is exported.
    The key \c k identifies which module_object_reader should be used to deserialize the object
    when the module is imported.

    \see module_object_reader
*/
environment add(environment const & env, std::shared_ptr<modification const> const & modif);
environment add_and_perform(environment const & env, std::shared_ptr<modification const> const & modif);

/** \brief Add the given declaration to the environment, and mark it to be exported. */
environment add(environment const & env, certified_declaration const & d);

/** \brief Return true iff \c n is a definition added to the current module using #module::add */
bool is_definition(environment const & env, name const & n);

/** \brief Add the given inductive declaration to the environment, and mark it to be exported. */
environment add_inductive(environment                       env,
                          inductive::inductive_decl const & decl,
                          bool                              is_trusted);

/** \brief The following function must be invoked to register the quotient type computation rules in the kernel. */
environment declare_quotient(environment const & env);

/* Auxiliary object for setting position information for module declarations.
   It affects module::add and module::add_inductive methods. */
class scope_pos_info {
public:
    scope_pos_info(pos_info const & pos_info);
    ~scope_pos_info();
};
}
void initialize_module();
void finalize_module();
}




// ========== module.cpp ==========

/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <vector>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <sys/stat.h>
#include "util/hash.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "util/sstream.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/name_map.h"
#include "util/file_lock.h"
#include "kernel/type_checker.h"
#include "kernel/quotient/quotient.h"
#include "library/module.h"
#include "library/noncomputable.h"
#include "library/sorry.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/unfold_macros.h"
#include "library/module_mgr.h"
#include "library/library_task_builder.h"

/*
Missing features: non monotonic modifications in .olean files

- Persistent `set_option`. We want to be able to store the option settings in .olean files.
  The main issue is conflict between imported modules. That is, each imported module wants to
  set a particular option with a different value. This can create counter-intuitive behavior.
  Consider the following scenarion

  * A.olean : sets option `foo` to true
  * B.olean : imports A.olean
  * C.olean : sets option `foo` to false
  * We create D.lean containing the following import clause:
    ```
    import B C A
    ```
    The user may expect that `foo` is set to true, since `A` is the last module to be imported,
    but this is not the case. `B` is imported first, then `A` (which sets option `foo` to true),
    then `C` (which sets option `foo` to false), the last import `A` is skipped since `A` has already
    been imported, and we get `foo` set to false.

  To address this issue we consider a persistent option import validator. The validator
  signs an error if there are two direct imports which try to set the same option to different
  values. For example, in the example above, `B` and `C` are conflicting, and an error would
  be signed when trying to import `C`. Then, users would have to resolve the conflict by
  creating an auxiliary import. For example, they could create the module `C_aux.lean` containing
  ```
  import C
  set_option persistent foo true
  ```
  and replace `import B C A` with `import B C_aux A`

- Removing attributes. The validation procedure for persistent options can be extended to attribute
  deletion. In latest version, we can only locally remove attributes. The validator for attribute deletion
  would sign an error if there are two direct imports where one adds an attribute `[foo]` to an declaration
  `bla` and the other removes it.

- Parametric attributes. This is not a missing feature, but a bug. In the current version, we have
  parametric attributes, and different modules may set the same declaration with different parameter values.
  We can fix this bug by using an attribute validator which will check parametric attributes, or
  we can allow parametric attributes to be set only once. That is, we sign an error if the user tries
  to reset them.
*/

namespace lean {
corrupted_file_exception::corrupted_file_exception(std::string const & fname):
    exception(sstream() << "failed to import '" << fname << "', file is corrupted, please regenerate the file from sources") {
}

struct module_ext : public environment_extension {
    std::vector<module_name> m_direct_imports;
    list<std::shared_ptr<modification const>> m_modifications;
    list<name>        m_module_univs;
    list<name>        m_module_decls;
    name_set          m_module_defs;
    name_set          m_imported;
    // Map from declaration name to olean file where it was defined
    name_map<std::string>     m_decl2olean;
    name_map<pos_info>        m_decl2pos_info;
};

struct module_ext_reg {
    unsigned m_ext_id;
    module_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<module_ext>()); }
};

static module_ext_reg * g_ext = nullptr;

static module_ext const & get_extension(environment const & env) {
    return static_cast<module_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, module_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<module_ext>(ext));
}

list<name> const & get_curr_module_decl_names(environment const & env) {
    return get_extension(env).m_module_decls;
}

list<name> const & get_curr_module_univ_names(environment const & env) {
    return get_extension(env).m_module_univs;
}

std::vector<module_name> get_curr_module_imports(environment const & env) {
    return get_extension(env).m_direct_imports;
}

/* Add the entry decl_name -> fname to the environment. fname is the name of the .olean file
   where decl_name was defined. */
static environment add_decl_olean(environment const & env, name const & decl_name, std::string const & fname) {
    module_ext ext = get_extension(env);
    ext.m_decl2olean.insert(decl_name, fname);
    return update(env, ext);
}

optional<std::string> get_decl_olean(environment const & env, name const & decl_name) {
    module_ext const & ext = get_extension(env);
    name d;
    if (auto r = inductive::is_intro_rule(env, decl_name))
        d = *r;
    else if (auto r = inductive::is_elim_rule(env, decl_name))
        d = *r;
    else
        d = decl_name;
    if (auto r = ext.m_decl2olean.find(d))
        return optional<std::string>(*r);
    else
        return optional<std::string>();
}

LEAN_THREAD_VALUE(bool, g_has_pos, false);
LEAN_THREAD_VALUE(unsigned, g_curr_line, 0);
LEAN_THREAD_VALUE(unsigned, g_curr_column, 0);

module::scope_pos_info::scope_pos_info(pos_info const & pos_info) {
    g_has_pos     = true;
    g_curr_line   = pos_info.first;
    g_curr_column = pos_info.second;
}

module::scope_pos_info::~scope_pos_info() {
    g_has_pos = false;
}

struct pos_info_mod : public modification {
    LEAN_MODIFICATION("PInfo")

    name m_decl_name;
    pos_info m_pos_info;

    pos_info_mod(name const & decl_name, pos_info const & pos) :
        m_decl_name(decl_name), m_pos_info(pos) {}

    void perform(environment & env) const override {
        auto ext = get_extension(env);
        ext.m_decl2pos_info.insert(m_decl_name, m_pos_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl_name << m_pos_info.first << m_pos_info.second;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name decl_name; unsigned line, column;
        d >> decl_name >> line >> column;
        return std::make_shared<pos_info_mod>(decl_name, pos_info {line, column});
    }
};

static environment add_decl_pos_info(environment const & env, name const & decl_name) {
    if (!g_has_pos)
        return env;
    return module::add_and_perform(env, std::make_shared<pos_info_mod>(decl_name, pos_info {g_curr_line, g_curr_column}));
}

optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name) {
    module_ext const & ext = get_extension(env);
    name d;
    if (auto r = inductive::is_intro_rule(env, decl_name))
        d = *r;
    else if (auto r = inductive::is_elim_rule(env, decl_name))
        d = *r;
    else
        d = decl_name;
    if (auto r = ext.m_decl2pos_info.find(d))
        return optional<pos_info>(*r);
    else
        return optional<pos_info>();
}

environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos) {
    module_ext ext = get_extension(env);
    ext.m_decl2pos_info.insert(decl_name, pos);
    return update(env, ext);
}

static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

serializer & operator<<(serializer & s, module_name const & n) {
    if (n.m_relative)
        s << true << *n.m_relative << n.m_name;
    else
        s << false << n.m_name;
    return s;
}

deserializer & operator>>(deserializer & d, module_name & r) {
    if (d.read_bool()) {
        unsigned k;
        d >> k >> r.m_name;
        r.m_relative = { k };
    } else {
        d >> r.m_name;
        r.m_relative = optional<unsigned>();
    }
    return d;
}

static unsigned olean_hash(std::string const & data) {
    return hash(data.size(), [&] (unsigned i) { return static_cast<unsigned char>(data[i]); });
}

void write_module(loaded_module const & mod, std::ostream & out) {
    std::ostringstream out1(std::ios_base::binary);
    serializer s1(out1);

    // store objects
    for (auto p : mod.m_modifications) {
        s1 << std::string(p->get_key());
        p->serialize(s1);
    }
    s1 << g_olean_end_file;

    if (!out1.good()) {
        throw exception(sstream() << "error during serialization of '" << mod.m_module_name << "'");
    }

    std::string r = out1.str();
    unsigned h    = olean_hash(r);

    bool uses_sorry = get(mod.m_uses_sorry);

    serializer s2(out);
    s2 << g_olean_header << get_version_string();
    s2 << h;
    s2 << uses_sorry;
    // store imported files
    s2 << static_cast<unsigned>(mod.m_imports.size());
    for (auto m : mod.m_imports)
        s2 << m;
    // store object code
    s2.write_blob(r);
}

static task<bool> has_sorry(modification_list const & mods) {
    std::vector<task<expr>> introduced_exprs;
    for (auto & mod : mods) mod->get_introduced_exprs(introduced_exprs);
    return any(introduced_exprs, [] (expr const & e) { return has_sorry(e); });
}

loaded_module export_module(environment const & env, std::string const & mod_name) {
    loaded_module out;
    out.m_module_name = mod_name;

    module_ext const & ext = get_extension(env);

    out.m_imports = ext.m_direct_imports;

    for (auto & w : ext.m_modifications)
        out.m_modifications.push_back(w);
    std::reverse(out.m_modifications.begin(), out.m_modifications.end());

    out.m_uses_sorry = has_sorry(out.m_modifications);

    return out;
}

typedef std::unordered_map<std::string, module_modification_reader> object_readers;
static object_readers * g_object_readers = nullptr;
static object_readers & get_object_readers() { return *g_object_readers; }

void register_module_object_reader(std::string const & k, module_modification_reader && r) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = r;
}

struct import_helper {
    static environment add_unchecked(environment const & env, declaration const & decl) {
        return env.add(certify_or_check(env, decl));
    }
    static certified_declaration certify_or_check(environment const & env, declaration const & decl) {
        return certify_unchecked::certify_or_check(env, decl);
    }
};

struct decl_modification : public modification {
    LEAN_MODIFICATION("decl")

    declaration m_decl;
    unsigned    m_trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;

    decl_modification() {}
    decl_modification(declaration const & decl, unsigned trust_lvl):
        m_decl(decl), m_trust_lvl(trust_lvl) {}

    void perform(environment & env) const override {
        auto decl = m_decl;
        /*
           The unfold_untrusted_macros is only needed when we are importing the declaration from a .olean
           file that has been created with a different (and higher) trust level. So, it may contain macros
           that will not be accepted by the current kernel, and they must be unfolded.

           In a single Lean session, the trust level is fixed, and we invoke unfold_untrusted_macros
           at frontends/lean/definition_cmds.cpp before we even create the declaration.
        */
        if (m_trust_lvl > env.trust_lvl()) {
            decl = unfold_untrusted_macros(env, decl);
        }

        // TODO(gabriel): this might be a bit more unsafe here than before
        env = import_helper::add_unchecked(env, decl);
    }

    void serialize(serializer & s) const override {
        s << m_decl << m_trust_lvl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto decl = read_declaration(d);
        unsigned trust_lvl; d >> trust_lvl;
        return std::make_shared<decl_modification>(std::move(decl), trust_lvl);
    }

    void get_introduced_exprs(std::vector<task<expr>> & es) const override {
        es.push_back(mk_pure_task(m_decl.get_type()));
        if (m_decl.is_theorem()) {
            es.push_back(m_decl.get_value_task());
        } else if (m_decl.is_definition()) {
            es.push_back(mk_pure_task(m_decl.get_value()));
        }
    }

    void get_task_dependencies(buffer<gtask> & deps) const override {
        if (m_decl.is_theorem())
            deps.push_back(m_decl.get_value_task());
    }
};

struct inductive_modification : public modification {
    LEAN_MODIFICATION("ind")

    inductive::certified_inductive_decl m_decl;
    unsigned m_trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;


    inductive_modification(inductive::certified_inductive_decl const & decl, unsigned trust_lvl) :
            m_decl(decl), m_trust_lvl(trust_lvl) {}

    void perform(environment & env) const override {
        if (m_trust_lvl > env.trust_lvl()) {
            auto d = m_decl.get_decl();
            d.m_type = unfold_untrusted_macros(env, d.m_type);
            d.m_intro_rules = map(d.m_intro_rules, [&](inductive::intro_rule const & r) {
                return unfold_untrusted_macros(env, r);
            });
            env = add_inductive(env, d, m_decl.is_trusted()).first;
        } else {
            env = m_decl.add(env);
        }
    }

    void serialize(serializer & s) const override {
        s << m_decl << m_trust_lvl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto decl = read_certified_inductive_decl(d);
        unsigned trust_lvl;
        d >> trust_lvl;
        return std::make_shared<inductive_modification>(std::move(decl), trust_lvl);
    }

    void get_introduced_exprs(std::vector<task<expr>> & es) const override {
        es.push_back(mk_pure_task(m_decl.get_decl().m_type));
        for (auto & i : m_decl.get_decl().m_intro_rules)
            es.push_back(mk_pure_task(i));
    }
};

struct quot_modification : public modification {
    LEAN_MODIFICATION("quot")

    void perform(environment & env) const override {
        env = ::lean::declare_quotient(env);
    }

    void serialize(serializer &) const override {}

    static std::shared_ptr<modification const> deserialize(deserializer &) {
        return std::make_shared<quot_modification>();
    }
};

namespace module {
environment add(environment const & env, std::shared_ptr<modification const> const & modf) {
    module_ext ext = get_extension(env);
    ext.m_modifications = cons(modf, ext.m_modifications);
    return update(env, ext);
}

environment add_and_perform(environment const & env, std::shared_ptr<modification const> const & modf) {
    auto new_env = env;
    modf->perform(new_env);
    module_ext ext = get_extension(new_env);
    ext.m_modifications = cons(modf, ext.m_modifications);
    return update(new_env, ext);
}

environment update_module_defs(environment const & env, declaration const & d) {
    if (d.is_definition() && !d.is_theorem()) {
        module_ext ext = get_extension(env);
        ext.m_module_decls = cons(d.get_name(), ext.m_module_decls);
        ext.m_module_defs.insert(d.get_name());
        return update(env, ext);
    } else {
        module_ext ext = get_extension(env);
        ext.m_module_decls = cons(d.get_name(), ext.m_module_decls);
        return update(env, ext);
    }
}

static name sorry_decl_name(name const & n) {
    if (n.is_string() && n.get_string()[0] == '_')
        return sorry_decl_name(n.get_prefix());
    return n;
}

struct sorry_warning_tag : public log_entry_cell {};
static bool is_sorry_warning_or_error(log_entry const & e) {
    return is_error_message(e) || dynamic_cast<sorry_warning_tag const *>(e.get()) != nullptr;
}

static task<bool> error_already_reported() {
    for (auto & e : logtree().get_entries())
        if (is_sorry_warning_or_error(e))
            return mk_pure_task(true);

    std::vector<task<bool>> children;
    logtree().get_used_children().for_each([&] (name const &, log_tree::node const & c) {
        children.push_back(c.has_entry(is_sorry_warning_or_error));
    });
    return any(children, [] (bool already_reported) { return already_reported; });
}

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    if (!check_computable(new_env, _d.get_name()))
        new_env = mark_noncomputable(new_env, _d.get_name());
    new_env = update_module_defs(new_env, _d);
    new_env = add(new_env, std::make_shared<decl_modification>(_d, env.trust_lvl()));

    if (_d.is_theorem()) {
        // report errors from kernel type-checker
        add_library_task(task_builder<unit>([_d, env] {
            message_builder msg(env, get_global_ios(),
                logtree().get_location().m_file_name, logtree().get_location().m_range.m_begin,
                ERROR);
            try {
                _d.get_value();
            } catch (std::exception & ex) {
                msg.set_exception(ex).report();
            } catch (...) {
                msg << "unknown exception while type-checking theorem";
                msg.report();
            }
            return unit();
        }).depends_on(_d.is_theorem() ? _d.get_value_task() : nullptr));
    }

    add_library_task(map<unit>(error_already_reported(), [_d] (bool already_reported) {
        if (!already_reported && has_sorry(_d)) {
            report_message(message(logtree().get_location().m_file_name,
                                   logtree().get_location().m_range.m_begin, WARNING,
                                   (sstream() << "declaration '" << sorry_decl_name(_d.get_name()) << "' uses sorry").str()));
            logtree().add(std::make_shared<sorry_warning_tag>());
        }
        return unit {};
    }).depends_on(_d.is_theorem() ? _d.get_value_task() : nullptr));

    return add_decl_pos_info(new_env, _d.get_name());
}

bool is_definition(environment const & env, name const & n) {
    module_ext const & ext = get_extension(env);
    return ext.m_module_defs.contains(n);
}

environment declare_quotient(environment const & env) {
    return add_and_perform(env, std::make_shared<quot_modification>());
}

using inductive::certified_inductive_decl;

environment add_inductive(environment                       env,
                          inductive::inductive_decl const & decl,
                          bool                              is_trusted) {
    pair<environment, certified_inductive_decl> r = inductive::add_inductive(env, decl, is_trusted);
    environment new_env             = r.first;
    certified_inductive_decl cidecl = r.second;
    module_ext ext = get_extension(env);
    ext.m_module_decls = cons(decl.m_name, ext.m_module_decls);
    new_env = update(new_env, ext);
    new_env = add_decl_pos_info(new_env, decl.m_name);
    return add(new_env, std::make_shared<inductive_modification>(cidecl, env.trust_lvl()));
}
} // end of namespace module

bool is_candidate_olean_file(std::string const & file_name) {
    std::ifstream in(file_name);
    deserializer d1(in, optional<std::string>(file_name));
    std::string header, version;
    d1 >> header;
    if (header != g_olean_header)
        return false;
    d1 >> version;
#ifndef LEAN_IGNORE_OLEAN_VERSION
    if (version != get_version_string())
        return false;
#endif
    return true;
}

olean_data parse_olean(std::istream & in, std::string const & file_name, bool check_hash) {
    std::vector<module_name> imports;
    bool uses_sorry;

    deserializer d1(in, optional<std::string>(file_name));
    std::string header, version;
    unsigned claimed_hash;
    d1 >> header;
    if (header != g_olean_header)
        throw exception(sstream() << "file '" << file_name << "' does not seem to be a valid object Lean file, invalid header");
    d1 >> version >> claimed_hash;
    // version has already been checked in `is_candidate_olean_file`

    d1 >> uses_sorry;

    unsigned num_imports  = d1.read_unsigned();
    for (unsigned i = 0; i < num_imports; i++) {
        module_name r;
        d1 >> r;
        imports.push_back(r);
    }

    auto code = d1.read_blob();

    if (!in.good()) {
        throw exception(sstream() << "file '" << file_name << "' has been corrupted");
    }

//    if (m_senv.env().trust_lvl() <= LEAN_BELIEVER_TRUST_LEVEL) {
    if (check_hash) {
        unsigned computed_hash = olean_hash(code);
        if (claimed_hash != computed_hash)
            throw exception(sstream() << "file '" << file_name << "' has been corrupted, checksum mismatch");
    }

    return { imports, code, uses_sorry };
}

static void import_module(environment & env, std::string const & module_file_name, module_name const & ref,
                          module_loader const & mod_ldr, buffer<import_error> & import_errors) {
    try {
        auto res = mod_ldr(module_file_name, ref);

        auto & ext0 = get_extension(env);
        if (ext0.m_imported.contains(res->m_module_name)) return;

        if (ext0.m_imported.empty() && res->m_env) {
            env = get(res->m_env);
        } else {
            for (auto &dep : res->m_imports) {
                import_module(env, res->m_module_name, dep, mod_ldr, import_errors);
            }
            import_module(res->m_modifications, res->m_module_name, env);
        }

        auto ext = get_extension(env);
        ext.m_imported.insert(res->m_module_name);
        env = update(env, ext);
    } catch (throwable) {
        import_errors.push_back({module_file_name, ref, std::current_exception()});
    }
}

environment import_modules(environment const & env0, std::string const & module_file_name,
                           std::vector<module_name> const & refs, module_loader const & mod_ldr,
                           buffer<import_error> & import_errors) {
    environment env = env0;

    for (auto & ref : refs)
        import_module(env, module_file_name, ref, mod_ldr, import_errors);

    module_ext ext = get_extension(env);
    ext.m_direct_imports = refs;
    return update(env, ext);
}

environment import_modules(environment const & env0, std::string const & module_file_name,
                           std::vector<module_name> const & refs, module_loader const & mod_ldr) {
    buffer<import_error> import_errors;
    auto env = import_modules(env0, module_file_name, refs, mod_ldr, import_errors);
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    return env;
}

static environment mk_preimported_module(environment const & initial_env, loaded_module const & lm, module_loader const & mod_ldr) {
    auto env = initial_env;
    buffer<import_error> import_errors;
    for (auto & dep : lm.m_imports) {
        import_module(env, lm.m_module_name, dep, mod_ldr, import_errors);
    }
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    import_module(lm.m_modifications, lm.m_module_name, env);
    return env;
}

std::shared_ptr<loaded_module const> cache_preimported_env(
        loaded_module && lm_ref, environment const & env0,
        std::function<module_loader()> const & mk_mod_ldr) {
    auto lm = std::make_shared<loaded_module>(lm_ref);
    std::weak_ptr<loaded_module> wlm = lm;
    lm->m_env = task_builder<environment>([env0, wlm, mk_mod_ldr] {
        if (auto lm = wlm.lock()) {
            return mk_preimported_module(env0, *lm, mk_mod_ldr());
        } else {
            throw exception("loaded_module got deallocated before preimporting");
        }
    }).build();
    return lm;
}

modification_list parse_olean_modifications(std::string const & olean_code, std::string const & file_name) {
    modification_list ms;
    std::istringstream in(olean_code, std::ios_base::binary);
    scoped_expr_caching enable_caching(false);
    deserializer d(in, optional<std::string>(file_name));
    object_readers & readers = get_object_readers();
    unsigned obj_counter = 0;
    while (true) {
        std::string k;
        unsigned offset = in.tellg();
        d >> k;
        if (k == g_olean_end_file) {
            break;
        }

        auto it = readers.find(k);
        if (it == readers.end())
            throw exception(sstream() << "file '" << file_name << "' has been corrupted at offset " << offset
                                      << ", unknown object: " << k);
        ms.emplace_back(it->second(d));

        obj_counter++;
    }
    if (!in.good()) {
        throw exception(sstream() << "file '" << file_name << "' has been corrupted");
    }
    return ms;
}

void import_module(modification_list const & modifications, std::string const & file_name, environment & env) {
    for (auto & m : modifications) {
        m->perform(env);

        if (auto dm = dynamic_cast<decl_modification const *>(m.get())) {
            env = add_decl_olean(env, dm->m_decl.get_name(), file_name);
        } else if (auto im = dynamic_cast<inductive_modification const *>(m.get())) {
            env = add_decl_olean(env, im->m_decl.get_decl().m_name, file_name);
        }
    }
}

module_loader mk_olean_loader(std::vector<std::string> const & path) {
    bool check_hash = false;
    return[=] (std::string const & module_fn, module_name const & ref) {
        auto base_dir = dirname(module_fn);
        auto fn = find_file(path, base_dir, ref.m_relative, ref.m_name, ".olean");
        std::ifstream in(fn, std::ios_base::binary);
        auto parsed = parse_olean(in, fn, check_hash);
        auto modifs = parse_olean_modifications(parsed.m_serialized_modifications, fn);
        return std::make_shared<loaded_module>(
                loaded_module { fn, parsed.m_imports, modifs,
                                mk_pure_task<bool>(parsed.m_uses_sorry), {} });
    };
}

module_loader mk_dummy_loader() {
    return[=] (std::string const &, module_name const &) -> std::shared_ptr<loaded_module const> {
        throw exception("module importing disabled");
    };
}

void initialize_module() {
    g_ext            = new module_ext_reg();
    g_object_readers = new object_readers();
    decl_modification::init();
    inductive_modification::init();
    quot_modification::init();
    pos_info_mod::init();
}

void finalize_module() {
    quot_modification::finalize();
    pos_info_mod::finalize();
    inductive_modification::finalize();
    decl_modification::finalize();
    delete g_object_readers;
    delete g_ext;
}
}




// ========== aux_definition.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** Helper class for creating closures for nested terms.

    There are two phases:
    1- Parameter and metavariable collection.
    2- Closure creation.

    The methods \c collect are used in the first phase.
    The method \c finalize_collection moves object to the second phase.

    The collection phase collects parameters and metavariables.
    A new parameter is created for each metavariable found in a subterm.

    Parameter and metavariables occurring in the types of collected
    parameters and metavariables are also collected.

    The method \c finalize_collection moves the state to phase 2.
    It also creates a new (normalized) parameter for each collected parameter and metavariable.
    The type of the new parameter is the type of the source after normalization.
    All new parameters are sorted based on dependencies.
*/
class closure_helper {
    type_context_old &  m_ctx;
    name            m_prefix;
    unsigned        m_next_idx;
    name_set        m_found_univ_params;
    name_map<level> m_univ_meta_to_param;
    name_map<level> m_univ_meta_to_param_inv;
    name_set        m_found_local;
    name_map<expr>  m_meta_to_param;
    name_map<expr>  m_meta_to_param_inv;
    buffer<name>    m_level_params;
    buffer<expr>    m_params;
    bool            m_finalized_collection{false};
    buffer<expr>    m_norm_params;

public:
    closure_helper(type_context_old & ctx):
        m_ctx(ctx),
        m_prefix("_aux_param"),
        m_next_idx(0) {}

    type_context_old & ctx() { return m_ctx; }

    /* \pre finalize_collection has not been invoked */
    level collect(level const & l);
    /* \pre finalize_collection has not been invoked */
    levels collect(levels const & ls);
    /* \pre finalize_collection has not been invoked */
    expr collect(expr const & e);

    /* \pre finalize_collection has not been invoked */
    void finalize_collection();

    /* Replace parameters in \c e with corresponding normalized parameters, obtain e', and
       then return (Pi N, e') where N are the normalized parameters.

       Remark \c e must not contain meta-variables. We can ensure this constraint by using the
       collect method

       \pre finalize_collection has been invoked */
    expr mk_pi_closure(expr const & e);

    /* Replace parameters in \c e with corresponding normalized parameters, obtain e', and
       then return (fun N, e') where N are the normalized parameters.

       Remark \c e must not contain meta-variables. We can ensure this constraint by using the
       collect method

       \pre finalize_collection has been invoked */
    expr mk_lambda_closure(expr const & e);

    /* Return the level parameters and meta-variables collected by collect methods.

      \pre finalize_collection has been invoked */
    void get_level_closure(buffer<level> & ls);
    /* Return the parameters and meta-variables collected by collect methods.

      \pre finalize_collection has been invoked */
    void get_expr_closure(buffer<expr> & ps);

    /* Return the normalized paramaters created by this helper object.

       \pre finalize_collection has been invoked */
    buffer<expr> const & get_norm_closure_params() const;

    /* Return the name of normalized parameters. That is, it includes the collected
       level parameters and new parameters created for universe meta-variables.

       \pre finalize_collection has been invoked */
    list<name> get_norm_level_names() const { return to_list(m_level_params); }
};

/** \brief Create an auxiliary definition with name `c` where `type` and `value` may contain local constants and
    meta-variables. This function collects all dependencies (universe parameters, universe metavariables,
    local constants and metavariables). The result is the updated environment and an expression of the form

          (c.{l_1 ... l_n} a_1 ... a_m)

    where l_i's and a_j's are the collected dependencies.

    If is_meta is none, then function also computes whether the new definition should be tagged as trusted or not.

    The updated environment is an extension of ctx.env() */
pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & type, expr const & value,
                                          optional<bool> const & is_meta = optional<bool>());
/** \brief Similar to mk_aux_definition, but the type of value is inferred using ctx. */
pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & value,
                                          optional<bool> const & is_meta = optional<bool>());
/** \brief Similar to mk_aux_definition, but creates a lemma */
pair<environment, expr> mk_aux_lemma(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                     name const & c, expr const & type, expr const & value);

pair<environment, expr> abstract_nested_proofs(environment const & env, metavar_context const & mctx, local_context const & lctx, name const & base_name, expr const & e);
pair<environment, expr> abstract_nested_proofs(environment const & env, name const & base_name, expr const & e);
}




// ========== aux_definition.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/placeholder.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/aux_definition.h"
#include "library/unfold_macros.h"
#include "library/replace_visitor_with_tc.h"

namespace lean {
level closure_helper::collect(level const & l) {
    lean_assert(!m_finalized_collection);
    return replace(l, [&](level const & l) {
            if (is_meta(l)) {
                name const & id = meta_id(l);
                if (auto r = m_univ_meta_to_param.find(id)) {
                    return some_level(*r);
                } else {
                    name n      = m_prefix.append_after(m_next_idx);
                    m_next_idx++;
                    level new_r = mk_param_univ(n);
                    m_univ_meta_to_param.insert(id, new_r);
                    m_univ_meta_to_param_inv.insert(n, l);
                    m_level_params.push_back(n);
                    return some_level(new_r);
                }
            } else if (is_param(l)) {
                lean_assert(!is_placeholder(l));
                name const & id = param_id(l);
                if (!m_found_univ_params.contains(id)) {
                    m_found_univ_params.insert(id);
                    m_level_params.push_back(id);
                }
            }
            return none_level();
        });
}

levels closure_helper::collect(levels const & ls) {
    lean_assert(!m_finalized_collection);
    bool modified = false;
    buffer<level> r;
    for (level const & l : ls) {
        level new_l = collect(l);
        if (new_l != l) modified = true;
        r.push_back(new_l);
    }
    if (!modified)
        return ls;
    else
        return to_list(r);
}

expr closure_helper::collect(expr const & e) {
    lean_assert(!m_finalized_collection);
    return replace(e, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                name const & id = mlocal_name(e);
                if (auto r = m_meta_to_param.find(id)) {
                    return some_expr(*r);
                } else {
                    expr type  = m_ctx.infer(e);
                    expr x     = m_ctx.push_local("_x", type);
                    m_meta_to_param.insert(id, x);
                    m_meta_to_param_inv.insert(mlocal_name(x), e);
                    m_params.push_back(x);
                    return some_expr(x);
                }
            } else if (is_local(e)) {
                name const & id = mlocal_name(e);
                if (!m_found_local.contains(id)) {
                    m_found_local.insert(id);
                    m_params.push_back(e);
                }
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, collect(sort_level(e))));
            } else if (is_constant(e)) {
                return some_expr(update_constant(e, collect(const_levels(e))));
            }
            return none_expr();
        });
}

void closure_helper::finalize_collection() {
    lean_assert(!m_finalized_collection);
    std::sort(m_level_params.begin(), m_level_params.end());
    name_map<expr> new_types;
    for (unsigned i = 0; i < m_params.size(); i++) {
        expr x = m_params[i];
        expr new_type = collect(zeta_expand(m_ctx.lctx(), m_ctx.instantiate_mvars(m_ctx.infer(x))));
        new_types.insert(mlocal_name(x), new_type);
    }
    local_context const & lctx = m_ctx.lctx();
    std::sort(m_params.begin(), m_params.end(), [&](expr const & l1, expr const & l2) {
            return lctx.get_local_decl(l1).get_idx() < lctx.get_local_decl(l2).get_idx();
        });
    for (unsigned i = 0; i < m_params.size(); i++) {
        expr x         = m_params[i];
        expr type      = *new_types.find(mlocal_name(x));
        expr new_type  = replace_locals(type, i, m_params.data(), m_norm_params.data());
        expr new_param = m_ctx.push_local(mlocal_pp_name(x), new_type, local_info(x));
        m_norm_params.push_back(new_param);
    }
    m_finalized_collection = true;
}

expr closure_helper::mk_pi_closure(expr const & e) {
    lean_assert(m_finalized_collection);
    expr new_e  = replace_locals(e, m_params, m_norm_params);
    return m_ctx.mk_pi(m_norm_params, new_e);
}

expr closure_helper::mk_lambda_closure(expr const & e) {
    lean_assert(m_finalized_collection);
    expr new_e  = replace_locals(e, m_params, m_norm_params);
    return m_ctx.mk_lambda(m_norm_params, new_e);
}

void closure_helper::get_level_closure(buffer<level> & ls) {
    lean_assert(m_finalized_collection);
    for (name const & n : m_level_params) {
        if (level const * l = m_univ_meta_to_param_inv.find(n))
            ls.push_back(*l);
        else
            ls.push_back(mk_param_univ(n));
    }
}

void closure_helper::get_expr_closure(buffer<expr> & ps) {
    lean_assert(m_finalized_collection);
    for (expr const & x : m_params) {
        if (expr const * m = m_meta_to_param_inv.find(mlocal_name(x)))
            ps.push_back(*m);
        else
            ps.push_back(x);
    }
}

buffer<expr> const & closure_helper::get_norm_closure_params() const {
    lean_assert(m_finalized_collection);
    return m_norm_params;
}

struct mk_aux_definition_fn : public closure_helper {
    mk_aux_definition_fn(type_context_old & ctx):closure_helper(ctx) {}

    pair<environment, expr> operator()(name const & c, expr const & type, expr const & value, bool is_lemma, optional<bool> const & is_meta) {
        lean_assert(!is_lemma || is_meta);
        lean_assert(!is_lemma || *is_meta == false);
        expr new_type  = collect(ctx().instantiate_mvars(type));
        expr new_value = collect(ctx().instantiate_mvars(value));
        environment env = ctx().env();
        finalize_collection();
        expr def_type  = mk_pi_closure(new_type);
        expr def_value = mk_lambda_closure(new_value);
        bool untrusted = false;
        if (is_meta)
            untrusted = *is_meta;
        else
            untrusted = use_untrusted(env, def_type) || use_untrusted(env, def_value);
        if (!untrusted) {
            def_type  = unfold_untrusted_macros(env, def_type);
            def_value = unfold_untrusted_macros(env, def_value);
        }
        declaration d;
        if (is_lemma) {
            d = mk_theorem(c, get_norm_level_names(), def_type, def_value);
        } else {
            bool use_self_opt = true;
            d = mk_definition(env, c, get_norm_level_names(), def_type, def_value, use_self_opt, !untrusted);
        }
        environment new_env = module::add(env, check(env, d, true));
        buffer<level> ls;
        get_level_closure(ls);
        buffer<expr> ps;
        get_expr_closure(ps);
        expr r = mk_app(mk_constant(c, to_list(ls)), ps);
        return mk_pair(new_env, r);
    }
};

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & type, expr const & value, optional<bool> const & is_meta) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_definition(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                          name const & c, expr const & value, optional<bool> const & is_meta) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    expr type     = ctx.infer(value);
    bool is_lemma = false;
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

pair<environment, expr> mk_aux_lemma(environment const & env, metavar_context const & mctx, local_context const & lctx,
                                     name const & c, expr const & type, expr const & value) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::All);
    bool is_lemma = true;
    optional<bool> is_meta(false);
    return mk_aux_definition_fn(ctx)(c, type, value, is_lemma, is_meta);
}

struct abstract_nested_proofs_fn : public replace_visitor_with_tc {
    name     m_base_name;
    unsigned m_idx{1};

    abstract_nested_proofs_fn(type_context_old & ctx, name const & b):
        replace_visitor_with_tc(ctx),
        m_base_name(b, "_proof") {
    }

    static bool is_atomic(expr const & e) {
        return is_constant(e) || is_local(e);
    }

    name mk_name() {
        environment env = m_ctx.env();
        while (true) {
            name curr = m_base_name.append_after(m_idx);
            m_idx++;
            if (!env.find(curr)) {
                m_ctx.set_env(env);
                return curr;
            }
        }
    }

    optional<expr> is_non_trivial_proof(expr const & e) {
        if (is_atomic(e))
            return none_expr();
        if (is_pi(e) || is_sort(e))
            return none_expr();
        expr type = m_ctx.infer(e);
        if (!m_ctx.is_prop(type))
            return none_expr();
        if (is_app(e)) {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            if (!is_atomic(fn))
                return some_expr(type);
            for (expr const & arg : args) {
                if (!is_atomic(arg))
                    return some_expr(type);
            }
            return none_expr();
        } else {
            return some_expr(type);
        }
    }

    virtual expr visit_mlocal(expr const & e) override {
        return e;
    }

    virtual expr visit(expr const & e) override {
        if (auto type = is_non_trivial_proof(e)) {
            expr new_e = zeta_expand(m_ctx.lctx(), e);
            if (e != new_e) {
                *type = m_ctx.infer(new_e);
            }
            name n = mk_name();
            auto new_env_new_e = mk_aux_lemma(m_ctx.env(), m_ctx.mctx(), m_ctx.lctx(), n, *type, new_e);
            m_ctx.set_env(new_env_new_e.first);
            return new_env_new_e.second;
        } else {
            return replace_visitor_with_tc::visit(e);
        }
    }

    pair<environment, expr> operator()(expr const & e) {
        expr new_e = replace_visitor_with_tc::operator()(e);
        return mk_pair(m_ctx.env(), new_e);
    }
};

pair<environment, expr> abstract_nested_proofs(environment const & env, metavar_context const & mctx, local_context const & lctx, name const & base_name, expr const & e) {
    type_context_old ctx(env, options(), mctx, lctx, transparency_mode::Semireducible);
    return abstract_nested_proofs_fn(ctx, base_name)(e);
}

pair<environment, expr> abstract_nested_proofs(environment const & env, name const & base_name, expr const & e) {
    lean_assert(!has_metavar(e));
    return abstract_nested_proofs(env, metavar_context(), local_context(), base_name, e);
}
}




// ========== congr_lemma.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class type_context_old;

enum class congr_arg_kind {
    /* It is a parameter for the congruence lemma, the parameter occurs in the left and right hand sides. */
    Fixed,
    /* It is not a parameter for the congruence lemma, the lemma was specialized for this parameter.
       This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. */
    FixedNoParam,
    /* The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i = b_i).
       a_i and b_i represent the left and right hand sides, and eq_i is a proof for their equality. */
    Eq,
    /* congr-simp lemma contains only one parameter for this kind of argument, and congr-lemmas contains two.
       They correspond to arguments that are subsingletons/propositions. */
    Cast,
    /* The lemma contains three parameters for this kind of argument a_i, b_i and (eq_i : a_i == b_i).
       a_i and b_i represent the left and right hand sides, and eq_i is a proof for their heterogeneous equality. */
    HEq
};

class congr_lemma {
    expr                 m_type;
    expr                 m_proof;
    list<congr_arg_kind> m_arg_kinds;
public:
    congr_lemma(expr const & type, expr const & proof, list<congr_arg_kind> const & ks):
        m_type(type), m_proof(proof), m_arg_kinds(ks) {}
    expr const & get_type() const { return m_type; }
    expr const & get_proof() const { return m_proof; }
    list<congr_arg_kind> const & get_arg_kinds() const { return m_arg_kinds; }
    bool all_eq_kind() const;
};

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn, unsigned nargs);
/* Create a specialized theorem using (a prefix of) the arguments of the given application. */
optional<congr_lemma> mk_specialized_congr_simp(type_context_old & ctx, expr const & a);

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn, unsigned nargs);
/* Create a specialized theorem using (a prefix of) the arguments of the given application. */
optional<congr_lemma> mk_specialized_congr(type_context_old & ctx, expr const & a);

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn);
optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn, unsigned nargs);

void initialize_congr_lemma();
void finalize_congr_lemma();
}




// ========== congr_lemma.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/congr_lemma.h"
#include "library/expr_unsigned_map.h"
#include "library/relation_manager.h"
#include "library/cache_helper.h"
#include "library/app_builder.h"
#include "library/fun_info.h"

namespace lean {
bool congr_lemma::all_eq_kind() const {
    return std::all_of(m_arg_kinds.begin(), m_arg_kinds.end(),
                       [](congr_arg_kind k) { return k == congr_arg_kind::Eq; });
}

struct congr_lemma_cache {
    typedef expr_unsigned_map<congr_lemma>  cache;
    environment          m_env;
    cache                m_simp_cache;
    cache                m_simp_cache_spec;
    cache                m_cache;
    cache                m_cache_spec;
    cache                m_hcache;
    congr_lemma_cache(environment const & env):
        m_env(env) {}
    environment const & env() const { return m_env; }
};

typedef cache_compatibility_helper<congr_lemma_cache> congr_lemma_cache_helper;

/* CACHE_RESET: YES */
MK_THREAD_LOCAL_GET_DEF(congr_lemma_cache_helper, get_clch);

congr_lemma_cache & get_congr_lemma_cache_for(type_context_old const & ctx) {
    return get_clch().get_cache_for(ctx);
}

struct congr_lemma_manager {
    typedef expr_unsigned key;
    typedef congr_lemma result;
    type_context_old &      m_ctx;
    congr_lemma_cache & m_cache;

    congr_lemma_manager(type_context_old & ctx):
        m_ctx(ctx), m_cache(get_congr_lemma_cache_for(ctx)) {}

    expr infer(expr const & e) { return m_ctx.infer(e); }
    expr whnf(expr const & e) { return m_ctx.whnf(e); }
    expr relaxed_whnf(expr const & e) { return m_ctx.relaxed_whnf(e); }

    /** \brief (Try to) cast expression \c e to the given type using the equations \c eqs.
        \c deps contains the indices of the relevant equalities.
        \remark deps is sorted. */
    expr cast(expr const & e, expr const & type, list<unsigned> const & deps, buffer<optional<expr>> const & eqs) {
        if (!deps)
            return e;
        unsigned d = head(deps);
        auto major = eqs[d];
        if (!major) {
            return cast(e, type, tail(deps), eqs);
        } else {
            expr lhs, rhs;
            lean_verify(is_eq(m_ctx.infer(*major), lhs, rhs));
            lean_assert(is_local(lhs));
            lean_assert(is_local(rhs));
            // We compute the new type by replacing rhs with lhs, and major with (refl lhs).
            expr motive, new_type;
            bool use_drec;
            if (depends_on(type, *major)) {
                // Since the type depends on the major, we must use dependent elimination.
                // and the motive just abstract rhs and *major
                use_drec  = true;
                motive    = m_ctx.mk_lambda({rhs, *major}, type);
                // We compute new_type by replacing rhs with lhs and *major with eq.refl(lhs) in type.
                new_type  = instantiate(abstract_local(type, rhs), lhs);
                expr refl = mk_eq_refl(m_ctx, lhs);
                new_type  = instantiate(abstract_local(new_type, *major), refl);
            } else {
                // type does not depend on the *major.
                // So, the motive is just (fun rhs, type), and
                // new_type just replaces rhs with lhs.
                use_drec = false;
                motive   = m_ctx.mk_lambda({rhs}, type);
                new_type = instantiate(abstract_local(type, rhs), lhs);
            }
            expr minor = cast(e, new_type, tail(deps), eqs);
            if (use_drec) {
                return mk_eq_drec(m_ctx, motive, minor, *major);
            } else {
                return mk_eq_rec(m_ctx, motive, minor, *major);
            }
        }
    }

    bool has_cast(buffer<congr_arg_kind> const & kinds) {
        return std::find(kinds.begin(), kinds.end(), congr_arg_kind::Cast) != kinds.end();
    }

    /** \brief Create simple congruence theorem using just congr, congr_arg, and congr_fun lemmas.
        \pre There are no "cast" arguments. */
    expr mk_simple_congr_proof(expr const & fn, buffer<expr> const & lhss,
                               buffer<optional<expr>> const & eqs, buffer<congr_arg_kind> const & kinds) {
        lean_assert(!has_cast(kinds));
        unsigned i = 0;
        for (; i < kinds.size(); i++) {
            if (kinds[i] != congr_arg_kind::Fixed)
                break;
        }
        expr g = mk_app(fn, i, lhss.data());
        if (i == kinds.size())
            return mk_eq_refl(m_ctx, g);
        lean_assert(kinds[i] == congr_arg_kind::Eq);
        lean_assert(eqs[i]);
        bool skip_arrow_test = true;
        expr pr = mk_congr_arg(m_ctx, g, *eqs[i], skip_arrow_test);
        i++;
        for (; i < kinds.size(); i++) {
            if (kinds[i] == congr_arg_kind::Eq) {
                bool skip_arrow_test = true;
                pr = ::lean::mk_congr(m_ctx, pr, *eqs[i], skip_arrow_test);
            } else {
                lean_assert(kinds[i] == congr_arg_kind::Fixed);
                pr = mk_congr_fun(m_ctx, pr, lhss[i]);
            }
        }
        return pr;
    }

    /** \brief Given a the set of hypotheses \c eqs, build a proof for <tt>lhs = rhs</tt> using \c eq.drec and \c eqs.
        \remark eqs are the proofs for the Eq arguments.
        \remark This is an auxiliary method used by mk_congr_simp. */
    expr mk_congr_proof(unsigned i, expr const & lhs, expr const & rhs, buffer<optional<expr>> const & eqs) {
        if (i == eqs.size()) {
            return mk_eq_refl(m_ctx, rhs);
        } else if (!eqs[i]) {
            return mk_congr_proof(i+1, lhs, rhs, eqs);
        } else {
            expr major = *eqs[i];
            expr x_1, x_2;
            lean_verify(is_eq(m_ctx.infer(major), x_1, x_2));
            lean_assert(is_local(x_1));
            lean_assert(is_local(x_2));
            expr motive_eq = mk_eq(m_ctx, lhs, rhs);
            expr motive    = m_ctx.mk_lambda({x_2, major}, motive_eq);
            // We compute the new_rhs by replacing x_2 with x_1 and major with (eq.refl x_1) in rhs.
            expr new_rhs = instantiate(abstract_local(rhs, x_2), x_1);
            expr x1_refl = mk_eq_refl(m_ctx, x_1);
            new_rhs      = instantiate(abstract_local(new_rhs, major), x1_refl);
            expr minor   = mk_congr_proof(i+1, lhs, new_rhs, eqs);
            return mk_eq_drec(m_ctx, motive, minor, major);
        }
    }

    void trace_too_many_arguments(expr const & fn, unsigned nargs) {
        lean_trace("congr_lemma", tout() << "failed to generate lemma for (" << fn << ") with " << nargs
                   << " arguments, too many arguments\n";);
    }

    void trace_app_builder_failure(expr const & fn) {
        lean_trace("congr_lemma", tout() << "failed to generate lemma for (" << fn << "), "
                   << " failed to build proof (enable 'trace.app_builder' for details)\n";);
    }

    /** \brief Create a congruence lemma that is useful for the simplifier.
        In this kind of lemma, if the i-th argument is a Cast argument, then the lemma
        contains an input a_i representing the i-th argument in the left-hand-side, and
        it appears with a cast (e.g., eq.drec ... a_i ...) in the right-hand-side.
        The idea is that the right-hand-side of this lemma "tells" the simplifier
        how the resulting term looks like. */
    optional<result> mk_congr_simp(expr const & fn, buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type = relaxed_whnf(infer(fn));
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;          // it contains the right-hand-side argument
            buffer<optional<expr>> eqs; // for Eq args, it contains the equality
            buffer<expr> hyps;          // contains lhss + rhss + eqs
            for (unsigned i = 0; i < pinfos.size(); i++) {
                if (!is_pi(fn_type)) {
                    trace_too_many_arguments(fn, pinfos.size());
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type);
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    expr rhs     = locals.push_local_from_binding(fn_type);
                    expr eq_type = mk_eq(m_ctx, lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = locals.push_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    break;
                }
                case congr_arg_kind::HEq:
                    lean_unreachable();
                case congr_arg_kind::Fixed:
                    rhss.push_back(lhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::FixedNoParam:
                    lean_unreachable(); // TODO(Leo): not implemented yet
                    break;
                case congr_arg_kind::Cast: {
                    expr rhs_type = m_ctx.infer(lhs);
                    rhs_type = instantiate_rev(abstract_locals(rhs_type, lhss.size()-1, lhss.data()),
                                               rhss.size(), rhss.data());
                    expr rhs = cast(lhs, rhs_type, pinfos[i].get_back_deps(), eqs);
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                }}
                fn_type  = relaxed_whnf(instantiate(binding_body(fn_type), lhs));
            }
            expr lhs = mk_app(fn, lhss);
            expr rhs = mk_app(fn, rhss);
            expr eq  = mk_eq(m_ctx, lhs, rhs);
            expr congr_type  = m_ctx.mk_pi(hyps, eq);
            expr congr_proof;
            if (has_cast(kinds)) {
                congr_proof = mk_congr_proof(0, lhs, rhs, eqs);
            } else {
                congr_proof = mk_simple_congr_proof(fn, lhss, eqs, kinds);
            }
            congr_proof = m_ctx.mk_lambda(hyps, congr_proof);
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    /** \brief Create a congruence lemma for the congruence closure module.
        In this kind of lemma, if the i-th argument is a Cast argument, then the lemma
        contains two inputs a_i and b_i representing the i-th argument in the left-hand-side and
        right-hand-side.
        This lemma is based on the congruence lemma for the simplifier.
        It uses subsinglenton elimination to show that the congr-simp lemma right-hand-side
        is equal to the right-hand-side of this lemma. */
    optional<result> mk_congr(expr const & fn, optional<result> const & simp_lemma,
                              buffer<param_info> const & pinfos, buffer<congr_arg_kind> const & kinds) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type1 = whnf(infer(fn));
            expr fn_type2 = fn_type1;
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;          // it contains the right-hand-side argument
            buffer<optional<expr>> eqs; // for Eq args, it contains the equality
            buffer<expr> hyps;          // contains lhss + rhss + eqs
            buffer<expr> simp_lemma_args;
            for (unsigned i = 0; i < pinfos.size(); i++) {
                if (!is_pi(fn_type1)) {
                    trace_too_many_arguments(fn, pinfos.size());
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type1);
                expr rhs;
                lhss.push_back(lhs);
                hyps.push_back(lhs);
                simp_lemma_args.push_back(lhs);
                switch (kinds[i]) {
                case congr_arg_kind::Eq: {
                    lean_assert(m_ctx.is_def_eq(binding_domain(fn_type1), binding_domain(fn_type2)));
                    rhs          = locals.push_local_from_binding(fn_type2);
                    expr eq_type = mk_eq(m_ctx, lhs, rhs);
                    rhss.push_back(rhs);
                    expr eq = locals.push_local(e_name.append_after(eqs.size()+1), eq_type);
                    eqs.push_back(some_expr(eq));
                    hyps.push_back(rhs);
                    hyps.push_back(eq);
                    simp_lemma_args.push_back(rhs);
                    simp_lemma_args.push_back(eq);
                    break;
                }
                case congr_arg_kind::HEq:
                    lean_unreachable();
                case congr_arg_kind::Fixed:
                    rhs = lhs;
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    break;
                case congr_arg_kind::FixedNoParam:
                    lean_unreachable(); // TODO(Leo): not implemented yet
                    break;
                case congr_arg_kind::Cast: {
                    rhs     = locals.push_local_from_binding(fn_type2);
                    rhss.push_back(rhs);
                    eqs.push_back(none_expr());
                    hyps.push_back(rhs);
                    break;
                }}
                fn_type1  = whnf(instantiate(binding_body(fn_type1), lhs));
                fn_type2  = whnf(instantiate(binding_body(fn_type2), rhs));
            }
            expr fst   = mk_app(simp_lemma->get_proof(), simp_lemma_args);
            expr type1 = simp_lemma->get_type();
            while (is_pi(type1))
                type1 = binding_body(type1);
            type1      = instantiate_rev(type1, simp_lemma_args.size(), simp_lemma_args.data());
            expr lhs1, rhs1;
            lean_verify(is_eq(type1, lhs1, rhs1));
            // build proof2
            expr rhs2 = mk_app(fn, rhss);
            expr eq   = mk_eq(m_ctx, lhs1, rhs2);
            expr congr_type = m_ctx.mk_pi(hyps, eq);
            // build proof that rhs1 = rhs2
            unsigned i;
            for (i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop())
                    break;
            }
            if (i == kinds.size()) {
                // rhs1 and rhs2 are definitionally equal
                expr congr_proof = m_ctx.mk_lambda(hyps, fst);
                return optional<result>(congr_type, congr_proof, to_list(kinds));
            }
            buffer<expr> rhss1;
            get_app_args_at_most(rhs1, rhss.size(), rhss1);
            lean_assert(rhss.size() == rhss1.size());
            expr a   = mk_app(fn, i, rhss1.data());
            expr snd = mk_eq_refl(m_ctx, a);
            for (; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast && !pinfos[i].is_prop()) {
                    expr r1   = rhss1[i];
                    expr r2   = rhss[i];
                    expr r1_eq_r2 = mk_app(m_ctx, get_subsingleton_elim_name(), r1, r2);
                    snd = ::lean::mk_congr(m_ctx, snd, r1_eq_r2);
                } else {
                    snd = mk_congr_fun(m_ctx, snd, rhss[i]);
                }
            }
            expr congr_proof = m_ctx.mk_lambda(hyps, mk_eq_trans(m_ctx, fst, snd));
            return optional<result>(congr_type, congr_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs,
                                   fun_info const & finfo, ss_param_infos const & ssinfos) {
        auto r = m_cache.m_simp_cache.find(key(fn, nargs));
        if (r != m_cache.m_simp_cache.end())
            return optional<result>(r->second);
        list<unsigned> const & result_deps = finfo.get_result_deps();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        buffer<ss_param_info>  ssinfos_buffer;
        to_buffer(finfo.get_params_info(), pinfos);
        to_buffer(ssinfos, ssinfos_buffer);
        kinds.resize(pinfos.size(), congr_arg_kind::Eq);
        for (unsigned i = 0; i < pinfos.size(); i++) {
            if (std::find(result_deps.begin(), result_deps.end(), i) != result_deps.end()) {
                kinds[i] = congr_arg_kind::Fixed;
            } else if (ssinfos_buffer[i].is_subsingleton()) {
                // See comment at mk_congr.
                if (!pinfos[i].is_prop() && pinfos[i].has_fwd_deps())
                    kinds[i] = congr_arg_kind::Fixed;
                else
                    kinds[i] = congr_arg_kind::Cast;
            } else if (pinfos[i].is_inst_implicit()) {
                lean_assert(!ssinfos_buffer[i].is_subsingleton());
                kinds[i] = congr_arg_kind::Fixed;
            }
        }
        for (unsigned i = 0; i < pinfos.size(); i++) {
            for (unsigned j = i+1; j < pinfos.size(); j++) {
                auto j_deps = pinfos[j].get_back_deps();
                if (std::find(j_deps.begin(), j_deps.end(), i) != j_deps.end() &&
                    kinds[j] == congr_arg_kind::Eq) {
                    // We must fix i because there is a j that depends on i,
                    // and j is not fixed nor a cast-fixed.
                    kinds[i] = congr_arg_kind::Fixed;
                    break;
                }
            }
        }
        auto new_r = mk_congr_simp(fn, pinfos, kinds);
        if (new_r) {
            m_cache.m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
            return new_r;
        } else if (has_cast(kinds)) {
            // remove casts and try again
            for (unsigned i = 0; i < kinds.size(); i++) {
                if (kinds[i] == congr_arg_kind::Cast)
                    kinds[i] = congr_arg_kind::Fixed;
            }
            auto new_r = mk_congr_simp(fn, pinfos, kinds);
            if (new_r) {
                m_cache.m_simp_cache.insert(mk_pair(key(fn, nargs), *new_r));
                return new_r;
            } else {
                return new_r;
            }
        } else {
            return new_r;
        }
    }

    optional<result> mk_congr_simp(expr const & fn, unsigned nargs) {
        fun_info finfo         = get_fun_info(m_ctx, fn, nargs);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn, nargs);
        return mk_congr_simp(fn, nargs, finfo, ssinfos);
    }

    optional<result> mk_congr(expr const & fn, unsigned nargs,
                              fun_info const & finfo, ss_param_infos const & ssinfos) {
        auto r = m_cache.m_cache.find(key(fn, nargs));
        if (r != m_cache.m_cache.end())
            return optional<result>(r->second);
        optional<result> simp_lemma = mk_congr_simp(fn, nargs);
        if (!simp_lemma)
            return optional<result>();
        buffer<congr_arg_kind> kinds;
        buffer<param_info>     pinfos;
        buffer<ss_param_info>  ssinfos_buffer;
        to_buffer(simp_lemma->get_arg_kinds(), kinds);
        to_buffer(finfo.get_params_info(), pinfos);
        to_buffer(ssinfos, ssinfos_buffer);
        // For congr lemmas we have the following restriction:
        // if a Cast arg is subsingleton, it is not a proposition,
        // and it is a dependent argument, then we mark it as fixed.
        // This restriction doesn't affect the standard library,
        // but it simplifies the implementation.
        lean_assert(kinds.size() == pinfos.size());
        bool has_cast = false;
        for (unsigned i = 0; i < kinds.size(); i++) {
            if (!pinfos[i].is_prop() && ssinfos_buffer[i].is_subsingleton() && pinfos[i].has_fwd_deps()) {
                kinds[i] = congr_arg_kind::Fixed;
            }
            if (kinds[i] == congr_arg_kind::Cast)
                has_cast = true;
        }
        if (!has_cast) {
            m_cache.m_cache.insert(mk_pair(key(fn, nargs), *simp_lemma));
            return simp_lemma; // simp_lemma will be identical to regular congr lemma
        }
        auto new_r = mk_congr(fn, simp_lemma, pinfos, kinds);
        if (new_r)
            m_cache.m_cache.insert(mk_pair(key(fn, nargs), *new_r));
        return new_r;
    }

    void pre_specialize(expr const & a, expr & g, unsigned & prefix_sz, unsigned & num_rest_args) {
        ss_param_infos ssinfos = get_specialized_subsingleton_info(m_ctx, a);
        prefix_sz = 0;
        for (ss_param_info const & ssinfo : ssinfos) {
            if (!ssinfo.specialized())
                break;
            prefix_sz++;
        }
        num_rest_args = get_app_num_args(a) - prefix_sz;
        g = a;
        for (unsigned i = 0; i < num_rest_args; i++) {
            g = app_fn(g);
        }
    }

    result mk_specialize_result(result const & r, unsigned prefix_sz) {
        list<congr_arg_kind> new_arg_kinds = r.get_arg_kinds();
        for (unsigned i = 0; i < prefix_sz; i++)
            new_arg_kinds = cons(congr_arg_kind::FixedNoParam, new_arg_kinds);
        return result(r.get_type(), r.get_proof(), new_arg_kinds);
    }

    expr mk_hcongr_proof(expr type) {
        expr A, B, a, b;
        if (is_eq(type, a, b)) {
            return mk_eq_refl(m_ctx, a);
        } else if (is_heq(type, A, a, B, b)) {
            return mk_heq_refl(m_ctx, a);
        } else {
            type_context_old::tmp_locals locals(m_ctx);
            lean_assert(is_pi(type) && is_pi(binding_body(type)) && is_pi(binding_body(binding_body(type))));
            expr a      = locals.push_local_from_binding(type);
            type        = instantiate(binding_body(type), a);
            expr b      = locals.push_local_from_binding(type);
            expr motive = instantiate(binding_body(type), b);
            type        = instantiate(binding_body(type), a);
            expr eq_pr  = locals.push_local_from_binding(motive);
            type        = binding_body(type);
            motive      = binding_body(motive);
            lean_assert(closed(type) && closed(motive));
            expr minor  = mk_hcongr_proof(type);
            expr major  = eq_pr;
            if (is_heq(m_ctx.infer(eq_pr)))
                major  = mk_eq_of_heq(m_ctx, eq_pr);
            motive      = m_ctx.mk_lambda({b}, motive);
            return m_ctx.mk_lambda({a, b, eq_pr}, mk_eq_rec(m_ctx, motive, minor, major));
        }
    }

    optional<result> mk_hcongr_core(expr const & fn, unsigned nargs) {
        try {
            type_context_old::tmp_locals locals(m_ctx);
            expr fn_type_lhs = relaxed_whnf(infer(fn));
            expr fn_type_rhs = fn_type_lhs;
            name e_name("e");
            buffer<expr> lhss;
            buffer<expr> rhss;
            buffer<expr> eqs;
            buffer<expr> hyps;    // contains lhss + rhss + eqs
            buffer<congr_arg_kind> kinds;
            for (unsigned i = 0; i < nargs; i++) {
                if (!is_pi(fn_type_lhs)) {
                    trace_too_many_arguments(fn, nargs);
                    return optional<result>();
                }
                expr lhs = locals.push_local_from_binding(fn_type_lhs);
                lhss.push_back(lhs); hyps.push_back(lhs);
                expr rhs = locals.push_local(binding_name(fn_type_rhs).append_after("'"), binding_domain(fn_type_rhs));
                rhss.push_back(rhs); hyps.push_back(rhs);
                expr eq_type;
                expr domain_lhs = consume_auto_opt_param(binding_domain(fn_type_lhs));
                expr domain_rhs = consume_auto_opt_param(binding_domain(fn_type_rhs));
                if (domain_lhs == domain_rhs) {
                    eq_type = mk_eq(m_ctx, lhs, rhs);
                    kinds.push_back(congr_arg_kind::Eq);
                } else {
                    eq_type = mk_heq(m_ctx, lhs, rhs);
                    kinds.push_back(congr_arg_kind::HEq);
                }
                expr h_eq = locals.push_local(e_name.append_after(i), eq_type);
                eqs.push_back(h_eq); hyps.push_back(h_eq);
                fn_type_lhs  = relaxed_whnf(instantiate(binding_body(fn_type_lhs), lhs));
                fn_type_rhs  = relaxed_whnf(instantiate(binding_body(fn_type_rhs), rhs));
            }
            expr lhs = mk_app(fn, lhss);
            expr rhs = mk_app(fn, rhss);
            expr eq_type = mk_heq(m_ctx, lhs, rhs);
            expr result_type  = m_ctx.mk_pi(hyps, eq_type);
            expr result_proof = mk_hcongr_proof(result_type);
            return optional<result>(result_type, result_proof, to_list(kinds));
        } catch (app_builder_exception &) {
            trace_app_builder_failure(fn);
            return optional<result>();
        }
    }

    optional<result> mk_congr_simp(expr const & fn) {
        fun_info finfo         = get_fun_info(m_ctx, fn);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn);
        return mk_congr_simp(fn, finfo.get_arity(), finfo, ssinfos);
    }

    optional<result> mk_specialized_congr_simp(expr const & a) {
        lean_assert(is_app(a));
        expr g; unsigned prefix_sz, num_rest_args;
        pre_specialize(a, g, prefix_sz, num_rest_args);
        key k(g, num_rest_args);
        auto it = m_cache.m_simp_cache_spec.find(k);
        if (it != m_cache.m_simp_cache_spec.end())
            return optional<result>(it->second);
        auto r = mk_congr_simp(g, num_rest_args);
        if (!r)
            return optional<result>();
        result new_r = mk_specialize_result(*r, prefix_sz);
        m_cache.m_simp_cache_spec.insert(mk_pair(k, new_r));
        return optional<result>(new_r);
    }

    optional<result> mk_congr(expr const & fn, unsigned nargs) {
        fun_info finfo = get_fun_info(m_ctx, fn, nargs);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn, nargs);
        return mk_congr(fn, nargs, finfo, ssinfos);
    }

    optional<result> mk_congr(expr const & fn) {
        fun_info finfo = get_fun_info(m_ctx, fn);
        ss_param_infos ssinfos = get_subsingleton_info(m_ctx, fn);
        return mk_congr(fn, finfo.get_arity(), finfo, ssinfos);
    }

    optional<result> mk_specialized_congr(expr const & a) {
        lean_assert(is_app(a));
        expr g; unsigned prefix_sz, num_rest_args;
        pre_specialize(a, g, prefix_sz, num_rest_args);
        key k(g, num_rest_args);
        auto it = m_cache.m_cache_spec.find(k);
        if (it != m_cache.m_cache_spec.end())
            return optional<result>(it->second);
        auto r = mk_congr(g, num_rest_args);
        if (!r) {
            return optional<result>();
        }
        result new_r = mk_specialize_result(*r, prefix_sz);
        m_cache.m_cache_spec.insert(mk_pair(k, new_r));
        return optional<result>(new_r);
    }

    optional<result> mk_hcongr(expr const & fn, unsigned nargs) {
        auto r = m_cache.m_hcache.find(key(fn, nargs));
        if (r != m_cache.m_hcache.end())
            return optional<result>(r->second);
        auto new_r = mk_hcongr_core(fn, nargs);
        if (new_r)
            m_cache.m_hcache.insert(mk_pair(key(fn, nargs), *new_r));
        return new_r;
    }

    optional<result> mk_hcongr(expr const & fn) {
        fun_info finfo = get_fun_info(m_ctx, fn);
        return mk_hcongr(fn, finfo.get_arity());
    }
};

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_congr_simp(fn);
}

optional<congr_lemma> mk_congr_simp(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_congr_simp(fn, nargs);
}

optional<congr_lemma> mk_specialized_congr_simp(type_context_old & ctx, expr const & a) {
    return congr_lemma_manager(ctx).mk_specialized_congr_simp(a);
}

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_congr(fn);
}

optional<congr_lemma> mk_congr(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_congr(fn, nargs);
}

optional<congr_lemma> mk_specialized_congr(type_context_old & ctx, expr const & a) {
    return congr_lemma_manager(ctx).mk_specialized_congr(a);
}

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn) {
    return congr_lemma_manager(ctx).mk_hcongr(fn);
}

optional<congr_lemma> mk_hcongr(type_context_old & ctx, expr const & fn, unsigned nargs) {
    return congr_lemma_manager(ctx).mk_hcongr(fn, nargs);
}

void initialize_congr_lemma() {
    register_trace_class("congr_lemma");
    register_thread_local_reset_fn([]() { get_clch().clear(); });
}
void finalize_congr_lemma() {
}
}




// ========== inverse.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
struct inverse_info {
    unsigned m_arity;
    name     m_inv;
    unsigned m_inv_arity;
    name     m_lemma;
};

optional<inverse_info> has_inverse(environment const & env, name const & fn);
optional<name> is_inverse(environment const & env, name const & inv);
environment add_inverse_lemma(environment const & env, name const & lemma, bool persistent);
void initialize_inverse();
void finalize_inverse();
}




// ========== inverse.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/attribute_manager.h"
#include "library/inverse.h"

namespace lean {
struct inverse_entry {
    name         m_fn;
    inverse_info m_info;
    inverse_entry() {}
    inverse_entry(name const & fn, inverse_info const & info):
        m_fn(fn), m_info(info) {}
};

struct inverse_state {
    name_map<inverse_info> m_fn_info;  /* mapping from function to its inverse and lemma */
    name_map<name>         m_inv_info; /* mapping from inverse to function */

    void add(inverse_entry const & e) {
        m_fn_info.insert(e.m_fn, e.m_info);
        m_inv_info.insert(e.m_info.m_inv, e.m_fn);
    }
};

static name * g_inverse_name = nullptr;

struct inverse_config {
    typedef inverse_state state;
    typedef inverse_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.add(e);
    }
    static name const & get_class_name() {
        return *g_inverse_name;
    }
    static const char * get_serialization_key() {
        return "inverse";
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e.m_fn << e.m_info.m_arity << e.m_info.m_inv << e.m_info.m_inv_arity << e.m_info.m_lemma;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_fn >> e.m_info.m_arity >> e.m_info.m_inv >> e.m_info.m_inv_arity >> e.m_info.m_lemma;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.m_info.m_lemma.hash());
    }
};

template class scoped_ext<inverse_config>;
typedef scoped_ext<inverse_config> inverse_ext;

optional<inverse_info> has_inverse(environment const & env, name const & fn) {
    if (auto r = inverse_ext::get_state(env).m_fn_info.find(fn))
        return optional<inverse_info>(*r);
    else
        return optional<inverse_info>();
}

optional<name> is_inverse(environment const & env, name const & inv) {
    if (auto r = inverse_ext::get_state(env).m_inv_info.find(inv))
        return optional<name>(*r);
    else
        return optional<name>();
}

void throw_inverse_error() {
    throw exception("invalid inverse lemma, "
                    "it should be of the form: (f ... (g ... x)) = x");
}

environment add_inverse_lemma(environment const & env, name const & lemma, bool persistent) {
    type_checker tc(env);
    declaration d = env.get(lemma);
    buffer<expr> tele;
    expr type     = to_telescope(tc, d.get_type(), tele);
    expr lhs, rhs;
    if (!is_eq(type, lhs, rhs) || !is_app(lhs) || !is_constant(get_app_fn(lhs)) || !is_local(rhs))
        throw_inverse_error();
    inverse_info info;
    buffer<expr> lhs_args;
    expr const & lhs_fn = get_app_args(lhs, lhs_args);
    info.m_inv       = const_name(lhs_fn);
    info.m_inv_arity = lhs_args.size();
    info.m_lemma     = lemma;
    expr const & last_arg = lhs_args.back();
    if (!is_app(last_arg) || !is_constant(get_app_fn(last_arg)))
        throw_inverse_error();
    buffer<expr> last_arg_args;
    expr const & fn = get_app_args(last_arg, last_arg_args);
    if (last_arg_args.back() != rhs)
        throw_inverse_error();
    info.m_arity = last_arg_args.size();
    return inverse_ext::add_entry(env, get_dummy_ios(), inverse_entry(const_name(fn), info), persistent);
}

void initialize_inverse() {
    g_inverse_name = new name("inverse");
    inverse_ext::initialize();

    register_system_attribute(basic_attribute("inverse", "attribute for marking inverse lemmas "
                                              "used by the equation compiler",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_inverse_lemma(env, d, persistent);
                                              }));
}

void finalize_inverse() {
    inverse_ext::finalize();
    delete g_inverse_name;
}
}




// ========== fun_info.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class type_context_old;

/** \brief Function parameter information. */
class param_info {
    unsigned       m_implicit:1;
    unsigned       m_inst_implicit:1;
    unsigned       m_prop:1;
    unsigned       m_has_fwd_deps:1; // true if rest depends on this parameter
    list<unsigned> m_back_deps;      // previous arguments it depends on
public:
    param_info(bool imp, bool inst_imp, bool prop, bool has_fwd_deps, list<unsigned> const & back_deps):
        m_implicit(imp), m_inst_implicit(inst_imp), m_prop(prop),
        m_has_fwd_deps(has_fwd_deps), m_back_deps(back_deps) {}
    list<unsigned> const & get_back_deps() const { return m_back_deps; }
    bool is_implicit() const { return m_implicit; }
    bool is_inst_implicit() const { return m_inst_implicit; }
    bool is_prop() const { return m_prop; }
    bool has_fwd_deps() const { return m_has_fwd_deps; }
    void set_has_fwd_deps() { m_has_fwd_deps = true; }
};

/** \brief Function information produced by get_fun_info procedures. */
class fun_info {
    unsigned         m_arity;
    list<param_info> m_params_info;
    list<unsigned>   m_result_deps; // resulting type dependencies
public:
    fun_info():m_arity(0) {}
    fun_info(unsigned arity, list<param_info> const & info, list<unsigned> const & result_deps):
        m_arity(arity), m_params_info(info), m_result_deps(result_deps) {}
    unsigned get_arity() const { return m_arity; }
    list<param_info> const & get_params_info() const { return m_params_info; }
    list<unsigned> const & get_result_deps() const { return m_result_deps; }
};

fun_info get_fun_info(type_context_old & ctx, expr const & fn);
/** \brief Return information assuming the function has only nargs.
    \pre nargs <= get_fun_info(ctx, fn).get_arity() */
fun_info get_fun_info(type_context_old & ctx, expr const & fn, unsigned nargs);

/** \brief Subsingleton parameter information */
class subsingleton_param_info {
    /* m_specialized is true if the result of fun_info has been specifialized
       using this argument.
       For example, consider the function

             f : Pi (A : Type), A -> A

       Now, suppse we request get_specialize fun_info for the application

             f unit a

       fun_info_manager returns two param_info objects:
       1) m_specialized = true
       2) m_subsingleton = true

       Note that, in general, the second argument of f is not a subsingleton,
       but it is in this particular case/specialization.

       \remark This bit is only set if it is a dependent parameter (i.e., m_is_dep is true).

       Moreover, we only set m_specialized IF another parameter
       becomes a subsingleton or proposition. */
    unsigned short m_specialized;
    unsigned short m_subsingleton;
public:
    subsingleton_param_info(bool spec, bool ss):
        m_specialized(spec), m_subsingleton(ss) {}
    bool specialized() const { return m_specialized; }
    bool is_subsingleton() const { return m_subsingleton; }
    void set_specialized() { m_specialized = true; }
};

typedef subsingleton_param_info ss_param_info;
typedef list<ss_param_info>     ss_param_infos;

list<ss_param_info> get_subsingleton_info(type_context_old & ctx, expr const & fn);
list<ss_param_info> get_subsingleton_info(type_context_old & ctx, expr const & fn, unsigned nargs);
/** \brief Return subsingleton parameter information for the function application.
    This is more precise than \c get_subsingleton_info for dependent functions.

    Example: given (f : Pi (A : Type), A -> A), \c get_specialized_fun_info for

    f unit b

    returns a \c fun_info with two param_info
    1) m_specialized = true
    2) m_subsingleton = true

    The second argument is marked as subsingleton only because the resulting information
    is taking into account the first argument. */
list<ss_param_info> get_specialized_subsingleton_info(type_context_old & ctx, expr const & app);
unsigned get_specialization_prefix_size(type_context_old & ctx, expr const & fn, unsigned nargs);

void initialize_fun_info();
void finalize_fun_info();
}




// ========== fun_info.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/expr_unsigned_map.h"
#include "library/fun_info.h"
#include "library/cache_helper.h"

namespace lean {
static name * g_fun_info = nullptr;

#define lean_trace_fun_info(Code) lean_trace(*g_fun_info, Code)

static bool is_fun_info_trace_enabled() {
    return is_trace_class_enabled(*g_fun_info);
}

void initialize_fun_info() {
    g_fun_info = new name("fun_info");
    register_trace_class(*g_fun_info);
}

void finalize_fun_info() {
    delete g_fun_info;
}

/* Return the list of dependencies for the given type.
   If it depends on local i, then it also sets pinfos[i].set_has_fwd_deps();
 */
static list<unsigned> collect_deps(expr const & type, buffer<expr> const & locals, buffer<param_info> & pinfos) {
    buffer<unsigned> deps;
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e)) {
                unsigned idx;
                for (idx = 0; idx < locals.size(); idx++)
                    if (locals[idx] == e)
                        break;
                if (idx < locals.size() && std::find(deps.begin(), deps.end(), idx) == deps.end()) {
                    deps.push_back(idx);
                    pinfos[idx].set_has_fwd_deps();
                }
            }
            return has_local(e); // continue the search only if e has locals
        });
    std::sort(deps.begin(), deps.end());
    return to_list(deps);
}

/* Store parameter info for fn in \c pinfos and return the dependencies of the resulting type. */
static list<unsigned> get_core(type_context_old & ctx,
                               expr const & fn, buffer<param_info> & pinfos,
                               unsigned max_args) {
    expr type = ctx.relaxed_try_to_pi(ctx.infer(fn));
    type_context_old::tmp_locals locals(ctx);
    unsigned i = 0;
    while (is_pi(type)) {
        if (i == max_args)
            break;
        expr local_type = consume_auto_opt_param(binding_domain(type));
        expr local      = locals.push_local(binding_name(type), local_type, binding_info(type));
        expr new_type   = ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool is_prop    = ctx.is_prop(local_type);
        bool is_dep     = false; /* it is set by collect_deps */
        pinfos.emplace_back(binding_info(type).is_implicit(),
                            binding_info(type).is_inst_implicit(),
                            is_prop, is_dep, collect_deps(local_type, locals.as_buffer(), pinfos));
        type = new_type;
        i++;
    }
    return collect_deps(type, locals.as_buffer(), pinfos);
}

fun_info get_fun_info(type_context_old & ctx, expr const & e) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_fun_info(ctx.mode(), e))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, std::numeric_limits<unsigned>::max());
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.set_fun_info(ctx.mode(), e, r);
    return r;
}

fun_info get_fun_info(type_context_old & ctx, expr const & e, unsigned nargs) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_fun_info_nargs(ctx.mode(), e, nargs))
        return *r;
    buffer<param_info> pinfos;
    auto result_deps = get_core(ctx, e, pinfos, nargs);
    fun_info r(pinfos.size(), to_list(pinfos), result_deps);
    cache.set_fun_info_nargs(ctx.mode(), e, nargs, r);
    return r;
}

/* Store subsingleton parameter info for fn in \c ssinfos */
static void get_ss_core(type_context_old & ctx, expr const & fn, buffer<ss_param_info> & ssinfos,
                        unsigned max_args) {
    expr type = ctx.relaxed_try_to_pi(ctx.infer(fn));
    type_context_old::tmp_locals locals(ctx);
    unsigned i = 0;
    while (is_pi(type)) {
        if (i == max_args)
            break;
        expr local      = locals.push_local_from_binding(type);
        expr local_type = ctx.infer(local);
        expr new_type   = ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool spec       = false;
        bool is_prop    = ctx.is_prop(local_type);
        bool is_sub     = is_prop;
        if (!is_sub) {
            // TODO(Leo): check if the following line is a performance bottleneck.
            is_sub = static_cast<bool>(ctx.mk_subsingleton_instance(local_type));
        }
        ssinfos.emplace_back(spec, is_sub);
        type = new_type;
        i++;
    }
}

ss_param_infos get_subsingleton_info(type_context_old & ctx, expr const & e) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_subsingleton_info(ctx.mode(), e))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, e, ssinfos, std::numeric_limits<unsigned>::max());
    ss_param_infos r = to_list(ssinfos);
    cache.set_subsingleton_info(ctx.mode(), e, r);
    return r;
}

ss_param_infos get_subsingleton_info(type_context_old & ctx, expr const & e, unsigned nargs) {
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_subsingleton_info_nargs(ctx.mode(), e, nargs))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, e, ssinfos, nargs);
    ss_param_infos r = to_list(ssinfos);
    cache.set_subsingleton_info_nargs(ctx.mode(), e, nargs, r);
    return r;
}

/* Return true if there is j s.t. ssinfos[j] is marked as subsingleton,
   and it dependends of argument i */
static bool has_nonsubsingleton_fwd_dep(unsigned i, buffer<param_info> const & pinfos, buffer<ss_param_info> const & ssinfos) {
    lean_assert(pinfos.size() == ssinfos.size());
    for (unsigned j = i+1; j < pinfos.size(); j++) {
        if (ssinfos[j].is_subsingleton())
            continue;
        auto const & back_deps = pinfos[j].get_back_deps();
        if (std::find(back_deps.begin(), back_deps.end(), i) != back_deps.end()) {
            return true;
        }
    }
    return false;
}

static void trace_if_unsupported(type_context_old & ctx, expr const & fn,
                                 buffer<expr> const & args, unsigned prefix_sz, ss_param_infos const & result) {
    lean_assert(args.size() >= length(result));
    if (!is_fun_info_trace_enabled())
        return;
    fun_info info = get_fun_info(ctx, fn, args.size());
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    buffer<ss_param_info> ssinfos;
    to_buffer(get_subsingleton_info(ctx, fn, args.size()), ssinfos);
    lean_assert(pinfos.size() == ssinfos.size());
    /* Check if all remaining arguments are nondependent or
       dependent (but all forward dependencies are subsingletons) */
    unsigned i = prefix_sz;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
            continue; /* nondependent argument */
        if (has_nonsubsingleton_fwd_dep(i, pinfos, ssinfos))
            break; /* failed i-th argument has a forward dependent that is not a prop nor a subsingleton */
    }
    if (i == pinfos.size())
        return; // It is *cheap* case

    /* Expensive case */
    /* We generate a trace message IF it would be possible to compute more precise information.
       That is, there is an argument that is a proposition and/or subsingleton, but
       the corresponding pinfo is not a marked a prop/subsingleton.
    */
    i = 0;
    for (ss_param_info const & ssinfo : result) {
        if (ssinfo.is_subsingleton())
            continue;
        expr arg_type = ctx.infer(args[i]);
        if (ctx.mk_subsingleton_instance(arg_type)) {
            lean_trace_fun_info(
                tout() << "approximating function information for '" << fn
                << "', this may affect the effectiveness of the simplifier and congruence closure modules, "
                << "more precise information can be efficiently computed if all parameters are moved to the "
                << "beginning of the function\n";);
            return;
        }
        i++;
    }
}

unsigned get_specialization_prefix_size(type_context_old & ctx, expr const & fn, unsigned nargs) {
    /*
      We say a function is "cheap" if it is of the form:

      a) 0 or more dependent parameters p s.t. there is at least one forward dependency x : C[p]
         which is not a proposition nor a subsingleton.

      b) followed by 0 or more nondependent parameter and/or a dependent parameter
      s.t. all forward dependencies are propositions and subsingletons.

      We have a caching mechanism for the "cheap" case.
      The cheap case cover many commonly used functions

        eq  : Pi {A : Type} (x y : A), Prop
        add : Pi {A : Type} [s : has_add A] (x y : A), A
        inv : Pi {A : Type} [s : has_inv A] (x : A) (h : invertible x), A

      but it doesn't cover

         p : Pi {A : Type} (x : A) {B : Type} (y : B), Prop

      I don't think this is a big deal since we can write it as:

         p : Pi {A : Type} {B : Type} (x : A) (y : B), Prop

      Therefore, we ignore the non-cheap cases, and pretend they are "cheap".
      If tracing is enabled, we produce a tracing message whenever we find
      a non-cheap case.

      This procecure returns the size of group a)
    */
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_specialization_prefix_size(ctx.mode(), fn, nargs))
        return *r;
    fun_info info = get_fun_info(ctx, fn, nargs);
    buffer<param_info> pinfos;
    to_buffer(info.get_params_info(), pinfos);
    buffer<ss_param_info> ssinfos;
    to_buffer(get_subsingleton_info(ctx, fn, nargs), ssinfos);
    lean_assert(pinfos.size() == ssinfos.size());
    /* Compute "prefix": 0 or more parameters s.t.
       at lest one forward dependency is not a proposition or a subsingleton */
    unsigned i = 0;
    for (; i < pinfos.size(); i++) {
        param_info const & pinfo = pinfos[i];
        if (!pinfo.has_fwd_deps())
            break;
        /* search for forward dependency that is not a proposition nor a subsingleton */
        if (!has_nonsubsingleton_fwd_dep(i, pinfos, ssinfos))
            break;
    }
    unsigned prefix_sz = i;
    cache.set_specialization_prefix_size(ctx.mode(), fn, nargs, prefix_sz);
    return prefix_sz;
}

ss_param_infos get_specialized_subsingleton_info(type_context_old & ctx, expr const & a) {
    lean_assert(is_app(a));
    buffer<expr> args;
    expr const & fn        = get_app_args(a, args);
    unsigned prefix_sz     = get_specialization_prefix_size(ctx, fn, args.size());
    unsigned num_rest_args = args.size() - prefix_sz;
    expr g = a;
    for (unsigned i = 0; i < num_rest_args; i++)
        g = app_fn(g);
    abstract_context_cache & cache = ctx.get_cache();
    if (auto r = cache.get_specialized_subsingleton_info_nargs(ctx.mode(), g, num_rest_args))
        return *r;
    buffer<ss_param_info> ssinfos;
    get_ss_core(ctx, fn, ssinfos, prefix_sz);
    for (unsigned i = 0; i < prefix_sz; i++) {
        ssinfos[i].set_specialized();
    }
    get_ss_core(ctx, g, ssinfos, num_rest_args);
    ss_param_infos r = to_list(ssinfos);
    cache.set_specialization_subsingleton_info_nargs(ctx.mode(), g, num_rest_args, r);
    trace_if_unsupported(ctx, fn, args, prefix_sz, r);
    return r;
}
}




// ========== head_map.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "util/list.h"
#include "kernel/expr.h"
#include "library/io_state_stream.h"

namespace lean {
struct head_index {
    expr_kind m_kind;
    name      m_name;
    explicit head_index(expr_kind k = expr_kind::Var):m_kind(k) {}
    explicit head_index(name const & c):m_kind(expr_kind::Constant), m_name(c) {}
    head_index(expr const & e);
    expr_kind kind() const { return m_kind; }
    name const & get_name() const { return m_name; }

    struct cmp {
        int operator()(head_index const & i1, head_index const & i2) const;
    };

    friend std::ostream & operator<<(std::ostream & out, head_index const & head_idx);
};

io_state_stream const & operator<<(io_state_stream const & out, head_index const & head_idx);

/**
    \brief Very simple indexing data-structure that allow us to map the head symbol of an expression to
    a list of values.

    The index is the expression kind and a name (if it is a constant).

    This index is very naive, but it is effective for many applications. */
template<typename V, typename GetPrio>
class head_map_prio : private GetPrio {
    rb_map<head_index, list<V>, head_index::cmp> m_map;

    unsigned get_priority(V const & v) const { return GetPrio::operator()(v); }

    list<V> insert_prio(V const & v, list<V> const & vs) {
        if (!vs)
            return to_list(v);
        else if (get_priority(v) >= get_priority(head(vs)))
            return cons(v, vs);
        else
            return cons(head(vs), insert_prio(v, tail(vs)));
    }

public:
    head_map_prio() {}
    head_map_prio(GetPrio const & g):GetPrio(g) {}
    void clear() { m_map = rb_map<head_index, list<V>, head_index::cmp>(); }
    bool empty() const { return m_map.empty(); }
    bool contains(head_index const & h) const { return m_map.contains(h); }
    list<V> const * find(head_index const & h) const { return m_map.find(h); }
    void erase(head_index const & h) { m_map.erase(h); }
    template<typename P> void filter(head_index const & h, P && p) {
        if (auto it = m_map.find(h)) {
            auto new_vs = ::lean::filter(*it, std::forward<P>(p));
            if (!new_vs)
                m_map.erase(h);
            else
                m_map.insert(h, new_vs);
        }
    }
    void erase(head_index const & h, V const & v) {
        return filter(h, [&](V const & v2) { return v != v2; });
    }
    void insert(head_index const & h, V const & v) {
        if (auto it = m_map.find(h))
            m_map.insert(h, insert_prio(v, ::lean::filter(*it, [&](V const & v2) { return v != v2; })));
        else
            m_map.insert(h, to_list(v));
    }
    template<typename F> void for_each(F && f) const { m_map.for_each(f); }
    template<typename F> void for_each_entry(F && f) const {
        m_map.for_each([&](head_index const & h, list<V> const & vs) {
                for (V const & v : vs)
                    f(h, v);
            });
    }
};

template<typename V>
struct constant_priority_fn { unsigned operator()(V const &) const { return 0; } };

template<typename V>
class head_map : public head_map_prio<V, constant_priority_fn<V>> {
public:
    head_map() {}
};
}




// ========== head_map.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/head_map.h"
#include "library/explicit.h"

namespace lean {
head_index::head_index(expr const & e) {
    expr f = get_app_fn(e);
    while (true) {
        if (is_as_atomic(f))
            f = get_app_fn(get_as_atomic_arg(f));
        else if (is_explicit(f))
            f = get_explicit_arg(f);
        else
            break;
    }
    m_kind = f.kind();
    if (is_constant(f))
        m_name = const_name(f);
    else if (is_local(f))
        m_name = mlocal_name(f);
}

int head_index::cmp::operator()(head_index const & i1, head_index const & i2) const {
    if (i1.m_kind != i2.m_kind || (i1.m_kind != expr_kind::Constant && i1.m_kind != expr_kind::Local))
        return static_cast<int>(i1.m_kind) - static_cast<int>(i2.m_kind);
    else
        return quick_cmp(i1.m_name, i2.m_name);
}

std::ostream & operator<<(std::ostream & out, head_index const & head_idx) {
    if (head_idx.m_kind == expr_kind::Constant || head_idx.m_kind == expr_kind::Local)
        out << head_idx.m_name;
    else
        out << head_idx.m_kind;
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, head_index const & head_idx) {
    return display(out, head_idx);
}
}




// ========== choice.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
    \brief Create a choice expression for the given expressions.
    The elaborator decides which one should be used based on the type of the arguments.

    \remark if num_fs == 1, then return fs[0]

    \pre num_fs >= 1
*/
expr mk_choice(unsigned num_es, expr const * es);
/** \brief Return true iff \c e is an expression created using \c mk_choice. */
bool is_choice(expr const & e);
/**
   \brief Return the number of alternatives in a choice expression.
   We have that <tt>get_num_choices(mk_choice(n, es)) == n</tt> whenever <tt>n >= 2</tt>.

   \pre is_choice(e)
*/
unsigned get_num_choices(expr const & e);
/**
   \brief Return the (i+1)-th alternative of a choice expression.

   \pre is_choice(e)
   \pre i < get_num_choices(e)
*/
expr const & get_choice(expr const & e, unsigned i);

/**
   \brief Collect "choices" occurring in \c e.
   For example, if \c e contains [choice (f a) (g a)] where f and g are constants,
   the result contains the list [f, g]. This function is only used for producing nicer
   error messages.
*/
list<list<name>> collect_choice_symbols(expr const & e);
/** \brief Format the result produced by collect_choice_symbols. */
format pp_choice_symbols(expr const & e);

void initialize_choice();
void finalize_choice();
}




// ========== choice.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "library/choice.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_choice_name = nullptr;
static std::string * g_choice_opcode = nullptr;

[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'choice' expression"); }

// We encode a 'choice' expression using a macro.
// This is a trick to avoid creating a new kind of expression.
// 'Choice' expressions are temporary objects used by the elaborator,
// and have no semantic significance.
class choice_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const override { return *g_choice_name; }
    // Choice expressions must be replaced with metavariables before invoking the type checker.
    // Choice expressions cannot be exported. They are transient/auxiliary objects.
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_ex(); }
    virtual void write(serializer & s) const override {
        // we should be able to write choice expressions because of notation declarations
        s.write_string(*g_choice_opcode);
    }
};

static macro_definition * g_choice = nullptr;
expr mk_choice(unsigned num_es, expr const * es) {
    lean_assert(num_es > 0);
    if (num_es == 1)
        return es[0];
    else
        return mk_macro(*g_choice, num_es, es);
}

list<list<name>> collect_choice_symbols(expr const & e) {
    buffer<list<name>> r;
    for_each(e, [&](expr const & e, unsigned) {
            if (is_choice(e)) {
                buffer<name> cs;
                for (unsigned i = 0; i < get_num_choices(e); i++) {
                    expr const & c = get_app_fn(get_choice(e, i));
                    if (is_constant(c))
                        cs.push_back(const_name(c));
                    else if (is_local(c))
                        cs.push_back(mlocal_pp_name(c));
                }
                if (cs.size() > 1)
                    r.push_back(to_list(cs));
            }
            return true;
        });
    return to_list(r);
}

format pp_choice_symbols(expr const & e) {
    list<list<name>> symbols = collect_choice_symbols(e);
    if (symbols) {
        format r;
        bool first = true;
        for (auto cs : symbols) {
            format aux("overloads:");
            for (auto s : cs)
                aux += space() + format(s);
            if (!first)
                r += line();
            r += aux;
            first = false;
        }
        return r;
    } else {
        return format();
    }
}

void initialize_choice() {
    g_choice_name   = new name("choice");
    g_choice_opcode = new std::string("Choice");
    g_choice        = new macro_definition(new choice_macro_cell());
    register_macro_deserializer(*g_choice_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_choice(num, args);
                                });
}

void finalize_choice() {
    delete g_choice;
    delete g_choice_opcode;
    delete g_choice_name;
}

bool is_choice(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return macro_num_args(e);
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return macro_arg(e, i);
}
}




// ========== explicit.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Create an explicit expression '@@ f'.
    This only affects the elaborator behavior.
*/
expr mk_explicit(expr const & e);
/** \brief Return true iff \c e is an explicit expression. */
bool is_explicit(expr const & e);
/** \brief See #is_nested_annotation */
bool is_nested_explicit(expr const & e);
/** \brief Return the argument of an explicit expression.
    \pre is_explicit(e)
*/
expr const & get_explicit_arg(expr const & e);

/** \brief Create an partial explicit expression '@ f'.
    This only affects the elaborator behavior.
*/
expr mk_partial_explicit(expr const & e);
/** \brief Return true iff \c e is a partial explicit expression. */
bool is_partial_explicit(expr const & e);
/** \brief See #is_nested_annotation */
bool is_nested_partial_explicit(expr const & e);
/** \brief Return the argument of a partial explicit expression.
    \pre is_partial_explicit(e)
*/
expr const & get_partial_explicit_arg(expr const & e);

bool is_explicit_or_partial_explicit(expr const & e);
expr get_explicit_or_partial_explicit_arg(expr const & e);

/** \brief Create an explicit expression that is accepted as is
    by the elaborator.
*/
expr mk_as_is(expr const & e);
/** \brief Return true iff \c e was created with mk_as_is. */
bool is_as_is(expr const & e);
/** \brief Return the argument of an expression created using mk_as_is.
    \pre is_as_is(e)
*/
expr const & get_as_is_arg(expr const & e);

/** \brief Create an expression that should be treated as an atom by the elaborator.
    This expression also "cancels" the effect of a nested '@'.
*/
expr mk_as_atomic(expr const & e);
/** \brief Return true iff \c e is an atomic expression. */
bool is_as_atomic(expr const & e);
/** \brief Return the argument of an atomic expression.
    \pre is_atomic(e)
*/
expr const & get_as_atomic_arg(expr const & e);

void initialize_explicit();
void finalize_explicit();
}




// ========== explicit.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "library/annotation.h"
#include "library/explicit.h"

namespace lean {
static name * g_explicit_name = nullptr;
static name * g_partial_explicit_name = nullptr;
static name * g_as_atomic_name = nullptr;
static name * g_as_is_name    = nullptr;

expr mk_explicit(expr const & e) { return mk_annotation(*g_explicit_name, e); }
bool is_explicit(expr const & e) { return is_annotation(e, *g_explicit_name); }
bool is_nested_explicit(expr const & e) { return is_nested_annotation(e, *g_explicit_name); }
expr const & get_explicit_arg(expr const & e) { lean_assert(is_explicit(e)); return get_annotation_arg(e); }

expr mk_partial_explicit(expr const & e) { return mk_annotation(*g_partial_explicit_name, e); }
bool is_partial_explicit(expr const & e) { return is_annotation(e, *g_partial_explicit_name); }
bool is_nested_partial_explicit(expr const & e) { return is_nested_annotation(e, *g_partial_explicit_name); }
expr const & get_partial_explicit_arg(expr const & e) { lean_assert(is_partial_explicit(e)); return get_annotation_arg(e); }

bool is_explicit_or_partial_explicit(expr const & e) { return is_explicit(e) || is_partial_explicit(e); }
expr get_explicit_or_partial_explicit_arg(expr const & e) { lean_assert(is_explicit_or_partial_explicit(e)); return get_annotation_arg(e); }

expr mk_as_is(expr const & e) { return mk_annotation(*g_as_is_name, e); }
bool is_as_is(expr const & e) { return is_annotation(e, *g_as_is_name); }
expr const & get_as_is_arg(expr const & e) { lean_assert(is_as_is(e)); return get_annotation_arg(e); }

expr mk_as_atomic(expr const & e) { return mk_annotation(*g_as_atomic_name, e); }
bool is_as_atomic(expr const & e) { return is_annotation(e, *g_as_atomic_name); }
expr const & get_as_atomic_arg(expr const & e) { lean_assert(is_as_atomic(e)); return get_annotation_arg(e); }

void initialize_explicit() {
    g_explicit_name         = new name("@");
    g_partial_explicit_name = new name("@@");
    g_as_atomic_name        = new name("as_atomic");
    g_as_is_name            = new name("as_is");

    register_annotation(*g_explicit_name);
    register_annotation(*g_partial_explicit_name);
    register_annotation(*g_as_atomic_name);
    register_annotation(*g_as_is_name);
}

void finalize_explicit() {
    delete g_as_is_name;
    delete g_as_atomic_name;
    delete g_partial_explicit_name;
    delete g_explicit_name;
}
}




// ========== st_task_queue.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task.h"

namespace lean {

class st_task_queue : public task_queue {
public:
    void wait_for_finish(gtask const &) override;
    void fail_and_dispose(gtask const &) override;

    void submit(gtask const &) override;

    void evacuate() override;

    void join() override;
};

}




// ========== st_task_queue.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/st_task_queue.h"

namespace lean {

void st_task_queue::wait_for_finish(gtask const & t) {
    if (t && get_state(t).load() <= task_state::Running) {
        get_state(t).store(task_state::Running);
        execute(t);
        clear(t);
    }
}

void st_task_queue::fail_and_dispose(gtask const & t) {
    if (t && get_state(t).load() < task_state::Running) {
        fail(t, std::make_exception_ptr(cancellation_exception()));
        clear(t);
    }
}

void st_task_queue::submit(gtask const & t) {
    wait_for_finish(t);
}

void st_task_queue::evacuate() {}

void st_task_queue::join() {}

}




// ========== replace_visitor_with_tc.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/replace_visitor.h"
#include "library/type_context.h"
namespace lean {
/** \brief Version of replace_visitor with a nested type_context_old object. */
class replace_visitor_with_tc : public replace_visitor {
protected:
    type_context_old & m_ctx;
    expr visit_lambda_pi_let(bool is_lam, expr const & e);
    virtual expr visit_lambda(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }
    virtual expr visit_let(expr const & e) override {
        return visit_lambda_pi_let(true, e);
    }
    virtual expr visit_pi(expr const & e) override {
        return visit_lambda_pi_let(false, e);
    }
    virtual expr visit_app(expr const & e) override;
public:
    replace_visitor_with_tc(type_context_old & ctx):m_ctx(ctx) {}
};
}




// ========== replace_visitor_with_tc.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/replace_visitor_with_tc.h"
namespace lean {
expr replace_visitor_with_tc::visit_lambda_pi_let(bool is_lam, expr const & e) {
    type_context_old::tmp_locals locals(m_ctx);
    expr t = e;
    while (true) {
        if ((is_lam && is_lambda(t)) || (!is_lam && is_pi(t))) {
            expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            d = visit(d);
            locals.push_local(binding_name(t), d, binding_info(t));
            t = binding_body(t);
        } else if (is_let(t)) {
            expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
            expr v = instantiate_rev(let_value(t), locals.size(), locals.data());
            d = visit(d);
            v = visit(v);
            locals.push_let(let_name(t), d, v);
            t = let_body(t);
        } else {
            break;
        }
    }
    t = instantiate_rev(t, locals.size(), locals.data());
    t = visit(t);
    return is_lam ? copy_tag(e, locals.mk_lambda(t)) : copy_tag(e, locals.mk_pi(t));
}

expr replace_visitor_with_tc::visit_app(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    expr new_fn   = visit(fn);
    bool modified = !is_eqp(fn, new_fn);
    for (expr & arg : args) {
        expr new_arg = visit(arg);
        if (!is_eqp(new_arg, arg))
            modified = true;
        arg = new_arg;
    }
    if (!modified)
        return e;
    else
        return copy_tag(e, mk_app(new_fn, args));
}
}




// ========== export_decl.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** Structure for storing the contents of an 'export' command. */
struct export_decl {
    name                   m_ns;
    name                   m_as;
    bool                   m_had_explicit;
    list<pair<name, name>> m_renames;
    list<name>             m_except_names;

    export_decl() {}
    export_decl(name const & ns, name const & as, bool had_explicit, buffer<pair<name, name>> const & renames,
                buffer<name> const & except_names):
        m_ns(ns), m_as(as), m_had_explicit(had_explicit),
        m_renames(to_list(renames)), m_except_names(to_list(except_names)) {}
};

/** \brief We store export commands to allow us to replay them whenever the namespace is opened. */
environment add_export_decl(environment const & env, name const & in_ns, export_decl const & e);
environment add_export_decl(environment const & env, export_decl const & entry);

environment activate_export_decls(environment, name);
list<export_decl> get_active_export_decls(environment const & env);

void initialize_export_decl();
void finalize_export_decl();
}




// ========== export_decl.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/serializer.h"
#include "library/export_decl.h"
#include "library/scoped_ext.h"

namespace lean {

static void write_pair_name(serializer & s, pair<name, name> const & p) {
    s << p.first << p.second;
}

static serializer & operator<<(serializer & s, pair<name, name> const & p) {
    write_pair_name(s, p);
    return s;
}

static pair<name, name> read_pair_name(deserializer & d) {
    pair<name, name> r;
    d >> r.first >> r.second;
    return r;
}

bool operator==(export_decl const & d1, export_decl const & d2) {
    return
        d1.m_ns           == d2.m_ns &&
        d1.m_as           == d2.m_as &&
        d1.m_had_explicit == d2.m_had_explicit &&
        d1.m_renames      == d2.m_renames &&
        d1.m_except_names == d2.m_except_names;
}

bool operator!=(export_decl const & d1, export_decl const & d2) {
    return !(d1 == d2);
}

struct export_decl_env_ext : public environment_extension {
    name_map<list<export_decl>> m_ns_map;

    export_decl_env_ext() {}
    export_decl_env_ext(name_map<list<export_decl>> const & ns_map): m_ns_map(ns_map) {}
};

/** \brief Auxiliary object for registering the environment extension */
struct export_decl_env_ext_reg {
    unsigned m_ext_id;
    export_decl_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<export_decl_env_ext>()); }
};

static export_decl_env_ext_reg * g_ext = nullptr;

/** \brief Retrieve environment extension */
static export_decl_env_ext const & get_export_decl_extension(environment const & env) {
    return static_cast<export_decl_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

/** \brief Update environment extension */
static environment update(environment const & env, export_decl_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<export_decl_env_ext>(ext));
}

struct export_decl_modification : public modification {
    LEAN_MODIFICATION("export_decl")

    name m_in_ns;
    export_decl m_export_decl;

    export_decl_modification() {}
    export_decl_modification(name const & in_ns, export_decl const & e) :
        m_in_ns(in_ns), m_export_decl(e) {}

    void perform(environment & env) const override {
        env = add_export_decl(env, m_in_ns, m_export_decl);
    }

    void serialize(serializer & s) const override {
        s << m_in_ns << m_export_decl.m_ns << m_export_decl.m_as << m_export_decl.m_had_explicit;
        write_list<name>(s, m_export_decl.m_except_names);
        write_list<pair<name, name>>(s, m_export_decl.m_renames);
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto m = std::make_shared<export_decl_modification>();
        auto & e = m->m_export_decl;
        d >> m->m_in_ns >> e.m_ns >> e.m_as >> e.m_had_explicit;
        e.m_except_names = read_list<name>(d, read_name);
        e.m_renames = read_list<pair<name, name>>(d, read_pair_name);
        return m;
    }
};

environment add_export_decl(environment const & env, name const & in_ns, export_decl const & e) {
    auto ns_map = get_export_decl_extension(env).m_ns_map;
    list<export_decl> decls;
    if (ns_map.contains(in_ns))
        decls = *ns_map.find(in_ns);

    if (std::find(decls.begin(), decls.end(), e) != decls.end())
        return env;

    auto new_env = update(env, export_decl_env_ext(insert(ns_map, in_ns, cons(e, decls))));
    return module::add(new_env, std::make_shared<export_decl_modification>(in_ns, e));
}
environment add_export_decl(environment const & env, export_decl const & entry) {
    return add_export_decl(env, get_namespace(env), entry);
}

struct active_export_decls_config {
    typedef export_decl       entry;
    typedef list<export_decl> state;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (std::find(s.begin(), s.end(), e) == s.end()) {
            s = cons(e, s);
        }
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }

    // uses local scope only
    static const char * get_serialization_key() { return "active_export_decls"; }
    static void write_entry(serializer &, entry const &) { lean_unreachable(); }
    static entry read_entry(deserializer &) { lean_unreachable(); }
};

template class scoped_ext<active_export_decls_config>;
typedef scoped_ext<active_export_decls_config> active_export_decls_ext;

environment activate_export_decls(environment env, name ns) {
    auto ns_map = get_export_decl_extension(env).m_ns_map;
    while (true) {
        if (ns_map.contains(ns)) {
            for (auto const & e : *ns_map.find(ns))
                env = active_export_decls_ext::add_entry(env, get_dummy_ios(), e, false);
        }
        if (ns.is_anonymous())
            break;
        ns = ns.get_prefix();
    }
    return env;
}

list<export_decl> get_active_export_decls(environment const & env) {
    return active_export_decls_ext::get_state(env);
}

void initialize_export_decl() {
    g_ext = new export_decl_env_ext_reg();
    export_decl_modification::init();
    active_export_decls_ext::initialize();
}

void finalize_export_decl() {
    active_export_decls_ext::finalize();
    export_decl_modification::finalize();
    delete g_ext;
}
}




// ========== fingerprint.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/int64.h"
#include "kernel/environment.h"

namespace lean {
environment update_fingerprint(environment const & env, unsigned h);
uint64 get_fingerprint(environment const & env);
void initialize_fingerprint();
void finalize_fingerprint();
}




// ========== fingerprint.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/hash.h"
#include "util/int64.h"
#include "kernel/environment.h"

namespace lean {
struct fingerprint_ext : public environment_extension {
    uint64 m_fingerprint;
    fingerprint_ext():m_fingerprint(0) {}
};

struct fingerprint_ext_reg {
    unsigned m_ext_id;
    fingerprint_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<fingerprint_ext>()); }
};

static fingerprint_ext_reg * g_ext = nullptr;
static fingerprint_ext const & get_extension(environment const & env) {
    return static_cast<fingerprint_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, fingerprint_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<fingerprint_ext>(ext));
}

environment update_fingerprint(environment const & env, unsigned h) {
    fingerprint_ext ext = get_extension(env);
    ext.m_fingerprint = hash(ext.m_fingerprint, static_cast<uint64>(h));
    return update(env, ext);
}

uint64 get_fingerprint(environment const & env) {
    return get_extension(env).m_fingerprint;
}

void initialize_fingerprint() {
    g_ext     = new fingerprint_ext_reg();
}

void finalize_fingerprint() {
    delete g_ext;
}
}




// ========== time_task.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <string>
#include "library/message_builder.h"
#include "library/profiling.h"
#include "util/timeit.h"

namespace lean {
void report_profiling_time(std::string const & category, second_duration time);
void display_cumulative_profiling_times(std::ostream & out);

/** Measure time of some task and report it for the final cumulative profile. */
class time_task {
    std::string     m_category;
    optional<xtimeit> m_timeit;
public:
    time_task(std::string const & category, message_builder builder, options const & opts, name decl = name()):
            m_category(category) {
        if (get_profiler(opts)) {
            m_timeit = optional<xtimeit>(get_profiling_threshold(opts), [=](second_duration duration) mutable {
                builder.get_text_stream().get_stream() << m_category;
                if (decl)
                    builder.get_text_stream().get_stream() << " of " << decl;
                builder.get_text_stream().get_stream() << " took " << display_profiling_time{duration} << "\n";
                builder.report();
            });
        }
    }

    ~time_task() {
        if (m_timeit)
            report_profiling_time(m_category, m_timeit->get_elapsed());
    }
};

void initialize_time_task();
void finalize_time_task();
}




// ========== time_task.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <map>
#include "library/time_task.h"

namespace lean {

static std::map<std::string, second_duration> * g_cum_times;
static mutex * g_cum_times_mutex;

void report_profiling_time(std::string const & category, second_duration time) {
    lock_guard<mutex> _(*g_cum_times_mutex);
    (*g_cum_times)[category] += time;
}

void display_cumulative_profiling_times(std::ostream & out) {
    if (g_cum_times->empty())
        return;
    out << "cumulative profiling times:\n";
    for (auto const & p : *g_cum_times)
        out << "\t" << p.first << " " << display_profiling_time{p.second} << "\n";
}

void initialize_time_task() {
    g_cum_times_mutex = new mutex;
    g_cum_times = new std::map<std::string, second_duration>;
}

void finalize_time_task() {
    delete g_cum_times;
    delete g_cum_times_mutex;
}
}




// ========== eval_helper.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/vm/vm_io.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/constants.h"
#include <string>
#include <vector>

namespace lean {

class eval_helper {
    environment        m_env;
    options            m_opts;
    type_context_old       m_tc;
    buffer<vm_obj>     m_args;
    vm_state           m_vms;
    vm_state::profiler m_prof;
    name               m_fn;
    expr               m_ty;
    unsigned           m_arity;

public:
    eval_helper(environment const & env, options const & opts, name const & fn);

    vm_obj invoke_fn();

    expr const & get_type() const { return m_ty; }
    vm_state::profiler & get_profiler() { return m_prof; }

    optional<vm_obj> try_exec_io();
    optional<vm_obj> try_exec_tac();
    optional<vm_obj> try_exec();
};

}




// ========== eval_helper.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/eval_helper.h"
#include "library/tactic/tactic_state.h"

namespace lean {

eval_helper::eval_helper(environment const & env, options const & opts, name const & fn) :
        m_env(env), m_opts(opts), m_tc(env, opts, transparency_mode::None),
        m_vms(env, opts), m_prof(m_vms, opts), m_fn(fn) {
    auto d = env.get(m_fn);
    m_ty = m_tc.whnf(d.get_type());

    if (auto vm_decl = m_vms.get_decl(m_fn)) {
        m_arity = vm_decl->get_arity();
    } else {
        throw exception(sstream() << "no vm declaration found for " << m_fn);
    }
}

vm_obj eval_helper::invoke_fn() {
    /* We use `scope_vm_state` to set thread local g_vm_state which is used
       to collect performance numbers when profiling. */
    scope_vm_state scope(m_vms);
    unsigned arity = m_vms.get_decl(m_fn)->get_arity();
    if (arity > m_args.size()) {
        throw exception(sstream() << "cannot evaluate function: " << m_args.size()
                                  << " arguments given but expected " << arity);
    }
    std::reverse(m_args.begin(), m_args.end());
    return m_vms.invoke(m_fn, m_args.size(), m_args.data());
}

optional<vm_obj> eval_helper::try_exec_io() {
    if (is_app_of(m_ty, get_io_name(), 1)) {
        m_args.push_back(mk_vm_simple(0)); // "world state"
        auto r = invoke_fn();
        if (auto error = is_io_error(r)) {
            throw exception(io_error_to_string(*error));
        } else if (auto result = is_io_result(r)) {
            return result;
        } else {
            throw exception("unexpected vm result of io expression");
        }
    }
    return optional<vm_obj>();
}

optional<vm_obj> eval_helper::try_exec_tac() {
    if (is_constant(get_app_fn(m_ty), get_tactic_name())) {
        auto tac_st = mk_tactic_state_for(m_env, m_opts, m_fn, m_tc.mctx(), m_tc.lctx(), mk_true());
        m_args.push_back(tactic::to_obj(tac_st));
        auto r = invoke_fn();
        if (tactic::is_result_success(r)) {
            return optional<vm_obj>(tactic::get_success_value(r));
        } else if (auto ex = tactic::is_exception(m_vms, r)) {
            throw formatted_exception(std::get<1>(*ex), std::get<0>(*ex));
        } else {
            throw exception("tactic failed");
        }
    }
    return optional<vm_obj>();
}

optional<vm_obj> eval_helper::try_exec() {
    if (auto res = try_exec_io()) return res;
    if (auto res = try_exec_tac()) return res;
    return optional<vm_obj>();
}

}




// ========== trace.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <string>
#include "library/io_state_stream.h"

namespace lean {
void register_trace_class(name const & n);
void register_trace_class_alias(name const & n, name const & alias);
bool is_trace_enabled();
bool is_trace_class_enabled(name const & n);

#define lean_is_trace_enabled(CName) (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(CName))

class scope_trace_env {
    unsigned                m_enable_sz;
    unsigned                m_disable_sz;
    environment const *     m_old_env;
    options     const *     m_old_opts;
    abstract_type_context * m_old_ctx;
    void init(environment * env, options * opts, abstract_type_context * ctx);
public:
    scope_trace_env(environment const & env, options const & opts, abstract_type_context & ctx);
    scope_trace_env(environment const & env, abstract_type_context & ctx);
    scope_trace_env(options const & opts);
    ~scope_trace_env();
};

class scope_traces_as_messages {
    std::string                            m_stream_name;
    pos_info                               m_pos;
    std::unique_ptr<io_state>              m_redirected_ios;
    std::unique_ptr<scope_global_ios>      m_scoped_ios;
    std::shared_ptr<string_output_channel> m_buffer;

public:
    scope_traces_as_messages(std::string const & stream_name, pos_info const & pos);
    scope_traces_as_messages(pos_info_provider const * provider, expr const & ref);
    ~scope_traces_as_messages();
    bool enabled() const { return static_cast<bool>(m_scoped_ios); }
};

class scope_traces_as_string {
    std::unique_ptr<io_state>              m_redirected_ios;
    std::unique_ptr<scope_global_ios>      m_scoped_ios;
    std::shared_ptr<string_output_channel> m_buffer;
public:
    scope_traces_as_string();
    ~scope_traces_as_string();
    std::string get_string() const { return m_buffer->str(); }
};

class scope_trace_inc_depth {
    bool m_active{false};
public:
    ~scope_trace_inc_depth();
    void activate();
};

#define LEAN_MERGE_(a, b)  a##b
#define LEAN_LABEL_(a) LEAN_MERGE_(unique_name_, a)
#define LEAN_UNIQUE_NAME LEAN_LABEL_(__LINE__)

#define lean_trace_inc_depth(CName)                                     \
scope_trace_inc_depth LEAN_UNIQUE_NAME;                                 \
if (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(name(CName))) \
    LEAN_UNIQUE_NAME.activate();

/* Temporarily set an option if it is not already set in the trace environment. */
class scope_trace_init_bool_option {
    bool                      m_initialized{false};
    options                   m_opts;
    options *                 m_old_opts;
public:
    ~scope_trace_init_bool_option();
    void init(name const & opt, bool val);
};

#define lean_trace_init_bool(CName, Opt, Val)           \
    scope_trace_init_bool_option LEAN_UNIQUE_NAME;      \
if (lean_is_trace_enabled(CName)) {                     \
    LEAN_UNIQUE_NAME.init(Opt, Val);                    \
}

/* Helper object for temporarily silencing trace messages */
class scope_trace_silent {
    bool m_old_value;
public:
    scope_trace_silent(bool flag);
    ~scope_trace_silent();
};

struct tdepth {};
struct tclass { name m_cls; tclass(name const & c):m_cls(c) {} };

io_state_stream tout();
io_state_stream const & operator<<(io_state_stream const & ios, tdepth const &);
io_state_stream const & operator<<(io_state_stream const & ios, tclass const &);

#define lean_trace_plain(CName, CODE) {         \
if (lean_is_trace_enabled(CName)) {             \
    CODE                                        \
}}

#define lean_trace(CName, CODE) {               \
if (lean_is_trace_enabled(CName)) {             \
    tout() << tclass(CName); CODE               \
}}

#define lean_trace_d(CName, CODE) {               \
if (lean_is_trace_enabled(CName)) {               \
    tout() << tdepth() << tclass(CName); CODE     \
}}

void initialize_trace();
void finalize_trace();
}




// ========== trace.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/io_state.h"
#include "library/trace.h"
#include "library/messages.h"

namespace lean {
static name_set *            g_trace_classes = nullptr;
static name_map<name_set>  * g_trace_aliases = nullptr;
static name *                g_trace_as_messages = nullptr;
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_enabled_trace_classes);
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_disabled_trace_classes);
MK_THREAD_LOCAL_GET_DEF(environment, get_dummy_env);
MK_THREAD_LOCAL_GET_DEF(options,     get_dummy_options);
LEAN_THREAD_VALUE(bool,                g_silent, false);
LEAN_THREAD_PTR(environment,           g_env);
LEAN_THREAD_PTR(options,               g_opts);
LEAN_THREAD_PTR(abstract_type_context, g_ctx);
LEAN_THREAD_VALUE(unsigned,  g_depth, 0);

void register_trace_class(name const & n) {
    register_option(name("trace") + n, BoolOption, "false",
                    "(trace) enable/disable tracing for the given module and submodules");
    g_trace_classes->insert(n);
}

void register_trace_class_alias(name const & n, name const & alias) {
    name_set new_s;
    if (auto s = g_trace_aliases->find(n))
        new_s = *s;
    new_s.insert(alias);
    g_trace_aliases->insert(n, new_s);
}

bool is_trace_enabled() {
    return !get_enabled_trace_classes().empty();
}

static void update_class(std::vector<name> & cs, name const & c) {
    if (std::find(cs.begin(), cs.end(), c) == cs.end()) {
        cs.push_back(c);
    }
}

static void enable_trace_class(name const & c) {
    update_class(get_enabled_trace_classes(), c);
}

static void disable_trace_class(name const & c) {
    update_class(get_disabled_trace_classes(), c);
}

static bool is_trace_class_set_core(std::vector<name> const & cs, name const & n) {
    for (name const & p : cs) {
        if (is_prefix_of(p, n)) {
            return true;
        }
    }
    return false;
}

static bool is_trace_class_set(std::vector<name> const & cs, name const & n) {
    if (is_trace_class_set_core(cs, n))
        return true;
    auto it = n;
    while (true) {
        if (auto s = g_trace_aliases->find(it)) {
            bool found = false;
            s->for_each([&](name const & alias) {
                    if (!found && is_trace_class_set_core(cs, alias))
                        found = true;
                });
            if (found)
                return true;
        }
        if (it.is_atomic())
            return false;
        it = it.get_prefix();
    }
}

bool is_trace_class_enabled(name const & n) {
    if (!is_trace_enabled())
        return false;
    if (is_trace_class_set(get_disabled_trace_classes(), n))
        return false; // it was explicitly disabled
    return is_trace_class_set(get_enabled_trace_classes(), n);
}


void scope_trace_env::init(environment * env, options * opts, abstract_type_context * ctx) {
    m_enable_sz  = get_enabled_trace_classes().size();
    m_disable_sz = get_disabled_trace_classes().size();
    m_old_env    = g_env;
    m_old_opts   = g_opts;
    m_old_ctx    = g_ctx;
    g_env        = env;
    g_ctx        = ctx;
    name trace("trace");
    if (opts && g_opts != opts) {
        opts->for_each([&](name const & n) {
                if (is_prefix_of(trace, n)) {
                    name cls        = n.replace_prefix(trace, name());
                    if (opts->get_bool(n, false))
                        enable_trace_class(cls);
                    else
                        disable_trace_class(cls);
                }
            });
    }
    g_opts = opts;
}

scope_trace_env::scope_trace_env(environment const & env, options const & o, abstract_type_context & ctx) {
    init(const_cast<environment*>(&env), const_cast<options*>(&o), &ctx);
}

scope_trace_env::scope_trace_env(environment const & env, abstract_type_context & ctx) {
    init(const_cast<environment*>(&env), g_opts, &ctx);
}

scope_trace_env::scope_trace_env(options const & o) {
    init(g_env, const_cast<options*>(&o), g_ctx);
}

scope_trace_env::~scope_trace_env() {
    g_env  = const_cast<environment*>(m_old_env);
    g_opts = const_cast<options*>(m_old_opts);
    g_ctx  = m_old_ctx;
    get_enabled_trace_classes().resize(m_enable_sz);
    get_disabled_trace_classes().resize(m_disable_sz);
}

void scope_trace_inc_depth::activate() {
    lean_assert(!m_active);
    m_active = true;
    g_depth++;
}

scope_trace_inc_depth::~scope_trace_inc_depth() {
    if (m_active)
        g_depth--;
}

void scope_trace_init_bool_option::init(name const & n, bool v) {
    m_initialized = true;
    m_old_opts = g_opts;
    if (g_opts)
        m_opts = *g_opts;
    m_opts = m_opts.update_if_undef(n, v);
    g_opts = &m_opts;
}

scope_trace_init_bool_option::~scope_trace_init_bool_option() {
    if (m_initialized) {
        g_opts = m_old_opts;
    }
}

struct silent_ios_helper {
    std::shared_ptr<output_channel> m_out;
    io_state                        m_ios;
    silent_ios_helper():
        m_out(new null_output_channel()),
        m_ios(get_dummy_ios(), m_out, m_out) {}
};

MK_THREAD_LOCAL_GET_DEF(silent_ios_helper, get_silent_ios_helper);
MK_THREAD_LOCAL_GET(type_checker, get_dummy_tc, get_dummy_env());

scope_trace_silent::scope_trace_silent(bool flag) {
    m_old_value = g_silent;
    g_silent    = flag;
}

scope_trace_silent::~scope_trace_silent() {
    g_silent    = m_old_value;
}

io_state_stream tout() {
    if (g_env && !g_silent) {
        options opts = g_opts ? *g_opts : get_dummy_options();
        io_state ios(get_global_ios(), opts);
        return diagnostic(*g_env, ios, *g_ctx);
    } else {
        return diagnostic(get_dummy_env(), get_silent_ios_helper().m_ios, get_dummy_tc());
    }
}

io_state_stream const & operator<<(io_state_stream const & ios, tdepth const &) {
    ios << g_depth << ". ";
    return ios;
}

io_state_stream const & operator<<(io_state_stream const & ios, tclass const & c) {
    ios << "[" << c.m_cls << "] ";
    return ios;
}

void initialize_trace() {
    g_trace_classes = new name_set();
    g_trace_aliases = new name_map<name_set>();
    g_trace_as_messages = new name {"trace", "as_messages"};

    register_trace_class(name{"debug"});
}

void finalize_trace() {
    delete g_trace_classes;
    delete g_trace_aliases;
    delete g_trace_as_messages;
}

scope_traces_as_messages::scope_traces_as_messages(std::string const & stream_name, pos_info const & pos) :
    m_stream_name(stream_name), m_pos(pos) {
    if (get_global_ios().get_options().get_bool(*g_trace_as_messages, false)) {
        m_redirected_ios = std::unique_ptr<io_state>(new io_state(get_global_ios()));
        m_buffer = std::make_shared<string_output_channel>();
        m_redirected_ios->set_regular_channel(m_buffer);
        m_redirected_ios->set_diagnostic_channel(m_buffer);
        m_scoped_ios = std::unique_ptr<scope_global_ios>(new scope_global_ios(*m_redirected_ios));
    }
}

scope_traces_as_messages::scope_traces_as_messages(pos_info_provider const *provider, expr const &ref) :
    scope_traces_as_messages(provider ? provider->get_file_name() : "<unknown>",
                             provider ? provider->get_pos_info_or_some(ref) : pos_info(1, 0)) {}

scope_traces_as_messages::~scope_traces_as_messages() {
    if (enabled()) {
        auto msg = m_buffer->str();
        if (!msg.empty()) {
            auto redirected_output = m_buffer->str();
            if (!redirected_output.empty())
                report_message(message(
                        m_stream_name, m_pos, INFORMATION, "trace output", redirected_output));
        }
    }
}

scope_traces_as_string::scope_traces_as_string() {
    m_redirected_ios = std::unique_ptr<io_state>(new io_state(get_global_ios()));
    m_buffer = std::make_shared<string_output_channel>();
    m_redirected_ios->set_regular_channel(m_buffer);
    m_redirected_ios->set_diagnostic_channel(m_buffer);
    m_scoped_ios = std::unique_ptr<scope_global_ios>(new scope_global_ios(*m_redirected_ios));
}

scope_traces_as_string::~scope_traces_as_string() {
}

}




// ========== annotation.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/expr.h"

namespace lean {
/** \brief Declare a new kind of annotation. It must only be invoked at startup time
    Use helper obect #register_annotation_fn.
*/
void register_annotation(name const & n);

/** \brief Create an annotated expression with tag \c kind based on \c e.

    \pre \c kind must have been registered using #register_annotation.

    \remark Annotations have no real semantic meaning, but are useful for guiding pretty printer and/or automation.
*/
expr mk_annotation(name const & kind, expr const & e, tag g);
expr mk_annotation(name const & kind, expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation. */
bool is_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_annotation, and has tag \c kind. */
bool is_annotation(expr const & e, name const & kind);
/** \brief Return true iff \c e is of the form (a_1 ... (a_k e') ...)
    where all a_i's are annotations and one of the is \c kind.

    \remark is_nested_annotation(e, kind) implies is_annotation(e, kind)
*/
bool is_nested_annotation(expr const & e, name const & kind);

/** \brief Return the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == e
*/
expr const & get_annotation_arg(expr const & e);
/** \brief Return the king of the annotated expression, \c e must have been created using #mk_annotation.

    \post get_annotation_arg(mk_annotation(k, e)) == k
*/
name const & get_annotation_kind(expr const & e);

/** \brief Return the nested annotated expression, \c e must have been created using #mk_annotation.
    This function is the "transitive" version of #get_annotation_arg.
    It guarantees that the result does not satisfy the predicate is_annotation.
*/
expr const & get_nested_annotation_arg(expr const & e);

/** \brief Copy annotation from \c from to \c to. */
expr copy_annotations(expr const & from, expr const & to);

/** \brief Tag \c e as a 'have'-expression. 'have' is a pre-registered annotation. */
expr mk_have_annotation(expr const & e);
/** \brief Tag \c e as a 'show'-expression. 'show' is a pre-registered annotation. */
expr mk_show_annotation(expr const & e);
/** \brief Tag \c e as a 'suffices'-expression. 'suffices' is a pre-registered annotation. */
expr mk_suffices_annotation(expr const & e);

expr mk_checkpoint_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_have_annotation. */
bool is_have_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_show_annotation. */
bool is_show_annotation(expr const & e);
/** \brief Return true iff \c e was created using #mk_suffices_annotation. */
bool is_suffices_annotation(expr const & e);
bool is_checkpoint_annotation(expr const & e);

/** \brief Return the serialization 'opcode' for annotation macros. */
std::string const & get_annotation_opcode();

void initialize_annotation();
void finalize_annotation();
}




// ========== annotation.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "kernel/abstract_type_context.h"
#include "library/kernel_serializer.h"
#include "library/annotation.h"

namespace lean {
static name * g_annotation = nullptr;
static std::string * g_annotation_opcode = nullptr;

name const & get_annotation_name() { return *g_annotation; }
std::string const & get_annotation_opcode() { return *g_annotation_opcode; }

/** \brief We use a macro to mark expressions that denote "let" and "have"-expressions.
    These marks have no real semantic meaning, but are useful for helping Lean's pretty printer.
*/
class annotation_macro_definition_cell : public macro_definition_cell {
    name m_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_name << "' annotation, incorrect number of arguments");
    }
public:
    annotation_macro_definition_cell(name const & n):m_name(n) {}
    name const & get_annotation_kind() const { return m_name; }
    virtual name get_name() const override { return get_annotation_name(); }
    virtual void display(std::ostream & out) const override { out << m_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const override {
        check_macro(m);
        return ctx.check(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, abstract_type_context &) const override {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const override {
        s.write_string(get_annotation_opcode());
        s << m_name;
    }
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<annotation_macro_definition_cell const *>(&other)) {
            return m_name == other_ptr->m_name;
        } else {
            return false;
        }
    }
    virtual unsigned hash() const override {
        return ::lean::hash(m_name.hash(), g_annotation->hash());
    }
};

typedef std::unordered_map<name, macro_definition, name_hash, name_eq> annotation_macros;
static annotation_macros * g_annotation_macros = nullptr;

annotation_macros & get_annotation_macros() { return *g_annotation_macros; }

void register_annotation(name const & n) {
    annotation_macros & ms = get_annotation_macros();
    lean_assert(ms.find(n) == ms.end());
    ms.insert(mk_pair(n, macro_definition(new annotation_macro_definition_cell(n))));
}

expr mk_annotation(name const & kind, expr const & e, tag g) {
    annotation_macros & ms = get_annotation_macros();
    auto it = ms.find(kind);
    if (it != ms.end()) {
        return mk_macro(it->second, 1, &e, g);
    } else {
        throw exception(sstream() << "unknown annotation kind '" << kind << "'");
    }
}

expr mk_annotation(name const & kind, expr const & e) {
    return mk_annotation(kind, e, e.get_tag());
}

bool is_annotation(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_annotation_name();
}

name const & get_annotation_kind(expr const & e) {
    lean_assert(is_annotation(e));
    return static_cast<annotation_macro_definition_cell const*>(macro_def(e).raw())->get_annotation_kind();
}

bool is_annotation(expr const & e, name const & kind) {
    return is_annotation(e) && get_annotation_kind(e) == kind;
}

expr const & get_annotation_arg(expr const & e) {
    lean_assert(is_annotation(e));
    return macro_arg(e, 0);
}

bool is_nested_annotation(expr const & e, name const & kind) {
    expr const * it = &e;
    while (is_annotation(*it)) {
        if (get_annotation_kind(*it) == kind)
            return true;
        it = &get_annotation_arg(*it);
    }
    return false;
}

expr const & get_nested_annotation_arg(expr const & e) {
    expr const * it = &e;
    while (is_annotation(*it))
        it = &get_annotation_arg(*it);
    return *it;
}

expr copy_annotations(expr const & from, expr const & to) {
    buffer<expr> trace;
    expr const * it = &from;
    while (is_annotation(*it)) {
        trace.push_back(*it);
        it = &get_annotation_arg(*it);
    }
    expr r     = to;
    unsigned i = trace.size();
    while (i > 0) {
        --i;
        r = copy_tag(trace[i], mk_annotation(get_annotation_kind(trace[i]), r));
    }
    return r;
}

static name * g_have       = nullptr;
static name * g_show       = nullptr;
static name * g_suffices   = nullptr;
static name * g_checkpoint = nullptr;

expr mk_have_annotation(expr const & e) { return mk_annotation(*g_have, e); }
expr mk_show_annotation(expr const & e) { return mk_annotation(*g_show, e); }
expr mk_suffices_annotation(expr const & e) { return mk_annotation(*g_suffices, e); }
expr mk_checkpoint_annotation(expr const & e) { return mk_annotation(*g_checkpoint, e); }
bool is_have_annotation(expr const & e) { return is_annotation(e, *g_have); }
bool is_show_annotation(expr const & e) { return is_annotation(e, *g_show); }
bool is_suffices_annotation(expr const & e) { return is_annotation(e, *g_suffices); }
bool is_checkpoint_annotation(expr const & e) { return is_annotation(e, *g_checkpoint); }

void initialize_annotation() {
    g_annotation = new name("annotation");
    g_annotation_opcode = new std::string("Annot");
    g_annotation_macros = new annotation_macros();
    g_have       = new name("have");
    g_show       = new name("show");
    g_suffices   = new name("suffices");
    g_checkpoint = new name("checkpoint");

    register_annotation(*g_have);
    register_annotation(*g_show);
    register_annotation(*g_suffices);
    register_annotation(*g_checkpoint);

    register_macro_deserializer(get_annotation_opcode(),
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name k;
                                    d >> k;
                                    return mk_annotation(k, args[0]);
                                });
}

void finalize_annotation() {
    delete g_checkpoint;
    delete g_show;
    delete g_have;
    delete g_suffices;
    delete g_annotation_macros;
    delete g_annotation_opcode;
    delete g_annotation;
}
}




// ========== print.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/formatter.h"

namespace lean {
/** \brief Return true iff \c t contains a constant named \c n or a local constant with named (pp or not) \c n */
bool is_used_name(expr const & t, name const & n);
name pick_unused_name(expr const & t, name const & s);
/**
    \brief Return the body of the binding \c b, where variable #0 is replaced by a local constant with a "fresh" name.
    The name is considered fresh if it is not used by a constant or local constant occuring in the body of \c b.
    The fresh constant is also returned (second return value).

    \remark If preserve_type is false, then the local constant will not use binding_domain.
*/
pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type = false);
pair<expr, expr> let_body_fresh(expr const & b, bool preserve_type = false);

/** \brief Create a simple formatter object based on operator for "print" procedure.

    \remark The print procedure is only used for debugging purposes.
*/
formatter_factory mk_print_formatter_factory();

/** \brief Use simple formatter as the default print function */
void init_default_print_fn();

void initialize_print();
void finalize_print();
}




// ========== print.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/formatter.h"
#include "kernel/environment.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/print.h"

namespace lean {
bool is_used_name(expr const & t, name const & n) {
    bool found = false;
    for_each(t, [&](expr const & e, unsigned) {
            if (found) return false; // already found
            if ((is_constant(e) && const_name(e).get_root() == n)  // t has a constant starting with n
                || (is_local(e) && (mlocal_name(e) == n || mlocal_pp_name(e) == n))) { // t has a local constant named n
                found = true;
                return false; // found it
            }
            if (is_local(e) || is_metavar(e))
                return false; // do not search their types
            return true; // continue search
        });
    return found;
}

name pick_unused_name(expr const & t, name const & s) {
    name r = s;
    unsigned i = 1;
    while (is_used_name(t, r)) {
        r = name(s).append_after(i);
        i++;
    }
    return r;
}

bool is_numerical_name(name n) {
    while (!n.is_atomic())
        n = n.get_prefix();
    return n.is_numeral();
}

static name * g_M   = nullptr;
static name * g_x   = nullptr;

void initialize_print() {
    g_M = new name("M");
    g_x = new name("x");
}

void finalize_print() {
    delete g_M;
    delete g_x;
}

static name cleanup_name(name const & n) {
    if (is_numerical_name(n))
        return *g_x;
    else
        return n;
}

pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type) {
    lean_assert(is_binding(b));
    name n = cleanup_name(binding_name(b));
    n = pick_unused_name(binding_body(b), n);
    expr c = mk_local(n, preserve_type ? binding_domain(b) : expr(), binding_info(b));
    return mk_pair(instantiate(binding_body(b), c), c);
}

pair<expr, expr> let_body_fresh(expr const & b, bool preserve_type) {
    lean_assert(is_let(b));
    name n = cleanup_name(let_name(b));
    n = pick_unused_name(let_body(b), n);
    expr c = mk_local(n, preserve_type ? let_type(b) : expr());
    return mk_pair(instantiate(let_body(b), c), c);
}

name fix_name(name const & a) {
    if (a.is_atomic()) {
        if (a.is_numeral())
            return *g_M;
        else
            return a;
    } else {
        name p = fix_name(a.get_prefix());
        if (p == a.get_prefix())
            return a;
        else if (a.is_numeral())
            return name(p, a.get_numeral());
        else
            return name(p, a.get_string());
    }
}

/**
   \brief Very basic printer for expressions.
   It is mainly used when debugging code.
*/
struct print_expr_fn {
    std::ostream & m_out;

    std::ostream & out() { return m_out; }

    bool is_atomic(expr const & a) {
        return ::lean::is_atomic(a) || is_mlocal(a);
    }

    void print_child(expr const & a) {
        if (is_atomic(a)) {
            print(a);
        } else {
            out() << "("; print(a); out() << ")";
        }
    }

    void print_macro(expr const & a) {
        macro_def(a).display(out());
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            out() << " "; print_child(macro_arg(a, i));
        }
    }

    void print_sort(expr const & a) {
        if (is_zero(sort_level(a))) {
            out() << "Prop";
        } else if (is_one(sort_level(a))) {
            out() << "Type";
        } else if (is_succ(sort_level(a))) {
            out() << "Type.{" << succ_of(sort_level(a)) << "}";
        } else {
            out() << "Sort.{" << sort_level(a) << "}";
        }
    }

    void print_app(expr const & e) {
        expr const & f = app_fn(e);
        if (is_app(f))
            print(f);
        else
            print_child(f);
        out() << " ";
        print_child(app_arg(e));
    }

    void print_arrow_body(expr const & a) {
        if (is_atomic(a) || is_arrow(a))
            return print(a);
        else
            return print_child(a);
    }

    void print_binding(char const * bname, expr e) {
        expr_kind k = e.kind();
        out() << bname;
        while (e.kind() == k) {
            out() << " ";
            auto p = binding_body_fresh(e);
            expr const & n = p.second;
            if (binding_info(e).is_implicit())
                out() << "{";
            else if (binding_info(e).is_inst_implicit())
                out() << "[";
            else if (binding_info(e).is_strict_implicit())
                out() << "{{";
            else
                out() << "(";
            out() << n << " : ";
            print(binding_domain(e));
            if (binding_info(e).is_implicit())
                out() << "}";
            else if (binding_info(e).is_inst_implicit())
                out() << "]";
            else if (binding_info(e).is_strict_implicit())
                out() << "}}";
            else
                out() << ")";
            e = p.first;
        }
        out() << ", ";
        print_child(e);
    }

    void print_let(expr const & e) {
        out() << "let " << let_name(e) << " : ";
        print(let_type(e));
        out() << " := ";
        print(let_value(e));
        out() << " in ";
        print(let_body(e));
    }

    void print_const(expr const & a) {
        list<level> const & ls = const_levels(a);
        out() << const_name(a);
        if (!is_nil(ls)) {
            out() << ".{";
            bool first = true;
            for (auto l : ls) {
                if (first) first = false; else out() << " ";
                if (is_max(l) || is_imax(l))
                    out() << "(" << l << ")";
                else
                    out() << l;
            }
            out() << "}";
        }
    }

    void print(expr const & a) {
        switch (a.kind()) {
        case expr_kind::Meta:
            out() << "?" << fix_name(mlocal_name(a));
            break;
        case expr_kind::Local:
            out() << fix_name(mlocal_pp_name(a));
            break;
        case expr_kind::Var:
            out() << "#" << var_idx(a);
            break;
        case expr_kind::Constant:
            print_const(a);
            break;
        case expr_kind::App:
            print_app(a);
            break;
        case expr_kind::Let:
            print_let(a);
            break;
        case expr_kind::Lambda:
            print_binding("fun", a);
            break;
        case expr_kind::Pi:
            if (!is_arrow(a)) {
                print_binding("Pi", a);
            } else {
                print_child(binding_domain(a));
                out() << " -> ";
                print_arrow_body(lower_free_vars(binding_body(a), 1));
            }
            break;
        case expr_kind::Sort:
            print_sort(a);
            break;
        case expr_kind::Macro:
            print_macro(a);
            break;
        }
    }

    print_expr_fn(std::ostream & out):m_out(out) {}

    void operator()(expr const & e) {
        scoped_expr_caching set(false);
        print(e);
    }
};

formatter_factory mk_print_formatter_factory() {
    return [](environment const &, options const & o, abstract_type_context &) { // NOLINT
        return formatter(o, [=](expr const & e, options const &) {
                std::ostringstream s;
                print_expr_fn pr(s);
                pr(e);
                return format(s.str());
            });
    };
}

void init_default_print_fn() {
    set_print_fn([](std::ostream & out, expr const & e) {
            print_expr_fn pr(out);
            pr(e);
        });
}
}




// ========== normalize.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "kernel/abstract_type_context.h"

namespace lean {
/** \brief Return the \c e normal form with respect to the environment \c env. */
expr normalize(environment const & env, expr const & e, bool eta = false);
expr normalize(abstract_type_context & ctx, expr const & e, bool eta = false);
}




// ========== normalize.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/inductive/inductive.h"
#include "library/replace_visitor.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/attribute_manager.h"

namespace lean {
class normalize_fn {
    abstract_type_context &           m_ctx;
    std::function<bool(expr const &)> m_pred;  // NOLINT
    bool                              m_use_eta;
    bool                              m_eval_nested_prop;

    environment const & env() const { return m_ctx.env(); }

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = m_ctx.push_local(binding_name(e), d, binding_info(e));
        expr b = m_ctx.abstract_locals(normalize(instantiate(binding_body(e), l)), 1, &l);
        m_ctx.pop_local();
        return update_binding(e, d, b);
    }

    optional<expr> is_constructor_like(expr const & e) {
        if (is_constructor_app(env(), e))
            return some_expr(e);
        else
            return none_expr();
    }

    optional<expr> unfold_recursor_core(expr const & f, unsigned i,
                                        buffer<unsigned> const & idxs, buffer<expr> & args, bool is_rec) {
        if (i == idxs.size()) {
            expr new_app = mk_rev_app(f, args);
            if (is_rec)
                return some_expr(normalize(new_app));
            else if (optional<expr> r = unfold_app(env(), new_app))
                return some_expr(normalize(*r));
            else
                return none_expr();
        } else {
            unsigned idx = idxs[i];
            if (idx >= args.size())
                return none_expr();
            expr & arg = args[args.size() - idx - 1];
            optional<expr> new_arg = is_constructor_like(arg);
            if (!new_arg)
                return none_expr();
            flet<expr> set_arg(arg, *new_arg);
            return unfold_recursor_core(f, i+1, idxs, args, is_rec);
        }
    }

    optional<expr> unfold_recursor_like(expr const & f, list<unsigned> const & idx_lst, buffer<expr> & args) {
        buffer<unsigned> idxs;
        to_buffer(idx_lst, idxs);
        return unfold_recursor_core(f, 0, idxs, args, false);
    }

    optional<expr> unfold_recursor_major(expr const & f, unsigned idx, buffer<expr> & args) {
        buffer<unsigned> idxs;
        idxs.push_back(idx);
        return unfold_recursor_core(f, 0, idxs, args, true);
    }

    bool is_prop(expr const & e) {
        return m_ctx.whnf(m_ctx.infer(e)) == mk_Prop();
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = a;
            if (m_eval_nested_prop || !is_prop(m_ctx.infer(a)))
                new_a = normalize(a);
            if (new_a != a)
                modified = true;
            a = new_a;
        }
        if (is_constant(f)) {
            if (auto idx = inductive::get_elim_major_idx(env(), const_name(f))) {
                if (auto r = unfold_recursor_major(f, *idx, args))
                    return *r;
            }
        }
        if (!modified)
            return e;
        expr r = mk_rev_app(f, args);
        if (is_constant(f) && env().is_recursor(const_name(f))) {
            return normalize(r);
        } else {
            return r;
        }
    }

    expr normalize(expr e) {
        check_system("normalize");
        if (!m_pred(e))
            return e;
        e = m_ctx.whnf(e);
        switch (e.kind()) {
        case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Meta: case expr_kind::Local: case expr_kind::Macro:
            return e;
        case expr_kind::Lambda: {
            e = normalize_binding(e);
            if (m_use_eta)
                return try_eta(e);
            else
                return e;
        }
        case expr_kind::Pi:
            return normalize_binding(e);
        case expr_kind::App:
            return normalize_app(e);
        case expr_kind::Let:
            // whnf unfolds let-exprs
            lean_unreachable();
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    normalize_fn(abstract_type_context & ctx, bool eta, bool nested_prop = true):
        m_ctx(ctx), m_pred([](expr const &) { return true; }),
        m_use_eta(eta), m_eval_nested_prop(nested_prop) {
    }

    normalize_fn(abstract_type_context & ctx, std::function<bool(expr const &)> const & fn, bool eta, bool nested_prop = true): // NOLINT
        m_ctx(ctx), m_pred(fn), m_use_eta(eta), m_eval_nested_prop(nested_prop) {
    }

    expr operator()(expr const & e) {
        return normalize(e);
    }
};

expr normalize(environment const & env, expr const & e, bool eta) {
    type_checker ctx(env);
    return normalize_fn(ctx, eta)(e);
}

expr normalize(abstract_type_context & ctx, expr const & e, bool eta) {
    return normalize_fn(ctx, eta)(e);
}
}




// ========== placeholder.h ==========

/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

// Placeholders are used to mark locations where additional
// metavariables should be inserted.
namespace lean {
/** \brief Return a new universe level placeholder. */
level mk_level_placeholder();
level mk_level_one_placeholder();

enum class expr_placeholder_kind { Implicit, StrictImplicit, Explicit };
/** \brief Return a new expression placeholder expression. */
expr mk_expr_placeholder(optional<expr> const & type = none_expr(), expr_placeholder_kind k = expr_placeholder_kind::Implicit);
inline expr mk_explicit_expr_placeholder(optional<expr> const & type = none_expr()) {
    return mk_expr_placeholder(type, expr_placeholder_kind::Explicit);
}
inline expr mk_strict_expr_placeholder(optional<expr> const & type = none_expr()) {
    return mk_expr_placeholder(type, expr_placeholder_kind::StrictImplicit);
}

/** \brief Return true if the given level is a placeholder. */
bool is_placeholder(level const & e);
bool is_one_placeholder(level const & e);

/** \brief Return true iff the given expression is a placeholder (strict, explicit or implicit). */
bool is_placeholder(expr const & e);

/** \brief Return true iff the given expression is a strict placeholder. */
bool is_strict_placeholder(expr const & e);

/** \brief Return true iff the given expression is an explicit placeholder. */
bool is_explicit_placeholder(expr const & e);

/** \brief Return the type of the placeholder (if available) */
optional<expr> placeholder_type(expr const & e);

/** \brief Return true iff the given expression contains placeholders. */
bool has_placeholder(expr const & e);

void initialize_placeholder();
void finalize_placeholder();
}




// ========== placeholder.cpp ==========

/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "kernel/find_fn.h"
#include "library/placeholder.h"

namespace lean {
static name * g_placeholder_one_name      = nullptr;
static name * g_implicit_placeholder_name = nullptr;
static name * g_placeholder_name          = nullptr;
static name * g_strict_placeholder_name   = nullptr;
static name * g_explicit_placeholder_name = nullptr;

void initialize_placeholder() {
    g_placeholder_one_name      = new name(name::mk_internal_unique_name(), "_");
    g_implicit_placeholder_name = new name(name::mk_internal_unique_name(), "_");
    g_placeholder_name          = g_implicit_placeholder_name;
    g_strict_placeholder_name   = new name(name::mk_internal_unique_name(), "_");
    g_explicit_placeholder_name = new name(name::mk_internal_unique_name(), "_");
}

void finalize_placeholder() {
    delete g_implicit_placeholder_name;
    delete g_strict_placeholder_name;
    delete g_explicit_placeholder_name;
    delete g_placeholder_one_name;
}

LEAN_THREAD_VALUE(unsigned, g_placeholder_id, 0);
static unsigned next_placeholder_id() {
    unsigned r = g_placeholder_id;
    g_placeholder_id++;
    return r;
}
level mk_level_placeholder() { return mk_param_univ(name(*g_placeholder_name, next_placeholder_id())); }
level mk_level_one_placeholder() { return mk_param_univ(*g_placeholder_one_name); }
static name const & to_prefix(expr_placeholder_kind k) {
    switch (k) {
    case expr_placeholder_kind::Implicit:       return *g_implicit_placeholder_name;
    case expr_placeholder_kind::StrictImplicit: return *g_strict_placeholder_name;
    case expr_placeholder_kind::Explicit:       return *g_explicit_placeholder_name;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
expr mk_expr_placeholder(optional<expr> const & type, expr_placeholder_kind k) {
    name n(to_prefix(k), next_placeholder_id());
    if (type)
        return mk_local(n, *type);
    else
        return mk_constant(n);
}
static bool is_placeholder(name const & n) {
    if (n.is_atomic())
        return false;
    name const & p = n.get_prefix();
    return p == *g_implicit_placeholder_name || p == *g_strict_placeholder_name || p == *g_explicit_placeholder_name;
}
static bool is_strict_placeholder(name const & n) {
    return !n.is_atomic() && n.get_prefix() == *g_strict_placeholder_name;
}
static bool is_explicit_placeholder(name const & n) {
    return !n.is_atomic() && n.get_prefix() == *g_explicit_placeholder_name;
}
bool is_placeholder(level const & e) { return is_param(e) && is_placeholder(param_id(e)); }
bool is_one_placeholder(level const & e) { return is_param(e) && param_id(e) == *g_placeholder_one_name; }

bool is_placeholder(expr const & e) {
    return (is_constant(e) && is_placeholder(const_name(e))) || (is_local(e) && is_placeholder(mlocal_name(e)));
}
bool is_strict_placeholder(expr const & e) {
    return (is_constant(e) && is_strict_placeholder(const_name(e))) || (is_local(e) && is_strict_placeholder(mlocal_name(e)));
}
bool is_explicit_placeholder(expr const & e) {
    return (is_constant(e) && is_explicit_placeholder(const_name(e))) || (is_local(e) && is_explicit_placeholder(mlocal_name(e)));
}
optional<expr> placeholder_type(expr const & e) {
    if (is_local(e) && is_placeholder(e))
        return some_expr(mlocal_type(e));
    else
        return none_expr();
}

bool has_placeholder(level const & l) {
    bool r = false;
    for_each(l, [&](level const & e) {
            if (is_placeholder(e) || is_one_placeholder(e))
                r = true;
            return !r;
        });
    return r;
}

bool has_placeholder(expr const & e) {
    return (bool) find(e, [](expr const & e, unsigned) { // NOLINT
            if (is_placeholder(e))
                return true;
            else if (is_sort(e))
                return has_placeholder(sort_level(e));
            else if (is_constant(e))
                return std::any_of(const_levels(e).begin(), const_levels(e).end(), [](level const & l) { return has_placeholder(l); });
            else
                return false;
        });
}
}




// ========== delayed_abstraction.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns);
expr mk_delayed_abstraction(expr const & e, name const & n);
bool is_delayed_abstraction(expr const & e);
expr const & get_delayed_abstraction_expr(expr const & e);
void get_delayed_abstraction_info(expr const & e, buffer<name> & ns, buffer<expr> & es);
/* Given a delayed abstraction `[delayed t, h_1 := e_1, ..., h_n := e_n]`, push
   the delayed substitutions `h_i := e_i` to the metavariables occurring in `t`.

   Remark: if `t` is a metavariable, then we just return `e`. */
expr push_delayed_abstraction(expr const & e);
/* Append the new delayed substitutions `ns[i] := es[i]` to the metavariables occurring in `e`.

   \pre ns.size() == es.size() */
expr append_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & es);

/* Create e{ls[0] := ls[0], ..., ls[n-1] := ls[n-1]}
   \pre is_metavar(e)
   \pre for all x in ls, is_local(x) */
expr mk_delayed_abstraction_with_locals(expr const & e, buffer<expr> const & ls);

/* Ceeate e{ns[0] := vs[0], ... ls[n-1] := vs[n-1]}
   \pre is_metavar(e)
   \pre ns.size() == es.size()
   \pre !ns.empty() */
expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs);

class metavar_context;

/* Similar to abstract_locals, but create a delayed_abstraction macro around metavariables
   occurring in \c e. */
expr delayed_abstract_locals(metavar_context const & mctx, expr const & e, unsigned nlocals, expr const * locals);

void initialize_delayed_abstraction();
void finalize_delayed_abstraction();
}




// ========== delayed_abstraction.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/freset.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/abstract_type_context.h"
#include "library/replace_visitor.h"
#include "library/metavar_context.h"

namespace lean {
static name * g_delayed_abstraction_macro = nullptr;
/** \brief Delayed abstraction macro. This is an auxiliary temporary macro used by the tactic framework.
    It is used in the following kind of situation.
    Suppose we have a goal ?M

            CTX |- A -> B

    Then, we apply the intro tactic and create the new goal ?M'

            CTX, H : A |- B

    The intro tactic adds the following assignment to the metavariable context

           ?M := fun H : A, (delayed_abstraction[H] ?M' #0)

     The delayed_abstraction macro indicates that when ?M' is instantiated, we need to replace
     the local constant H with the de-bruijn index 0 at this assignment.
*/
class delayed_abstraction_macro : public macro_definition_cell {
    list<name> m_value;
public:
    delayed_abstraction_macro(list<name> const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const override {
        /** TODO(Leo): improve if needed */
        return length(m_value) < length(static_cast<delayed_abstraction_macro const &>(d).m_value);
    }
    virtual name get_name() const override { return *g_delayed_abstraction_macro; }
    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const override {
        return ctx.infer(macro_arg(e, macro_num_args(e) - 1));
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return none_expr();
    }
    virtual unsigned trust_level() const override { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        delayed_abstraction_macro const * other_ptr = dynamic_cast<delayed_abstraction_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual unsigned hash() const override {
        /** TODO(Leo): improve if needed */
        return length(m_value);
    }
    virtual void write(serializer &) const override { lean_unreachable(); }
    list<name> const & get_names() const { return m_value; }
};

/** \brief Each name occurs only once. */
bool validate_delayed_abstraction(buffer<name> const & b) {
    for (unsigned i = 0; i < b.size(); i++) {
        for (unsigned j = i + 1; j < b.size(); j++) {
            if (b[i] == b[j])
                return false;
        }
    }
    return true;
}

bool validate_delayed_abstraction(list<name> const & s) {
    buffer<name> b;
    to_buffer(s, b);
    return validate_delayed_abstraction(b);
}

expr mk_delayed_abstraction_core(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    lean_assert(is_metavar(e));
    lean_assert(ns.size() == vs.size());
    buffer<expr> args;
    args.append(vs);
    args.push_back(e);
    return mk_macro(macro_definition(new delayed_abstraction_macro(to_list(ns))), args.size(), args.data());
}

bool is_delayed_abstraction(expr const & e) {
    return is_macro(e) && dynamic_cast<delayed_abstraction_macro const *>(macro_def(e).raw()) != nullptr;
}

void get_delayed_abstraction_info(expr const & e, buffer<name> & ns, buffer<expr> & es) {
    lean_assert(is_delayed_abstraction(e));
    to_buffer(static_cast<delayed_abstraction_macro const *>(macro_def(e).raw())->get_names(), ns);
    es.append(macro_num_args(e) - 1, macro_args(e));
}

expr const & get_delayed_abstraction_expr(expr const & e) {
    lean_assert(is_delayed_abstraction(e));
    return macro_arg(e, macro_num_args(e) - 1);
}

struct push_delayed_abstraction_fn : public replace_visitor {
    buffer<name>            m_ns;
    buffer<expr>            m_vs;
    buffer<unsigned>        m_deltas;
    /* If m_mctx is not nullptr we use it to filter unnecessary delayed abstractions. */
    metavar_context const * m_mctx{nullptr};

    void add_vidxs(int v) {
        for (unsigned & d : m_deltas)
            d += v;
    }

    void inc_vidxs() { add_vidxs(1); }
    void dec_vidxs() { add_vidxs(-1); }

    virtual expr visit_binding(expr const & e) override {
        expr new_d = visit(binding_domain(e));
        inc_vidxs();
        expr new_b;
        {
            freset<cache> reset_cache(m_cache);
            new_b = visit(binding_body(e));
        }
        dec_vidxs();
        return update_binding(e, new_d, new_b);
    }

    virtual expr visit_let(expr const & e) override {
        expr new_t = visit(let_type(e));
        expr new_v = visit(let_value(e));
        inc_vidxs();
        expr new_b;
        {
            freset<cache> reset_cache(m_cache);
            new_b = visit(let_body(e));
        }
        dec_vidxs();
        return update_let(e, new_t, new_v, new_b);
    }

    virtual expr visit_app(expr const & e) override {
        expr new_f = visit(app_fn(e));
        expr new_a = visit(app_arg(e));
        return update_app(e, new_f, new_a);
    }

    virtual expr visit_var(expr const & e) override {
        return e;
    }

    virtual expr visit_local(expr const & e) override {
        for (unsigned i = 0; i < m_ns.size(); i++) {
            if (m_ns[i] == mlocal_name(e)) {
                return lift_free_vars(m_vs[i], m_deltas[i]);
            }
        }
        return e;
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_delayed_abstraction(e)) {
            unsigned sz = m_vs.size();
            buffer<name> new_ns;
            buffer<expr> new_vs;
            get_delayed_abstraction_info(e, new_ns, new_vs);
            lean_assert(new_ns.size() == new_vs.size());
            for (expr & v : new_vs)
                v = visit(v);
            m_ns.append(new_ns);
            m_vs.append(new_vs);
            m_deltas.resize(m_vs.size(), 0);
            expr r;
            {
                freset<cache> reset_cache(m_cache);
                r = visit(get_delayed_abstraction_expr(e));
            }
            m_ns.shrink(sz);
            m_vs.shrink(sz);
            m_deltas.shrink(sz);
            return r;
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    virtual expr visit_meta(expr const & e) override {
        if (m_mctx && is_metavar_decl_ref(e)) {
            if (optional<metavar_decl> decl = m_mctx->find_metavar_decl(e)) {
                /* We only include delayed substitutions that are in the scope of `e` */
                local_context const & lctx = decl->get_context();
                buffer<name> new_ns;
                buffer<expr> new_vs;
                for (unsigned i = 0; i < m_vs.size(); i++) {
                    if (lctx.find_local_decl(m_ns[i])) {
                        new_ns.push_back(m_ns[i]);
                        new_vs.push_back(lift_free_vars(m_vs[i], m_deltas[i]));
                    }
                }
                if (new_vs.empty())
                    return e;
                else
                    return mk_delayed_abstraction_core(e, new_ns, new_vs);
            }
        }
        /* Otherwise include all delayed substitutions */
        buffer<expr> new_vs;
        for (unsigned i = 0; i < m_vs.size(); i++) {
            new_vs.push_back(lift_free_vars(m_vs[i], m_deltas[i]));
        }
        return mk_delayed_abstraction_core(e, m_ns, new_vs);
    }

    push_delayed_abstraction_fn(buffer<name> const & ns, buffer<expr> const & vs) {
        lean_assert(ns.size() == vs.size());
        m_ns.append(ns);
        m_vs.append(vs);
        m_deltas.resize(vs.size(), 0);
    }

    push_delayed_abstraction_fn(buffer<name> const & ns, buffer<expr> const & vs, metavar_context const & mctx):
        push_delayed_abstraction_fn(ns, vs) {
        m_mctx = &mctx;
    }
};

expr push_delayed_abstraction(expr const & e) {
    lean_assert(is_delayed_abstraction(e));
    expr const & a = get_delayed_abstraction_expr(e);
    if (is_metavar(a)) {
        return e;
    } else {
        buffer<name> ns;
        buffer<expr> vs;
        get_delayed_abstraction_info(e, ns, vs);
        return push_delayed_abstraction_fn(ns, vs)(a);
    }
}

expr append_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    return push_delayed_abstraction_fn(ns, vs)(e);
}

expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns) {
    lean_assert(ns.size() > 0);
    buffer<expr> vs;
    unsigned sz = ns.size();
    for (unsigned i = 0; i < sz; i++) {
        vs.push_back(mk_var(sz - i - 1));
    }
    if (is_metavar(e)) {
        return mk_delayed_abstraction_core(e, ns, vs);
    } else {
        return push_delayed_abstraction_fn(ns, vs)(e);
    }
}

expr mk_delayed_abstraction(expr const & e, name const & n) {
    buffer<name> ns;
    ns.push_back(n);
    return mk_delayed_abstraction(e, ns);
}

expr mk_delayed_abstraction_with_locals(expr const & e, buffer<expr> const & ls) {
    lean_assert(is_metavar(e));
    lean_assert(std::all_of(ls.begin(), ls.end(), is_local));
    buffer<name> ns;
    for (expr const & l : ls)
        ns.push_back(mlocal_name(l));
    return mk_delayed_abstraction_core(e, ns, ls);
}

expr mk_delayed_abstraction(expr const & e, buffer<name> const & ns, buffer<expr> const & vs) {
    lean_assert(ns.size() > 0);
    lean_assert(ns.size() == vs.size());
    if (is_metavar(e)) {
        return mk_delayed_abstraction_core(e, ns, vs);
    } else {
        return push_delayed_abstraction_fn(ns, vs)(e);
    }
}

expr delayed_abstract_locals(metavar_context const & mctx, expr const & e, unsigned nlocals, expr const * locals) {
    lean_assert(std::all_of(locals, locals + nlocals, is_local));
    if (!has_expr_metavar(e))
        return abstract_locals(e, nlocals, locals);
    buffer<name> ns;
    buffer<expr> vs;
    for (unsigned i = 0; i < nlocals; i++) {
        ns.push_back(mlocal_name(locals[i]));
        vs.push_back(mk_var(nlocals - i - 1));
    }
    return push_delayed_abstraction_fn(ns, vs, mctx)(e);
}

void initialize_delayed_abstraction() {
    g_delayed_abstraction_macro = new name("delayed_abstraction");
}

void finalize_delayed_abstraction() {
    delete g_delayed_abstraction_macro;
}
}




// ========== protected.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Mark \c n as protected, protected declarations are ignored by wildcard 'open' command */
environment add_protected(environment const & env, name const & n);
/** \brief Return true iff \c n was marked as protected in the environment \c n. */
bool is_protected(environment const & env, name const & n);
/** \brief Return the shortest name that can be used to reference the given name */
name get_protected_shortest_name(name const & n);

void initialize_protected();
void finalize_protected();
}




// ========== protected.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/name_set.h"
#include "library/protected.h"
#include "library/module.h"

namespace lean {
struct protected_ext : public environment_extension {
    name_set m_protected; // protected declarations
};

struct protected_ext_reg {
    unsigned m_ext_id;
    protected_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<protected_ext>()); }
};

static protected_ext_reg * g_ext = nullptr;
static protected_ext const & get_extension(environment const & env) {
    return static_cast<protected_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, protected_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<protected_ext>(ext));
}

struct protected_modification : public modification {
    LEAN_MODIFICATION("prt")

    name m_name;

    protected_modification() {}
    protected_modification(name const & n) : m_name(n) {}

    void perform(environment & env) const override {
        protected_ext ext = get_extension(env);
        ext.m_protected.insert(m_name);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<protected_modification>(read_name(d));
    }
};

environment add_protected(environment const & env, name const & n) {
    return module::add_and_perform(env, std::make_shared<protected_modification>(n));
}

bool is_protected(environment const & env, name const & n) {
    return get_extension(env).m_protected.contains(n);
}

name get_protected_shortest_name(name const & n) {
    if (n.is_atomic() || n.get_prefix().is_atomic()) {
        return n;
    } else {
        name new_prefix = n.get_prefix().replace_prefix(n.get_prefix().get_prefix(), name());
        return n.replace_prefix(n.get_prefix(), new_prefix);
    }
}

void initialize_protected() {
    g_ext     = new protected_ext_reg();
    protected_modification::init();
}

void finalize_protected() {
    protected_modification::finalize();
    delete g_ext;
}
}




// ========== string.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/environment.h"

namespace lean {
/**
    \brief Return an expression that encodes the given string in as a Lean expression.
    \post *to_string(from_string(s)) == s */
expr from_string(std::string const & s);

/** \brief If the given expression encodes a string, then convert it back to a string.
    \see from_string */
optional<std::string> to_string(expr const & e);
bool is_string_value(expr const & e);

bool is_string_macro(expr const & e);
/** \brief Expand string macro if 'e' is a string macro */
optional<expr> expand_string_macro(expr const & e);

optional<unsigned> to_char_core(expr const & e);
bool is_char_value_core(expr const & e);

optional<unsigned> to_char(abstract_type_context & ctx, expr const & e);
bool is_char_value(abstract_type_context & ctx, expr const & e);

format pp_string_literal(std::string const & s);
format pp_char_literal(unsigned c);

void initialize_string();
void finalize_string();
}




// ========== string.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "util/utf8.h"
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/string.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/trace.h"

namespace lean {
static name * g_string_macro         = nullptr;
static std::string * g_string_opcode = nullptr;
static expr * g_nat                  = nullptr;
static expr * g_char                 = nullptr;
static expr * g_char_mk              = nullptr;
static expr * g_char_of_nat          = nullptr;
static expr * g_string               = nullptr;
static expr * g_empty                = nullptr;
static expr * g_str                  = nullptr;
static expr * g_fin_mk               = nullptr;

expr from_string_core(std::string const & s);

static void display_char_literal_utf8(std::ostream & out, unsigned char c, bool in_string) {
    if (c == '\n') {
        out << "\\n";
    } else if (c == '\t') {
        out << "\\t";
    } else if (c == '\\') {
        out << "\\\\";
    } else if (in_string && c == '\"') {
        out << "\\\"";
    } else if (!in_string && c == '\'') {
        out << "\\'";
    } else if (c >= 32 && c != 127) {
        out << c;
    } else {
        out << "\\x";
        if (c < 16) out << "0";
        out << std::hex << static_cast<unsigned>(c);
    }
}

static void display_char_literal(std::ostream & out, unsigned c) {
    out << "'";
    std::string s;
    push_unicode_scalar(s, c);
    for (unsigned i = 0; i < s.size(); i++) {
        display_char_literal_utf8(out, s[i], false);
    }
    out << "'";
}

static void display_string_literal(std::ostream & out, std::string const & s) {
    out << "\"";
    for (unsigned i = 0; i < s.size(); i++) {
        display_char_literal_utf8(out, s[i], true);
    }
    out << "\"";
}

format pp_string_literal(std::string const & s) {
    std::ostringstream out;
    display_string_literal(out, s);
    return format(out.str());
}

format pp_char_literal(unsigned c) {
    std::ostringstream out;
    display_char_literal(out, c);
    return format(out.str());
}

/** \brief The string macro is a compact way of encoding strings inside Lean expressions. */
class string_macro : public macro_definition_cell {
    std::string m_value;
public:
    string_macro(std::string const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<string_macro const &>(d).m_value;
    }
    virtual name get_name() const { return *g_string_macro; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const {
        return *g_string;
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return some_expr(from_string_core(m_value));
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        string_macro const * other_ptr = dynamic_cast<string_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual void display(std::ostream & out) const {
        display_string_literal(out, m_value);
    }
    virtual unsigned hash() const { return std::hash<std::string>()(m_value); }
    virtual void write(serializer & s) const { s << *g_string_opcode << m_value; }
    std::string const & get_value() const { return m_value; }
};

expr mk_string_macro(std::string const & v) {
    return mk_macro(macro_definition(new string_macro(v)));
}

bool is_string_macro(expr const & e) {
    return is_macro(e) && dynamic_cast<string_macro const *>(macro_def(e).raw()) != nullptr;
}

string_macro const & to_string_macro(expr const & e) {
    lean_assert(is_string_macro(e));
    return *static_cast<string_macro const *>(macro_def(e).raw());
}

void initialize_string() {
    g_string_macro    = new name("string_macro");
    g_string_opcode   = new std::string("Str");
    g_nat             = new expr(Const(get_nat_name()));
    g_char            = new expr(Const(get_char_name()));
    g_char_mk         = new expr(Const(get_char_mk_name()));
    g_char_of_nat     = new expr(Const(get_char_of_nat_name()));
    g_string          = new expr(Const(get_string_name()));
    g_empty           = new expr(Const(get_string_empty_name()));
    g_str             = new expr(Const(get_string_str_name()));
    g_fin_mk          = new expr(Const(get_fin_mk_name()));
    register_macro_deserializer(*g_string_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    std::string v = d.read_string();
                                    return mk_string_macro(v);
                                });
}

optional<expr> expand_string_macro(expr const & e) {
    if (!is_string_macro(e)) return none_expr();
    return some_expr(from_string_core(to_string_macro(e).get_value()));
}

void finalize_string() {
    delete g_nat;
    delete g_str;
    delete g_empty;
    delete g_string;
    delete g_char_of_nat;
    delete g_char;
    delete g_char_mk;
    delete g_string_opcode;
    delete g_string_macro;
    delete g_fin_mk;
}

expr from_string_core(std::string const & s) {
    buffer<unsigned> tmp;
    utf8_decode(s, tmp);
    expr r = *g_empty;
    for (unsigned i = 0; i < tmp.size(); i++) {
        expr n = to_nat_expr(mpz(tmp[i]));
        expr c = mk_app(*g_char_of_nat, n);
        r = mk_app(*g_str, r, c);
    }
    return r;
}

expr from_string(std::string const & s) {
    return mk_string_macro(s);
}

optional<unsigned> to_char_core(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (fn == *g_char_mk && args.size() == 2) {
        if (auto n = to_num(args[0])) {
            return optional<unsigned>(n->get_unsigned_int());
        } else {
            return optional<unsigned>();
        }
    } else if (fn == *g_char_of_nat && args.size() == 1) {
        if (auto n = to_num(args[0])) {
            return optional<unsigned>(n->get_unsigned_int());
        } else {
            return optional<unsigned>();
        }
    } else {
        return optional<unsigned>();
    }
}

bool is_char_value_core(expr const & e) {
    return static_cast<bool>(to_char_core(e));
}

optional<unsigned> to_char(abstract_type_context & ctx, expr const & e) {
    if (auto v = to_char_core(e)) {
        if (ctx.is_def_eq(ctx.infer(e), mk_char_type()))
            return v;
    }
    return optional<unsigned>();
}

bool is_char_value(abstract_type_context & ctx, expr const & e) {
    if (!is_char_value_core(e))
        return false;
    expr type = ctx.infer(e);
    if (has_expr_metavar(type))
        return false;
    return ctx.is_def_eq(type, mk_char_type());
}

static bool append_char(expr const & e, std::string & r) {
    if (auto c = to_char_core(e)) {
        push_unicode_scalar(r, *c);
        return true;
    } else {
        return false;
    }
}

bool to_string_core(expr const & e, std::string & r) {
    if (e == *g_empty) {
        return true;
    } else if (is_string_macro(e)) {
        r = to_string_macro(e).get_value();
        return true;
    } else {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (fn == *g_str && args.size() == 2) {
            return to_string_core(args[0], r) && append_char(args[1], r);
        } else {
            return false;
        }
    }
}

optional<std::string> to_string(expr const & e) {
    if (is_string_macro(e)) {
        return optional<std::string>(to_string_macro(e).get_value());
    } else {
        std::string tmp;
        if (to_string_core(e, tmp)) {
            return optional<std::string>(tmp);
        } else {
            return optional<std::string>();
        }
    }
}

bool is_string_value(expr const & e) {
    /* TODO(Leo): optimize if needed */
    return static_cast<bool>(to_string(e));
}
}




// ========== comp_val.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/** \brief If 'a' and 'b' are two distinct natural number values, then return a proof
    they are disequal. Otherwise return none.

    \remark This function assumes 'a' and 'b' have type nat.

    \remark A natural number value is any expression built using
    bit0, bit1, zero, one and nat.zero */
optional<expr> mk_nat_val_ne_proof(expr const & a, expr const & b);

/** \brief If 'a' and 'b' are two natural number values s.t. a < b,
    then return a proof for a < b. Otherwise return none.

    \remark This function assumes 'a' and 'b' have type nat.

    \remark A natural number value is any expression built using
    bit0, bit1, zero, one and nat.zero */
optional<expr> mk_nat_val_lt_proof(expr const & a, expr const & b);
/* Same for a <= b */
optional<expr> mk_nat_val_le_proof(expr const & a, expr const & b);

/* Similar to mk_nat_val_ne_proof, but for fin type */
optional<expr> mk_fin_val_ne_proof(expr const & a, expr const & b);

/* Similar to mk_nat_val_ne_proof, but for char type */
optional<expr> mk_char_val_ne_proof(expr const & a, expr const & b);

/* Similar to mk_nat_val_ne_proof, but for string type */
optional<expr> mk_string_val_ne_proof(expr a, expr b);

/* Return a proof for e >= 0 if e is a nonnegative int numeral.

   \pre typeof(e) is int. */
optional<expr> mk_int_val_nonneg_proof(expr const & e);

/* Return a proof for e > 0 if e is a nonnegative int numeral.

   \pre typeof(e) is int. */
optional<expr> mk_int_val_pos_proof(expr const & a);

/* Similar to mk_nat_val_ne_proof, but for int type */
optional<expr> mk_int_val_ne_proof(expr const & a, expr const & b);

/* Return a proof for a != b, a/b has type nat/int/char/string, and they are distinct values. */
optional<expr> mk_val_ne_proof(type_context_old & ctx, expr const & a, expr const & b);

void initialize_comp_val();
void finalize_comp_val();
}




// ========== comp_val.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/num.h"
#include "library/string.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/comp_val.h"
#include "library/expr_pair.h"
#include "library/trace.h"

/* Remark: we can improve performance by using Lean macros for delaying the
   proof construction. */

namespace lean {
optional<expr> mk_nat_val_ne_proof(expr const & a, expr const & b) {
    if (a == b) return none_expr();
    if (auto a1 = is_bit0(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_ne_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit0_ne_bit1_name()), *a1, *b1));
        } else if (is_zero(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, b))
                return some_expr(mk_app(mk_constant(get_nat_bit0_ne_zero_name()), *a1, *pr));
        } else if (is_one(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit0_ne_one_name()), *a1));
        }
    } else if (auto a1 = is_bit1(a)) {
        if (auto b1 = is_bit0(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit1_ne_bit0_name()), *a1, *b1));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_ne_name()), *a1, *b1, *pr));
        } else if (is_zero(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit1_ne_zero_name()), *a1));
        } else if (is_one(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_bit1_ne_one_name()), *a1, *pr));
        }
    } else if (is_zero(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, a))
                return some_expr(mk_app(mk_constant(get_nat_zero_ne_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_zero_ne_bit1_name()), *b1));
        } else if (is_one(b)) {
            return some_expr(mk_constant(get_nat_zero_ne_one_name()));
        }
    } else if (is_one(a)) {
        if (auto b1 = is_bit0(b)) {
            return some_expr(mk_app(mk_constant(get_nat_one_ne_bit0_name()), *b1));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_ne_bit1_name()), *b1, *pr));
        } else if (is_zero(b)) {
            return some_expr(mk_constant(get_nat_one_ne_zero_name()));
        }
    }
    return none_expr();
}

optional<expr> mk_nat_val_le_proof(expr const & a, expr const & b);

optional<expr> mk_nat_val_lt_proof(expr const & a, expr const & b) {
    if (a == b) return none_expr();
    if (auto a1 = is_bit0(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_lt_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_le_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_lt_bit1_name()), *a1, *b1, *pr));
        }
    } else if (auto a1 = is_bit1(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_lt_bit0_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_lt_name()), *a1, *b1, *pr));
        }
    } else if (is_zero(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, a))
                return some_expr(mk_app(mk_constant(get_nat_zero_lt_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_zero_lt_bit1_name()), *b1));
        } else if (is_one(b)) {
            return some_expr(mk_constant(get_nat_zero_lt_one_name()));
        }
    } else if (is_one(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_lt_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_lt_bit1_name()), *b1, *pr));
        }
    }
    return none_expr();
}

optional<expr> mk_nat_val_le_proof(expr const & a, expr const & b) {
    if (a == b)
        return some_expr(mk_app(mk_constant(get_nat_le_refl_name()), a));
    if (auto pr = mk_nat_val_lt_proof(a, b))
        return some_expr(mk_app(mk_constant(get_nat_le_of_lt_name()), a, b, *pr));
    return none_expr();
}

optional<expr> mk_fin_val_ne_proof(expr const & a, expr const & b) {
    if (!is_app_of(a, get_fin_mk_name(), 3) ||
        !is_app_of(b, get_fin_mk_name(), 3))
        return none_expr();
    expr const & n   = app_arg(app_fn(app_fn(a)));
    expr const & v_a = app_arg(app_fn(a));
    expr const & v_b = app_arg(app_fn(b));
    auto pr = mk_nat_val_ne_proof(v_a, v_b);
    if (!pr) return none_expr();
    return some_expr(mk_app(mk_constant(get_fin_ne_of_vne_name()), n, a, b, *pr));
}

optional<expr> mk_char_mk_ne_proof(expr const & a, expr const & b) {
    if (!is_app_of(a, get_char_mk_name(), 2) ||
        !is_app_of(a, get_char_mk_name(), 2))
        return none_expr();
    expr const & v_a = app_arg(app_fn(a));
    expr const & v_b = app_arg(app_fn(b));
    auto pr = mk_nat_val_ne_proof(v_a, v_b);
    if (!pr) return none_expr();
    return some_expr(mk_app(mk_constant(get_char_ne_of_vne_name()), a, b, *pr));
}

static expr * g_d800   = nullptr;
static expr * g_dfff   = nullptr;
static expr * g_110000 = nullptr;

optional<expr> mk_is_valid_char_proof(expr const & v) {
    if (auto h = mk_nat_val_lt_proof(v, *g_d800)) {
        return some_expr(mk_app(mk_constant(get_is_valid_char_range_1_name()), v, *h));
    }

    if (auto h_1 = mk_nat_val_lt_proof(*g_dfff, v)) {
    if (auto h_2 = mk_nat_val_lt_proof(v, *g_110000)) {
        return some_expr(mk_app(mk_constant(get_is_valid_char_range_2_name()), v, *h_1, *h_2));
    }}

    return none_expr();
}

optional<expr> mk_char_val_ne_proof(expr const & a, expr const & b) {
    if (is_app_of(a, get_char_of_nat_name(), 1) &&
        is_app_of(a, get_char_of_nat_name(), 1)) {
        expr const & v_a = app_arg(a);
        expr const & v_b = app_arg(b);
        if (auto h_1 = mk_nat_val_ne_proof(v_a, v_b)) {
        if (auto h_2 = mk_is_valid_char_proof(v_a)) {
        if (auto h_3 = mk_is_valid_char_proof(v_b)) {
            return some_expr(mk_app({mk_constant(get_char_of_nat_ne_of_ne_name()), v_a, v_b, *h_1, *h_2, *h_3}));
        }}}
    }
    return mk_char_mk_ne_proof(a, b);
}

/* Remark: this function assumes 'e' has type string */
static bool is_string_str(expr const & e, expr & s, expr & c) {
    if (is_app_of(e, get_string_str_name(), 2)) {
        s = app_arg(app_fn(e));
        c = app_arg(e);
        return true;
    }
    return false;
}

/* Remark: this function assumes 'e' has type string */
static bool is_string_empty(expr const & e) {
    return is_constant(e, get_string_empty_name());
}

optional<expr> mk_string_val_ne_proof(expr a, expr b) {
    if (auto new_a = expand_string_macro(a))
        a = *new_a;
    if (auto new_b = expand_string_macro(b))
        b = *new_b;
    expr c_a, s_a;
    expr c_b, s_b;
    if (is_string_str(a, s_a, c_a)) {
        if (is_string_str(b, s_b, c_b)) {
            if (auto pr = mk_char_val_ne_proof(c_a, c_b)) {
                return some_expr(mk_app({mk_constant(get_string_str_ne_str_left_name()), c_a, c_b, s_a, s_b, *pr}));
            } else if (auto pr = mk_string_val_ne_proof(s_a, s_b)) {
                return some_expr(mk_app({mk_constant(get_string_str_ne_str_right_name()), c_a, c_b, s_a, s_b, *pr}));
            }
        } else if (is_string_empty(b)) {
            return some_expr(mk_app(mk_constant(get_string_str_ne_empty_name()), c_a, s_a));
        }
    } else if (is_string_empty(a)) {
        if (is_string_str(b, s_b, c_b)) {
            return some_expr(mk_app(mk_constant(get_string_empty_ne_str_name()), c_b, s_b));
        }
    }
    return none_expr();
}

optional<expr> mk_int_val_nonneg_proof(expr const & a) {
    if (auto a1 = is_bit0(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit0_nonneg_name()), *a1, *pr));
    } else if (auto a1 = is_bit1(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit1_nonneg_name()), *a1, *pr));
    } else if (is_one(a)) {
        return some_expr(mk_constant(get_int_one_nonneg_name()));
    } else if (is_zero(a)) {
        return some_expr(mk_constant(get_int_zero_nonneg_name()));
    }
    return none_expr();
}

optional<expr> mk_int_val_pos_proof(expr const & a) {
    if (auto a1 = is_bit0(a)) {
        if (auto pr = mk_int_val_pos_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit0_pos_name()), *a1, *pr));
    } else if (auto a1 = is_bit1(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit1_pos_name()), *a1, *pr));
    } else if (is_one(a)) {
        return some_expr(mk_constant(get_int_one_pos_name()));
    }
    return none_expr();
}

/* Given a nonnegative int numeral a, return a pair (n, H)
   where n is a nat numeral, and (H : nat_abs a = n) */
optional<expr_pair> mk_nat_abs_eq(expr const & a) {
    if (is_zero(a)) {
        return optional<expr_pair>(mk_pair(mk_nat_zero(), mk_constant(get_int_nat_abs_zero_name())));
    } else if (is_one(a)) {
        return optional<expr_pair>(mk_pair(mk_nat_one(), mk_constant(get_int_nat_abs_one_name())));
    } else if (auto a1 = is_bit0(a)) {
        if (auto p = mk_nat_abs_eq(*a1))
            return optional<expr_pair>(mk_pair(mk_nat_bit0(p->first),
                                               mk_app(mk_constant(get_int_nat_abs_bit0_step_name()), *a1, p->first, p->second)));
    } else if (auto a1 = is_bit1(a)) {
        if (auto p = mk_nat_abs_eq(*a1)) {
            expr new_n   = mk_nat_bit1(p->first);
            expr Hnonneg = *mk_int_val_nonneg_proof(*a1);
            expr new_H   = mk_app(mk_constant(get_int_nat_abs_bit1_nonneg_step_name()), *a1, p->first, Hnonneg, p->second);
            return optional<expr_pair>(mk_pair(new_n, new_H));
        }
    }
    return optional<expr_pair>();
}

/* Given nonneg int numerals a and b, create a proof for a != b IF they are not equal. */
optional<expr> mk_int_nonneg_val_ne_proof(expr const & a, expr const & b) {
    auto p1 = mk_nat_abs_eq(a);
    if (!p1) return none_expr();
    auto p2 = mk_nat_abs_eq(b);
    if (!p2) return none_expr();
    auto Ha_nonneg = mk_int_val_nonneg_proof(a);
    if (!Ha_nonneg) return none_expr();
    auto Hb_nonneg = mk_int_val_nonneg_proof(b);
    if (!Hb_nonneg) return none_expr();
    auto H_nat_ne  = mk_nat_val_ne_proof(p1->first, p2->first);
    if (!H_nat_ne) return none_expr();
    expr H = mk_app({mk_constant(get_int_ne_of_nat_ne_nonneg_case_name()), a, b, p1->first, p2->first,
                *Ha_nonneg, *Hb_nonneg, p1->second, p2->second, *H_nat_ne});
    return some_expr(H);
}

optional<expr> mk_int_val_ne_proof(expr const & a, expr const & b) {
    if (auto a1 = is_neg(a)) {
        if (auto b1 = is_neg(b)) {
            auto H = mk_int_nonneg_val_ne_proof(*a1, *b1);
            if (!H) return none_expr();
            return some_expr(mk_app(mk_constant(get_int_ne_neg_of_ne_name()), *a1, *b1, *H));
        } else {
            if (is_zero(b)) {
                auto H = mk_int_nonneg_val_ne_proof(*a1, b);
                if (!H) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_neg_ne_zero_of_ne_name()), *a1, *H));
            } else {
                auto Ha1_nonneg = mk_int_val_pos_proof(*a1);
                if (!Ha1_nonneg) return none_expr();
                auto Hb_nonneg  = mk_int_val_pos_proof(b);
                if (!Hb_nonneg) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_neg_ne_of_pos_name()), *a1, b, *Ha1_nonneg, *Hb_nonneg));
            }
        }
    } else {
        if (auto b1 = is_neg(b)) {
            if (is_zero(a)) {
                auto H = mk_int_nonneg_val_ne_proof(a, *b1);
                if (!H) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_zero_ne_neg_of_ne_name()), *b1, *H));
            } else {
                auto Ha_nonneg = mk_int_val_pos_proof(a);
                if (!Ha_nonneg) return none_expr();
                auto Hb1_nonneg = mk_int_val_pos_proof(*b1);
                return some_expr(mk_app(mk_constant(get_int_ne_neg_of_pos_name()), a, *b1, *Ha_nonneg, *Hb1_nonneg));
            }
        } else {
            return mk_int_nonneg_val_ne_proof(a, b);
        }
    }
}

optional<expr> mk_val_ne_proof(type_context_old & ctx, expr const & a, expr const & b) {
    expr type = ctx.infer(a);
    if (ctx.is_def_eq(type, mk_nat_type()))
        return mk_nat_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_int_type()))
        return mk_int_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_char_name())))
        return mk_char_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_string_name())))
        return mk_string_val_ne_proof(a, b);
    return none_expr();
}

void initialize_comp_val() {
    g_d800   = new expr(to_nat_expr(mpz(0xd800)));
    g_dfff   = new expr(to_nat_expr(mpz(0xdfff)));
    g_110000 = new expr(to_nat_expr(mpz(0xd110000)));
}

void finalize_comp_val() {
    delete g_d800;
    delete g_dfff;
    delete g_110000;
}
}




// ========== shared_environment.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "util/shared_mutex.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Auxiliary object used when multiple threads are trying to populate the same environment. */
class shared_environment {
    environment          m_env;
    mutable mutex        m_mutex;
public:
    shared_environment();
    shared_environment(environment const & env);
    /** \brief Return a copy of the current environment. This is a constant time operation. */
    environment get_environment() const;
    environment env() const { return get_environment(); }
    /**
        \brief Add the given certified declaration to the environment.
        This is a constant time operation.
        It blocks this object for a small amount of time.
    */
    void add(certified_declaration const & d);
    /**
        \brief Replace the axiom with name <tt>t.get_declaration().get_name()</tt> with the theorem t.get_declaration().
        This is a constant time operation.
        It blocks this object for a small amount of time.
    */
    void replace(certified_declaration const & t);
    /**
       \brief Update the environment using the given function.
       This procedure blocks access to this object.
    */
    void update(std::function<environment(environment const &)> const & f);
};
}




// ========== shared_environment.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/shared_environment.h"

namespace lean {
shared_environment::shared_environment() {}
shared_environment::shared_environment(environment const & env):m_env(env) {}

environment shared_environment::get_environment() const {
    lock_guard<mutex> l(m_mutex);
    return m_env;
}

void shared_environment::add(certified_declaration const & d) {
    lock_guard<mutex> l(m_mutex);
    m_env = m_env.add(d);
}

void shared_environment::replace(certified_declaration const & t) {
    lock_guard<mutex> l(m_mutex);
    m_env = m_env.replace(t);
}

void shared_environment::update(std::function<environment(environment const &)> const & f) {
    lock_guard<mutex> l(m_mutex);
    m_env = f(m_env);
}
}




// ========== deep_copy.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Return a shallow copy of \c e */
expr copy(expr const & e);

/**
    \brief Return a new expression that is equal to the given
    argument, but does not share any memory cell with it.
*/
expr deep_copy(expr const & e);
}




// ========== deep_copy.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"

namespace lean {
expr copy(expr const & a) {
    scoped_expr_caching scope(false);
    switch (a.kind()) {
    case expr_kind::Var:      return mk_var(var_idx(a));
    case expr_kind::Constant: return mk_constant(const_name(a), const_levels(a));
    case expr_kind::Sort:     return mk_sort(sort_level(a));
    case expr_kind::Macro:    return mk_macro(to_macro(a)->m_definition, macro_num_args(a), macro_args(a));
    case expr_kind::App:      return mk_app(app_fn(a), app_arg(a));
    case expr_kind::Lambda:   return mk_lambda(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::Pi:       return mk_pi(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::Meta:     return mk_metavar(mlocal_name(a), mlocal_pp_name(a), mlocal_type(a));
    case expr_kind::Local:    return mk_local(mlocal_name(a), mlocal_pp_name(a), mlocal_type(a), local_info(a));
    case expr_kind::Let:      return mk_let(let_name(a), let_type(a), let_value(a), let_body(a));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr deep_copy(expr const & e) {
    scoped_expr_caching scope(false);
    return replace(e, [](expr const & e) {
            if (is_atomic(e))
                return some_expr(copy(e));
            else
                return none_expr();
        });
}
}




// ========== local_instances.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class local_instance {
    name m_class_name;
    expr m_local;
public:
    local_instance(name const & n, expr const & e):
        m_class_name(n), m_local(e) {}
    name const & get_class_name() const { return m_class_name; }
    expr const & get_local() const { return m_local; }
    friend bool operator==(local_instance const & l1, local_instance const & l2) {
        return mlocal_name(l1.m_local) == mlocal_name(l2.m_local);
    }
};

inline bool operator!=(local_instance const & l1, local_instance const & l2) {
    return !(l1 == l2);
}

typedef list<local_instance> local_instances;
}




// ========== ac_match.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once


/*
(Design notes)

The simplifier will be the main consumer of this module.
The simplifier will use AC matching for any simp lemma marked with the [ac_match] attribute.
If AC matching fails, we use the matching procedure provided by type_context_old.
The AC matching procedure implemented here does not subsume the matching procedure at type_context_old,
which performs matching modulo CIC reduction rules and has support for higher-order patterns.
By default, all simp lemmas derived from the local context will have the [ac_match] attribute.
The simplifier will have an option for disabling all AC matching support.

This module also has support for symmetric operators (see type class `is_symm_op`).
The `is_symm_op` type class subsumes `is_commutative` (commutative operators) and `is_symm` (symmetric relations)
type classes.

The AC matching procedure uses backtracking. The state is a tuple (Y, U, U_p, U_u, P, S, S_u) where
  - Y is a set of auxiliary temporary metavariables
  - U is a set of (unsolved) matching constraints: p =?= t, p may contain temporary metavariables, but t doesn't
  - U_p is a set of unsolved and postponed matching constraints. We use this set for storing matching constraints that should
    be solved using using type_context_old full force is_def_eq procedure.
  - U_u is a set of (unsolved) universe matching constraints: p =?= u, p may contain temporary universe metavariables, but u doesn't.
  - P (partial solutions) is a mapping from temporary metavariable to a triple (op, y, t) where
      op is an AC operator, y is in Y, and t is a term and the head of t is not op.
      moreover t does not contain temporary metavariables.
  - S (solutions) is a mapping from temporary metavariable to a term t. t does not contain
    temporary metavariables.
  - S_u (universe solutions) is a mapping from temporary universe metavariable to an universe term u.
    u does not contain temporary metavariables.

We implement the mappings P and S using arrays. We use a similar approach in type_context_old.
We implement U as a queue. The queue is an array and index qidx (queue head).
This module ignores the fact that the universe operator `max` is associative and commutative.
Non trival universe constraints are just postponed like in the type_context_old class.

This module does not use AC matching for implicit arguments. Matching constraints for implicit arguments
are stored at U_p. When U is empty, we just use full force type_context_old is_def_eq to process the constraints
at U_p. Note that the type_context_old must have access to S and S_u.
We address this requirement by using the type_context_old m_eassignment and m_uassignment
to implement S and S_u. Similarly, we use m_postponed to implement U_u.

Here are the rules for processing U elements

Remark: we use + and * to denote arbitrary AC operators

- ?x =?= s, S[?x] := s'
  ==>
  remove ?x =?= s from U IF is_def_eq(s, s')
  failure (i.e., backtrack) otherwise

  The is_def_eq is performed using the same "force" used in AC matching.
  Remark: s and s' do not contain temporary universe metavariables.
  Remark: S[?x] := s' denotes that s' is assigned to temporary metavariable ?x.

- ?x =?= s, P[?x] := (op, ?y, t)
  ==>
  failure IF head(s) is not op

- ?x =?= s_1 + ... + s_n,  P[?x] := (+, ?y, s')
  ==>
  replace with ?y =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n
  IF is_def_eq(s_k, s') for some s_k.
  failure otherwise

- ?x =?= s
  ==>
  remove ?x =?= s, and add S[?x] := s
  If ?x not in P nor S.

- t =?= s, t does not contain temporary metavariables
  ==>
  remove t =?= s IF is_def_eq(t, s)
  failure otherwise

- (f ...) =?= (g ...) and f different from g
  ==>
  replace with (f ...) =?= unfold_of (g ...) If unfold step is successful
  failure otherwise

- (f a_1 ... a_n) =?= (f b_1 ... b_n)
  ==>
  replace constaints with a_1 =?= b_1 ... a_n =?= b_n
  where a_i =?= b_i goes to U if explicit argument and to U_p otherwise

- (a_1 op a_2) =?= (b_1 op b_2) where op is not AC, but there is an instance of (is_sym_op _ _ op)
  ==>
  split
  1- replace with a_1 =?= b_1 and a_2 =?= b_2
  2- replace with a_1 =?= b_2 and a_2 =?= b_1

  We say this is the SYMM_OP_SPLIT rule, and it always creates two cases.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, S[?x] := s, s is not a +-application
  ==>
  replace with t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n IF m <= n and is_def_eq(s, s_k)
  failure otherwise

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, S[?x] := s'_1 + ... + s'_n'
  ==>
  replace with t_2 + ... + t_m =?= s''_1 + ... + s''_n'' IF m - 1 <= n - n' and {s''_1, ..., s''_n'', s'_1, ... s'_n'} is definitionally equal to {s_1, ..., s_n}
  failure otherwise

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, P[?x] := (*, ?y, s) where * is not +.
  ==>
  If m <= n, split for each s_k s.t. s_k is of the form (s * s'_2' * ... * s'_n')
  replace with ?y =?= s'_2 * ...* s'_n' and t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n
  failure otherwise

  Remark: we don't need to perform a case split if (s_1 + ... + s_n) contains at most one term that is a *-application.

  We say this is an AC_P_SPLIT rule.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, P[?x] := (+, ?y, s)
  ==>
  replace with ?y + t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n IF m < n and is_def_eq(s, s_k) for some s_k
  failure otherwise.

- ?x + t_2 + ... + t_m =?= s_1 + ... + s_n, ?x is not in S nor P
  ==>
  For each s_k, we replace the constraint with
  - t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n and S[?x] := s_k IF m <= n
  - ?y + t_2 + .. + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n and P[?x] := (+, ?y, s_k) IF m < n where ?y is a fresh auxiliary temporary metavariable

  Remark: If m = n, then there are 2*n possible cases. If m < n, there are n cases.

  We say this is the AC_ASSIGN_SPLIT rule, and is the most expensive one.

- (g ...) + t_2 + ... + t_m =?= s_1 + ... + s_n,  `g` is not +
  ==>
  For each s_k with is a g-application
  - replace with (g ...) =?= s_k, t_2 + ... + t_m =?= s_1 + ... + s_{k-1} + s_{k+1} + ... + s_n

  The number of cases is the number of g-applications at s_1 + ... + s_n

  We say this is the AC_APP_SPLIT rule

- (let x := t in p) =?= s
  ==>
  replace with p[x/t] =?= s

- p =?= (let x := t in s)
  ==>
  replace with p =?= s[x/t]

After we don't have more elements in U to process using the rules above, we process U_p and U_u constraints using type_context_old is_def_eq with full force.

Remark: in the rules above we do not have support for Pi and lambda-terms containing temporary metavariables.
We will treat macros and (A -> B) as applications. Here (A -> B) denotes a non dependent Pi-term.

*/




// ========== aux_recursors.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Mark \c r as an auxiliary recursor automatically created by the system.
    We use it to mark recursors such as brec_on, rec_on, induction_on, etc. */
environment add_aux_recursor(environment const & env, name const & r);
environment add_no_confusion(environment const & env, name const & r);
/** \brief Return true iff \c n is the name of an auxiliary recursor.
    \see add_aux_recursor */
bool is_aux_recursor(environment const & env, name const & n);
bool is_no_confusion(environment const & env, name const & n);

void initialize_aux_recursors();
void finalize_aux_recursors();
}




// ========== aux_recursors.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/aux_recursors.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/module.h"

namespace lean {
struct aux_recursor_ext : public environment_extension {
    name_set m_aux_recursor_set;
    name_set m_no_confusion_set;
};

struct aux_recursor_ext_reg {
    unsigned m_ext_id;
    aux_recursor_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<aux_recursor_ext>()); }
};

static aux_recursor_ext_reg * g_ext = nullptr;
static aux_recursor_ext const & get_extension(environment const & env) {
    return static_cast<aux_recursor_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, aux_recursor_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<aux_recursor_ext>(ext));
}

struct auxrec_modification : public modification {
    LEAN_MODIFICATION("auxrec")

    name m_decl;

    auxrec_modification() {}
    auxrec_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        aux_recursor_ext ext = get_extension(env);
        ext.m_aux_recursor_set.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<auxrec_modification>(read_name(d));
    }
};

struct no_conf_modification : public modification {
    LEAN_MODIFICATION("no_conf")

    name m_decl;

    no_conf_modification() {}
    no_conf_modification(name const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        aux_recursor_ext ext = get_extension(env);
        ext.m_no_confusion_set.insert(m_decl);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<no_conf_modification>(read_name(d));
    }
};

environment add_aux_recursor(environment const & env, name const & r) {
    return module::add_and_perform(env, std::make_shared<auxrec_modification>(r));
}

environment add_no_confusion(environment const & env, name const & r) {
    return module::add_and_perform(env, std::make_shared<no_conf_modification>(r));
}

bool is_aux_recursor(environment const & env, name const & r) {
    return get_extension(env).m_aux_recursor_set.contains(r);
}

bool is_no_confusion(environment const & env, name const & r) {
    return get_extension(env).m_no_confusion_set.contains(r);
}

void initialize_aux_recursors() {
    g_ext              = new aux_recursor_ext_reg();
    auxrec_modification::init();
    no_conf_modification::init();
}

void finalize_aux_recursors() {
    auxrec_modification::finalize();
    no_conf_modification::finalize();
    delete g_ext;
}
}




// ========== aliases.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "kernel/environment.h"

namespace lean {
/** \brief Add the alias \c a for \c e. */
environment add_expr_alias(environment const & env, name const & a, name const & e, bool overwrite = false);
/**
   \brief Add alias \c a for \c e, and also add it to all parent scopes
   until in a namespace scope.
*/
environment add_expr_alias_rec(environment const & env, name const & a, name const & e, bool overwrite = false);

/** \brief If \c t is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_expr_aliased(environment const & env, name const & t);

/** \brief Return expressions associated with the given alias. */
list<name> get_expr_aliases(environment const & env, name const & n);

/** \brief Remove aliases for `n`, the effect affects the current scope only. */
environment erase_expr_aliases(environment const & env, name const & n);

/**
    \brief Add the alias \c a for level \c l. An error is generated if the new alias shadows
    existing aliases and/or declarations. We don't have "choice" construct for universe
    levels.
*/
environment add_level_alias(environment const & env, name const & a, name const & l);

/** \brief If \c l is aliased in \c env, then return its name. Otherwise, return none. */
optional<name> is_level_aliased(environment const & env, name const & l);

/** \brief Return the level associated with the given alias. */
optional<name> get_level_alias(environment const & env, name const & n);

/**
   \brief Create an alias for each declaration named <tt>prefix.rest</tt>.
   The alias for <tt>prefix.rest</tt> is <tt>new_prefix.rest</tt>.

   \remark \c new_prefix may be the anonymous name.
*/
environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions = 0, name const * exceptions = nullptr, bool overwrite = false);
inline environment overwrite_aliases(environment const & env, name const & prefix, name const & new_prefix) {
    return add_aliases(env, prefix, new_prefix, 0, nullptr, true);
}

bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions);

void for_each_expr_alias(environment const & env, std::function<void(name const &, list<name> const &)> const & fn);

/* When we declare a definition in a section, we create an alias for it that fixes the parameters in
   universe parameters. */
environment add_local_ref(environment const & env, name const & a, expr const & ref);

optional<expr> get_local_ref(environment const & env, name const & n);

void initialize_aliases();
void finalize_aliases();
}




// ========== aliases.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "util/rb_map.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/expr_lt.h"
#include "library/aliases.h"
#include "library/placeholder.h"
#include "library/scoped_ext.h"
#include "library/protected.h"

namespace lean {
struct aliases_ext;
static aliases_ext const & get_extension(environment const & env);
static environment update(environment const & env, aliases_ext const & ext);

struct aliases_ext : public environment_extension {
    struct state {
        bool                  m_in_section;
        name_map<list<name>>  m_aliases;
        name_map<name>        m_inv_aliases;
        name_map<name>        m_level_aliases;
        name_map<name>        m_inv_level_aliases;
        name_map<expr>        m_local_refs;
        state():m_in_section(false) {}

        void add_local_ref(name const & a, expr const & ref) {
            m_local_refs.insert(a, ref);
        }

        void add_expr_alias(name const & a, name const & e, bool overwrite) {
            if (auto ref = m_local_refs.find(e)) {
                add_local_ref(a, *ref);
            } else {
                auto it = m_aliases.find(a);
                if (it && !overwrite)
                    m_aliases.insert(a, cons(e, filter(*it, [&](name const & t) { return t != e; })));
                else
                    m_aliases.insert(a, to_list(e));
                m_inv_aliases.insert(e, a);
            }
        }
    };

    state       m_state;
    list<state> m_scopes;

    void add_expr_alias(name const & a, name const & e, bool overwrite) {
        m_state.add_expr_alias(a, e, overwrite);
    }

    void add_level_alias(name const & a, name const & l) {
        auto it = m_state.m_level_aliases.find(a);
        if (it)
            throw exception(sstream() << "universe level alias '" << a << "' shadows existing alias");
        m_state.m_level_aliases.insert(a, l);
        m_state.m_inv_level_aliases.insert(l, a);
    }

    list<state> add_expr_alias_rec_core(list<state> const & scopes, name const & a, name const & e, bool overwrite) {
        if (empty(scopes)) {
            return scopes;
        } else {
            state s = head(scopes);
            s.add_expr_alias(a, e, overwrite);
            if (s.m_in_section) {
                return cons(s, add_expr_alias_rec_core(tail(scopes), a, e, overwrite));
            } else {
                return cons(s, tail(scopes));
            }
        }
    }

    void add_expr_alias_rec(name const & a, name const & e, bool overwrite = false) {
        if (m_state.m_in_section) {
            m_scopes = add_expr_alias_rec_core(m_scopes, a, e, overwrite);
        }
        add_expr_alias(a, e, overwrite);
    }

    void add_local_ref(name const & a, expr const & ref) {
        m_state.add_local_ref(a, ref);
    }

    void push(bool in_section) {
        m_scopes = cons(m_state, m_scopes);
        m_state.m_in_section = in_section;
    }

    void pop() {
        m_state  = head(m_scopes);
        m_scopes = tail(m_scopes);
    }

    void for_each_expr_alias(std::function<void(name const &, list<name> const &)> const & fn) {
        m_state.m_aliases.for_each(fn);
    }

    static environment push_scope(environment const & env, io_state const &, scope_kind k) {
        aliases_ext ext = get_extension(env);
        ext.push(k != scope_kind::Namespace);
        environment new_env = update(env, ext);
        return new_env;
    }

    static environment pop_scope(environment const & env, io_state const &, scope_kind) {
        aliases_ext ext = get_extension(env);
        ext.pop();
        return update(env, ext);
    }
};

struct aliases_ext_reg {
    unsigned m_ext_id;
    aliases_ext_reg() {
        register_scoped_ext(aliases_ext::push_scope, aliases_ext::pop_scope);
        m_ext_id = environment::register_extension(std::make_shared<aliases_ext>());
    }
};
static aliases_ext_reg * g_ext = nullptr;
static aliases_ext const & get_extension(environment const & env) {
    return static_cast<aliases_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, aliases_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<aliases_ext>(ext));
}

environment add_expr_alias(environment const & env, name const & a, name const & e, bool overwrite) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias(a, e, overwrite);
    return update(env, ext);
}

environment add_expr_alias_rec(environment const & env, name const & a, name const & e, bool overwrite) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias_rec(a, e, overwrite);
    return update(env, ext);
}

optional<name> is_expr_aliased(environment const & env, name const & t) {
    auto it = get_extension(env).m_state.m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

list<name> get_expr_aliases(environment const & env, name const & n) {
    return ptr_to_list(get_extension(env).m_state.m_aliases.find(n));
}

environment erase_expr_aliases(environment const & env, name const & n) {
    aliases_ext ext = get_extension(env);
    ext.m_state.m_aliases.erase(n);
    return update(env, ext);
}

environment add_local_ref(environment const & env, name const & a, expr const & ref) {
    aliases_ext ext = get_extension(env);
    ext.add_local_ref(a, ref);
    return update(env, ext);
}

optional<expr> get_local_ref(environment const & env, name const & n) {
    aliases_ext const & ext = get_extension(env);
    if (auto r = ext.m_state.m_local_refs.find(n))
        return some_expr(*r);
    else
        return none_expr();
}

environment add_level_alias(environment const & env, name const & a, name const & l) {
    aliases_ext ext = get_extension(env);
    ext.add_level_alias(a, l);
    return update(env, ext);
}

optional<name> is_level_aliased(environment const & env, name const & l) {
    auto it = get_extension(env).m_state.m_inv_level_aliases.find(l);
    return it ? optional<name>(*it) : optional<name>();
}

optional<name> get_level_alias(environment const & env, name const & n) {
    auto it = get_extension(env).m_state.m_level_aliases.find(n);
    return it ? optional<name>(*it) : optional<name>();
}

// Return true iff \c n is (prefix + ex) for some ex in exceptions
bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions) {
    return std::any_of(exceptions, exceptions + num_exceptions, [&](name const & ex) { return (prefix + ex) == n; });
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions, name const * exceptions, bool overwrite) {
    aliases_ext ext = get_extension(env);
    env.for_each_declaration([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name()) && !is_exception(d.get_name(), prefix, num_exceptions, exceptions)) {
                name a        = d.get_name().replace_prefix(prefix, new_prefix);
                if (!(is_protected(env, d.get_name()) && a.is_atomic()) &&
                    !(a.is_anonymous()))
                    ext.add_expr_alias(a, d.get_name(), overwrite);
            }
        });
    return update(env, ext);
}

void for_each_expr_alias(environment const & env, std::function<void(name const &, list<name> const &)> const & fn) {
    aliases_ext ext = get_extension(env);
    ext.for_each_expr_alias(fn);
}

void initialize_aliases() {
    g_ext     = new aliases_ext_reg();
}

void finalize_aliases() {
    delete g_ext;
}
}




// ========== relation_manager.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
struct relation_info {
    unsigned m_arity;
    unsigned m_lhs_pos;
    unsigned m_rhs_pos;
public:
    relation_info() {}
    relation_info(unsigned arity, unsigned lhs, unsigned rhs):
        m_arity(arity), m_lhs_pos(lhs), m_rhs_pos(rhs) {
        lean_assert(m_lhs_pos < m_arity);
        lean_assert(m_rhs_pos < m_arity);
    }
    unsigned get_arity() const { return m_arity; }
    unsigned get_lhs_pos() const { return m_lhs_pos; }
    unsigned get_rhs_pos() const { return m_rhs_pos; }
};

/** \brief Return true if \c rop is a registered equivalence relation in the given manager */
bool is_equivalence(environment const & env, name const & rop);

/** \brief If \c rop is a registered relation, then return a non-null pointer to the associated information
    Lean assumes that the arguments of the binary relation are the last two explicit arguments.
    Everything else is assumed to be a parameter.
*/
relation_info const * get_relation_info(environment const & env, name const & rop);
inline bool is_relation(environment const & env, name const & rop) { return get_relation_info(env, rop) != nullptr; }

typedef std::function<optional<relation_info>(name const &)>  relation_info_getter;
relation_info_getter mk_relation_info_getter(environment const & env);

/** \brief Return true iff \c e is of the form (lhs rop rhs) where rop is a registered relation. */
bool is_relation(environment const & env, expr const & e, name & rop, expr & lhs, expr & rhs);
typedef std::function<bool(expr const &, name &, expr &, expr &)> is_relation_pred; // NOLINT
/** \brief Construct an \c is_relation predicate for the given environment. */
is_relation_pred mk_is_relation_pred(environment const & env);

/** \brief Declare a new binary relation named \c n */
environment add_relation(environment const & env, name const & n, bool persistent);

/** \brief Declare subst/refl/symm/trans lemmas for a binary relation,
 * it also declares the relation if it has not been declared yet */
environment add_subst(environment const & env, name const & n, bool persistent);
environment add_refl(environment const & env, name const & n, bool persistent);
environment add_symm(environment const & env, name const & n, bool persistent);
environment add_trans(environment const & env, name const & n, bool persistent);

struct relation_lemma_info {
    name     m_name;
    unsigned m_num_univs;
    unsigned m_num_args;
    relation_lemma_info() {}
    relation_lemma_info(name const & n, unsigned nunivs, unsigned nargs):m_name(n), m_num_univs(nunivs), m_num_args(nargs) {}
};

typedef relation_lemma_info refl_info;
typedef relation_lemma_info symm_info;
typedef relation_lemma_info subst_info;

struct trans_info : public relation_lemma_info {
    name  m_res_relation;
    trans_info() {}
    trans_info(name const & n, unsigned nunivs, unsigned nargs, name const & rel):
        relation_lemma_info(n, nunivs, nargs), m_res_relation(rel) {}
};

optional<subst_info> get_subst_extra_info(environment const & env, name const & op);
optional<refl_info> get_refl_extra_info(environment const & env, name const & op);
optional<symm_info> get_symm_extra_info(environment const & env, name const & op);
optional<trans_info> get_trans_extra_info(environment const & env, name const & op1, name const & op2);
optional<name> get_refl_info(environment const & env, name const & op);
optional<name> get_symm_info(environment const & env, name const & op);
optional<name> get_trans_info(environment const & env, name const & op);

typedef std::function<optional<refl_info>(name const &)>  refl_info_getter;
typedef std::function<optional<trans_info>(name const &, name const &)> trans_info_getter;
typedef std::function<optional<symm_info>(name const &)>  symm_info_getter;

refl_info_getter mk_refl_info_getter(environment const & env);
trans_info_getter mk_trans_info_getter(environment const & env);
symm_info_getter mk_symm_info_getter(environment const & env);

bool is_subst_relation(environment const & env, name const & op);
inline bool is_trans_relation(environment const & env, name const & op) { return static_cast<bool>(get_trans_info(env, op)); }
inline bool is_symm_relation(environment const & env, name const & op) { return static_cast<bool>(get_symm_info(env, op)); }
inline bool is_refl_relation(environment const & env, name const & op) { return static_cast<bool>(get_refl_info(env, op)); }

void initialize_relation_manager();
void finalize_relation_manager();
}




// ========== relation_manager.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/optional.h"
#include "util/name.h"
#include "util/rb_map.h"
#include "util/sstream.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/relation_manager.h"
#include "library/attribute_manager.h"

namespace lean {
// Check whether e is of the form (f ...) where f is a constant. If it is return f.
static name const & get_fn_const(expr const & e, char const * msg) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        throw exception(msg);
    return const_name(fn);
}

static pair<expr, unsigned> extract_arg_types_core(environment const & env, name const & f, buffer<expr> & arg_types) {
    declaration d = env.get(f);
    expr f_type = d.get_type();
    while (is_pi(f_type)) {
        arg_types.push_back(binding_domain(f_type));
        f_type = binding_body(f_type);
    }
    return mk_pair(f_type, d.get_num_univ_params());
}

enum class op_kind { Relation, Subst, Trans, Refl, Symm };

struct rel_entry {
    op_kind m_kind;
    name    m_name;
    rel_entry() {}
    rel_entry(op_kind k, name const & n):m_kind(k), m_name(n) {}
};

struct rel_state {
    typedef name_map<refl_info> refl_table;
    typedef name_map<subst_info> subst_table;
    typedef name_map<symm_info> symm_table;
    typedef rb_map<name_pair, trans_info, name_pair_quick_cmp> trans_table;
    typedef name_map<relation_info> rop_table;
    trans_table    m_trans_table;
    refl_table     m_refl_table;
    subst_table    m_subst_table;
    symm_table     m_symm_table;
    rop_table      m_rop_table;
    rel_state() {}

    bool is_equivalence(name const & rop) const {
        return m_trans_table.contains(mk_pair(rop, rop)) && m_refl_table.contains(rop) && m_symm_table.contains(rop);
    }

    static void throw_invalid_relation(name const & rop) {
        throw exception(sstream() << "invalid binary relation declaration, relation '" << rop
                        << "' must have two explicit parameters");
    }

    void register_rop(environment const & env, name const & rop) {
        if (m_rop_table.contains(rop))
            return;
        declaration const & d = env.get(rop);
        optional<unsigned> lhs_pos;
        optional<unsigned> rhs_pos;
        unsigned i = 0;
        expr type = d.get_type();
        while (is_pi(type)) {
            if (is_explicit(binding_info(type))) {
                if (!lhs_pos) {
                    lhs_pos = i;
                } else if (!rhs_pos) {
                    rhs_pos = i;
                } else {
                    lhs_pos = rhs_pos;
                    rhs_pos = i;
                }
            }
            type = binding_body(type);
            i++;
        }
        if (lhs_pos && rhs_pos) {
            m_rop_table.insert(rop, relation_info(i, *lhs_pos, *rhs_pos));
        } else {
            throw_invalid_relation(rop);
        }
    }

    void add_subst(environment const & env, name const & subst) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, subst, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 2)
            throw exception("invalid substitution theorem, it must have at least 2 arguments");
        name const & rop = get_fn_const(arg_types[nargs-2], "invalid substitution theorem, penultimate argument must be an operator application");
        m_subst_table.insert(rop, subst_info(subst, nunivs, nargs));
    }

    void add_refl(environment const & env, name const & refl) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, refl, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 1)
            throw exception("invalid reflexivity rule, it must have at least 1 argument");
        name const & rop = get_fn_const(r_type, "invalid reflexivity rule, result type must be an operator application");
        register_rop(env, rop);
        m_refl_table.insert(rop, refl_info(refl, nunivs, nargs));
    }

    void add_trans(environment const & env, name const & trans) {
        buffer<expr> arg_types;
        auto p = extract_arg_types_core(env, trans, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 5)
            throw exception("invalid transitivity rule, it must have at least 5 arguments");
        name const & rop = get_fn_const(r_type, "invalid transitivity rule, result type must be an operator application");
        name const & op1 = get_fn_const(arg_types[nargs-2], "invalid transitivity rule, penultimate argument must be an operator application");
        name const & op2 = get_fn_const(arg_types[nargs-1], "invalid transitivity rule, last argument must be an operator application");
        register_rop(env, rop);
        m_trans_table.insert(name_pair(op1, op2), trans_info(trans, nunivs, nargs, rop));
    }

    void add_symm(environment const & env, name const & symm) {
        buffer<expr> arg_types;
        auto p          = extract_arg_types_core(env, symm, arg_types);
        expr r_type     = p.first;
        unsigned nunivs = p.second;
        unsigned nargs  = arg_types.size();
        if (nargs < 1)
            throw exception("invalid symmetry rule, it must have at least 1 argument");
        name const & rop = get_fn_const(r_type, "invalid symmetry rule, result type must be an operator application");
        register_rop(env, rop);
        m_symm_table.insert(rop, symm_info(symm, nunivs, nargs));
    }
};

struct rel_config {
    typedef rel_state state;
    typedef rel_entry entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case op_kind::Relation: s.register_rop(env, e.m_name); break;
        case op_kind::Refl:     s.add_refl(env, e.m_name); break;
        case op_kind::Subst:    s.add_subst(env, e.m_name); break;
        case op_kind::Trans:    s.add_trans(env, e.m_name); break;
        case op_kind::Symm:     s.add_symm(env, e.m_name); break;
        }
    }
    static const char * get_serialization_key() { return "REL"; }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind) << e.m_name;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        char cmd;
        d >> cmd >> e.m_name;
        e.m_kind = static_cast<op_kind>(cmd);
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const &) {
        return optional<unsigned>();
    }
};

template class scoped_ext<rel_config>;
typedef scoped_ext<rel_config> rel_ext;

environment add_relation(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Relation, n), persistent);
}

environment add_subst(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Subst, n), persistent);
}

environment add_refl(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Refl, n), persistent);
}

environment add_symm(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Symm, n), persistent);
}

environment add_trans(environment const & env, name const & n, bool persistent) {
    return rel_ext::add_entry(env, get_dummy_ios(), rel_entry(op_kind::Trans, n), persistent);
}

static optional<relation_lemma_info> get_info(name_map<relation_lemma_info> const & table, name const & op) {
    if (auto it = table.find(op)) {
        return optional<relation_lemma_info>(*it);
    } else {
        return optional<relation_lemma_info>();
    }
}

optional<refl_info> get_refl_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_refl_table, op);
}
optional<subst_info> get_subst_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_subst_table, op);
}
optional<symm_info> get_symm_extra_info(environment const & env, name const & op) {
    return get_info(rel_ext::get_state(env).m_symm_table, op);
}

optional<trans_info> get_trans_extra_info(environment const & env, name const & op1, name const & op2) {
    if (auto it = rel_ext::get_state(env).m_trans_table.find(mk_pair(op1, op2))) {
        return optional<trans_info>(*it);
    } else {
        return optional<trans_info>();
    }
}

bool is_subst_relation(environment const & env, name const & op) {
    return rel_ext::get_state(env).m_subst_table.contains(op);
}

optional<name> get_refl_info(environment const & env, name const & op) {
    if (auto it = get_refl_extra_info(env, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

optional<name> get_symm_info(environment const & env, name const & op) {
    if (auto it = get_symm_extra_info(env, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

optional<name> get_trans_info(environment const & env, name const & op) {
    if (auto it = get_trans_extra_info(env, op, op))
        return optional<name>(it->m_name);
    else
        return optional<name>();
}

refl_info_getter mk_refl_info_getter(environment const & env) {
    auto t = rel_ext::get_state(env).m_refl_table;
    return [=](name const & n) { return get_info(t, n); }; // NOLINT
}

trans_info_getter mk_trans_info_getter(environment const & env) {
    auto t = rel_ext::get_state(env).m_trans_table;
    return [=](name const & op1, name const & op2) {  // NOLINT
        if (auto it = t.find(mk_pair(op1, op2))) {
            return optional<trans_info>(*it);
        } else {
            return optional<trans_info>();
        }
    };
}

symm_info_getter mk_symm_info_getter(environment const & env) {
    auto t = rel_ext::get_state(env).m_symm_table;
    return [=](name const & n) { return get_info(t, n); }; // NOLINT
}

bool is_equivalence(environment const & env, name const & rop) {
    return rel_ext::get_state(env).is_equivalence(rop);
}

relation_info const * get_relation_info(environment const & env, name const & rop) {
    return rel_ext::get_state(env).m_rop_table.find(rop);
}

relation_info_getter mk_relation_info_getter(environment const & env) {
    auto table = rel_ext::get_state(env).m_rop_table;
    return [=](name const & rop) { // NOLINT
        if (auto r = table.find(rop))
            return optional<relation_info>(*r);
        else
            return optional<relation_info>();
    };
}

bool is_relation(name_map<relation_info> const & table, expr const & e, name & rop, expr & lhs, expr & rhs) {
    if (!is_app(e))
        return false;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return false;
    auto r = table.find(const_name(f));
    if (!r)
        return false;
    buffer<expr> args;
    get_app_args(e, args);
    if (r->get_arity() != args.size())
        return false;
    rop = const_name(f);
    lhs = args[r->get_lhs_pos()];
    rhs = args[r->get_rhs_pos()];
    return true;
}

bool is_relation(environment const & env, expr const & e, name & rop, expr & lhs, expr & rhs) {
    return is_relation(rel_ext::get_state(env).m_rop_table, e, rop, lhs, rhs);
}

is_relation_pred mk_is_relation_pred(environment const & env) {
    name_map<relation_info> table = rel_ext::get_state(env).m_rop_table;
    return [=](expr const & e, name & rop, expr & lhs, expr & rhs) { // NOLINT
        return is_relation(table, e, rop, lhs, rhs);
    };
}

void initialize_relation_manager() {
    rel_ext::initialize();
    register_system_attribute(basic_attribute("refl", "reflexive relation",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_refl(env, d, persistent);
                                              }));

    register_system_attribute(basic_attribute("symm", "symmetric relation",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_symm(env, d, persistent);
                                              }));

    register_system_attribute(basic_attribute("trans", "transitive relation",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_trans(env, d, persistent);
                                              }));

    register_system_attribute(basic_attribute("subst", "substitution",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_subst(env, d, persistent);
                                              }));
}

void finalize_relation_manager() {
    rel_ext::finalize();
}
}




// ========== phash_map.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/bit_tricks.h"
#include "util/name.h"
#include "library/phashtable.h"

namespace lean {
template<typename Key, typename Value>
struct key_value_pair {
    Key   m_key;
    Value m_value;
    key_value_pair(Key const & k):m_key(k) {}
    key_value_pair(Key const & k, Value const & v):
        m_key(k), m_value(v) {}
};

template<typename Key, typename Value>
class default_map_entry : public default_hash_entry<key_value_pair<Key, Value>> {
    typedef default_hash_entry<key_value_pair<Key, Value>> parent;

    explicit default_map_entry(bool b):parent(b) {}
public:
    typedef Key                        key;
    typedef Value                      value;
    typedef key_value_pair<Key, Value> key_value;
    default_map_entry() {}
    default_map_entry(key_value const & d, unsigned h):parent(d, h) {}
    static default_map_entry mk_deleted() { return default_map_entry(false); }
    default_map_entry & operator=(default_map_entry const & src) {
        parent::operator=(src);
        return *this;
    }
};

template<typename Entry, typename HashProc, typename EqProc, bool ThreadSafe>
class phashtable2map {
protected:
    typedef Entry    entry;
    typedef typename Entry::key      key;
    typedef typename Entry::value    value;
    typedef typename Entry::key_value key_value;

    struct entry_hash_proc : private HashProc {
        entry_hash_proc(HashProc const & p):HashProc(p) {}

        unsigned operator()(key_value const & d) const {
            return HashProc::operator()(d.m_key);
        }
    };

    struct entry_eq_proc : private EqProc {
        entry_eq_proc(EqProc const & p):EqProc(p) {}

        bool operator()(key_value const & d1, key_value const & d2) const {
            return EqProc::operator()(d1.m_key, d2.m_key);
        }
    };

    typedef phashtable_core<entry, entry_hash_proc, entry_eq_proc, ThreadSafe> table;

    table m_table;

public:
    phashtable2map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        m_table(LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY, entry_hash_proc(h), entry_eq_proc(e)) {
    }

    void clear() {
        m_table.clear();
    }

    unsigned size() const {
        return m_table.size();
    }

    unsigned capacity() const {
        return m_table.capacity();
    }

    void insert(key const & k, value const & v) {
        m_table.insert(key_value(k, v));
    }

    optional<value> find(key const & k) const {
        if (auto e = m_table.find(key_value(k)))
            return optional<value>(e->m_value);
        else
            return optional<value>();
    }

    bool contains(key const & k) const {
        return m_table.contains(key_value(k));
    }

    void erase(key const & k) {
        m_table.erase(key_value(k));
    }

    template<typename F>
    void for_each(F && f) const {
        m_table.for_each([&](key_value const & e) {
                f(e.m_key, e.m_value);
            });
    }
};


template<typename Key, typename Value, typename HashProc, typename EqProc, bool ThreadSafe>
class phash_map : public phashtable2map<default_map_entry<Key, Value>, HashProc, EqProc, ThreadSafe> {
public:
    phash_map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        phashtable2map<default_map_entry<Key, Value>, HashProc, EqProc, ThreadSafe>(h, e) {
    }
};

template<typename T>
using name_hash_map = phash_map<name, T, name_hash, name_eq, true>;
}




// ========== io_state.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/output_channel.h"
#include "util/sexpr/options.h"
#include "util/exception_with_pos.h"
#include "kernel/expr.h"
#include "kernel/scope_pos_info_provider.h"

namespace lean {
/**
   \brief State provided to internal lean procedures that need to:
   1- Access user defined options
   2- Produce verbosity messages
   3- Output results
   4- Produce formatted output
*/
class io_state {
    options                         m_options;
    formatter_factory               m_formatter_factory;
    std::shared_ptr<output_channel> m_regular_channel;
    std::shared_ptr<output_channel> m_diagnostic_channel;
public:
    io_state();
    io_state(formatter_factory const & fmtf);
    io_state(options const & opts, formatter_factory const & fmtf);
    io_state(io_state const & ios, std::shared_ptr<output_channel> const & r, std::shared_ptr<output_channel> const & d);
    io_state(io_state const & ios, options const & o);
    ~io_state();

    options const & get_options() const { return m_options; }
    formatter_factory const & get_formatter_factory() const { return m_formatter_factory; }
    std::shared_ptr<output_channel> const & get_regular_channel_ptr() const { return m_regular_channel; }
    std::shared_ptr<output_channel> const & get_diagnostic_channel_ptr() const { return m_diagnostic_channel; }
    output_channel & get_regular_channel() const { return *m_regular_channel; }
    output_channel & get_diagnostic_channel() const { return *m_diagnostic_channel; }
    std::ostream & get_regular_stream() const { return m_regular_channel->get_stream(); }
    std::ostream & get_diagnostic_stream() const { return m_diagnostic_channel->get_stream(); }

    void set_regular_channel(std::shared_ptr<output_channel> const & out);
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out);
    void set_options(options const & opts);
    void set_formatter_factory(formatter_factory const & f);
    template<typename T> void set_option(name const & n, T const & v) {
        set_options(get_options().update(n, v));
    }
};

/** \brief Return a dummy io_state that is meant to be used in contexts that require an io_state, but it is not really used */
io_state const & get_dummy_ios();

/** \brief Return reference to thread local io_state object. */
io_state const & get_global_ios();

/** \brief Formatted exceptions where the format object must be eagerly constructed.
    This is slightly different from ext_exception where the format object is built on demand. */
class formatted_exception : public exception_with_pos {
protected:
    optional<pos_info>    m_pos;
    format                m_fmt;
    optional<std::string> m_what_buffer;
public:
    explicit formatted_exception(format const & fmt):m_fmt(fmt) {}
    formatted_exception(optional<pos_info> const & p, format const & fmt):m_pos(p), m_fmt(fmt) {}
    formatted_exception(optional<expr> const & e, format const & fmt):formatted_exception(get_pos_info(e), fmt) {}
    formatted_exception(expr const & e, format const & fmt):formatted_exception(some(e), fmt) {}
    virtual char const * what() const noexcept override;
    virtual throwable * clone() const override { return new formatted_exception(m_pos, m_fmt); }
    virtual void rethrow() const override { throw *this; }
    virtual optional<pos_info> get_pos() const override { return m_pos; }
    virtual format pp() const { return m_fmt; }
};

struct scope_global_ios {
    io_state * m_old_ios;
public:
    scope_global_ios(io_state const & ios);
    ~scope_global_ios();
};

options const & get_options_from_ios(io_state const & ios);

void initialize_io_state();
void finalize_io_state();
}




// ========== io_state.cpp ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/kernel_exception.h"
#include "library/print.h"
#include "library/io_state.h"

namespace lean {
static io_state * g_dummy_ios = nullptr;

io_state const & get_dummy_ios() {
    return *g_dummy_ios;
}

io_state::io_state():io_state(mk_print_formatter_factory()) {}

io_state::io_state(formatter_factory const & fmtf):
    m_formatter_factory(fmtf),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}

io_state::io_state(options const & opts, formatter_factory const & fmtf):
    m_options(opts),
    m_formatter_factory(fmtf),
    m_regular_channel(std::make_shared<stdout_channel>()),
    m_diagnostic_channel(std::make_shared<stderr_channel>()) {
}
io_state::io_state(io_state const & ios, std::shared_ptr<output_channel> const & r, std::shared_ptr<output_channel> const & d):
    m_options(ios.m_options),
    m_formatter_factory(ios.m_formatter_factory),
    m_regular_channel(r),
    m_diagnostic_channel(d) {
}
io_state::io_state(io_state const & ios, options const & o):
    m_options(o),
    m_formatter_factory(ios.m_formatter_factory),
    m_regular_channel(ios.m_regular_channel),
    m_diagnostic_channel(ios.m_diagnostic_channel) {
}

io_state::~io_state() {}

void io_state::set_regular_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_regular_channel = out;
}

void io_state::set_diagnostic_channel(std::shared_ptr<output_channel> const & out) {
    if (out)
        m_diagnostic_channel = out;
}

void io_state::set_options(options const & opts) {
    m_options = opts;
}

void io_state::set_formatter_factory(formatter_factory const & f) {
    m_formatter_factory = f;
}

LEAN_THREAD_PTR(io_state, g_ios);

io_state const & get_global_ios() {
    if (g_ios)
        return *g_ios;
    else
        return get_dummy_ios();
}

scope_global_ios::scope_global_ios(io_state const & ios) {
    m_old_ios = g_ios;
    g_ios     = const_cast<io_state*>(&ios);
}

scope_global_ios::~scope_global_ios() {
    g_ios = m_old_ios;
}

char const * formatted_exception::what() const noexcept {
    if (!m_what_buffer) {
        options const & opts = get_global_ios().get_options();
        std::ostringstream out;
        out << mk_pair(m_fmt, opts);
        const_cast<formatted_exception*>(this)->m_what_buffer = out.str();
    }
    return m_what_buffer->c_str();
}

options const & get_options_from_ios(io_state const & ios) {
    return ios.get_options();
}

void initialize_io_state() {
    g_dummy_ios = new io_state(mk_print_formatter_factory());
}

void finalize_io_state() {
    delete g_dummy_ios;
}
}




// ========== local_context.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/subscripted_name_set.h"
#include "kernel/expr.h"
#include "library/local_instances.h"

namespace lean {
class local_decl {
public:
    struct cell {
        /*
          <name> : <type> := <value>

          m_pp_name is used for interacting with the user.
          It may not be not unique.
        */
        name               m_name; /* this one is unique */
        name               m_pp_name;
        expr               m_type;
        optional<expr>     m_value;
        binder_info        m_bi;
        unsigned           m_idx;
        MK_LEAN_RC(); // Declare m_rc counter
        void dealloc();
        cell(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v,
             binder_info const & bi);
    };
private:
    cell * m_ptr;
    friend class local_context;
    friend void initialize_local_context();
    local_decl(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi);
    local_decl(local_decl const & d, expr const & t, optional<expr> const & v);
public:
    local_decl();
    local_decl(local_decl const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    local_decl(local_decl && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~local_decl() { if (m_ptr) m_ptr->dec_ref(); }
    local_decl & operator=(local_decl const & s) { LEAN_COPY_REF(s); }
    local_decl & operator=(local_decl && s) { LEAN_MOVE_REF(s); }

    friend bool is_eqp(local_decl const & a, local_decl const & b) { return a.m_ptr == b.m_ptr; }

    name const & get_name() const { return m_ptr->m_name; }
    name const & get_pp_name() const { return m_ptr->m_pp_name; }
    expr const & get_type() const { return m_ptr->m_type; }
    optional<expr> const & get_value() const { return m_ptr->m_value; }
    binder_info const & get_info() const { return m_ptr->m_bi; }
    expr mk_ref() const;
    unsigned get_idx() const { return m_ptr->m_idx; }
};

bool is_local_decl_ref(expr const & e);

class metavar_context;
class local_context;
bool depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals);
bool depends_on(local_decl const & d, metavar_context const & mctx,  unsigned num, expr const * locals);
bool depends_on(expr const & e, metavar_context const & mctx,  buffer<expr> const & locals);
bool depends_on(local_decl const & d, metavar_context const & mctx, buffer<expr> const & locals);

/* Similar to depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals), but it
   will also visit the value v of local definitions (x : t := v) if x occurs in e (directly or indirectly). */
bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals);
inline bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, expr const & local) {
    return depends_on(e, mctx, lctx, 1, &local);
}

/* Create an unieq local_decl name.
   This is a low-level function. The high-level methods
   at local_context use this function internally. */
name mk_local_decl_name();

class metavar_context;

class local_context {
    typedef unsigned_map<local_decl> idx2local_decl;
    typedef rb_tree<unsigned, unsigned_cmp> unsigned_set;
    unsigned                  m_next_idx;
    name_map<local_decl>      m_name2local_decl;
    subscripted_name_set      m_user_names;
    name_map<unsigned_set>    m_user_name2idxs;
    idx2local_decl            m_idx2local_decl;
    optional<local_instances> m_local_instances;
    friend class type_context_old;

    void insert_user_name(local_decl const &d);
    void erase_user_name(local_decl const &d);

    local_context remove(buffer<expr> const & locals) const;
    expr mk_local_decl(name const & n, name const & ppn, expr const & type,
                       optional<expr> const & value, binder_info const & bi);
    static local_decl update_local_decl(local_decl const & d, expr const & t,
                                        optional<expr> const & v) {
        return local_decl(d, t, v);
    }
public:
    local_context():m_next_idx(0) {}

    void freeze_local_instances(local_instances const & lis);
    void unfreeze_local_instances();
    optional<local_instances> get_frozen_local_instances() const { return m_local_instances; }

    bool empty() const { return m_idx2local_decl.empty(); }

    expr mk_local_decl(expr const & type, binder_info const & bi = binder_info());
    expr mk_local_decl(expr const & type, expr const & value);
    expr mk_local_decl(name const & ppn, expr const & type, binder_info const & bi = binder_info());
    expr mk_local_decl(name const & ppn, expr const & type, expr const & value);

    /* Low-level version of the methods above.

       \pre `n` was created using mk_local_decl_name
       \pre there is no local_decl named `n` in this local_context. */
    expr mk_local_decl(name const & n, name const & ppn, expr const & type, binder_info const & bi = binder_info());
    expr mk_local_decl(name const & n, name const & ppn, expr const & type, expr const & value);

    /** \brief Return the local declarations for the given reference.
        \pre is_local_decl_ref(e) */
    optional<local_decl> find_local_decl(expr const & e) const;
    optional<local_decl> find_local_decl(name const & n) const;

    local_decl const & get_local_decl(expr const & e) const;
    local_decl const & get_local_decl(name const & n) const;

    /** \brief Traverse local declarations based on the order they were created */
    void for_each(std::function<void(local_decl const &)> const & fn) const;
    optional<local_decl> find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT
    optional<local_decl> back_find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT

    /** \brief Return the most recently added local_decl \c d s.t. d.get_pp_name() == n
        \remark This method is used to implement tactics such as 'revert'. */
    optional<local_decl> find_local_decl_from_user_name(name const & n) const;

    optional<local_decl> find_last_local_decl() const;
    local_decl get_last_local_decl() const;

    /** Return a local_decl_ref associated with the given name.

        \pre get_local_decl(n) */
    expr get_local(name const & n) const;

    bool rename_user_name(name const & from, name const & to);

    /** \brief Execute fn for each local declaration created after \c d. */
    void for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const;

    /** \brief Return a non-none iff other local decls depends on \c d. If the result is not none,
        then it is the name of the local decl that depends on d.
        \pre \c d is in this local context. */
    optional<local_decl> has_dependencies(local_decl const & d, metavar_context const & mctx) const;

    /** \brief Return an unused hypothesis "user name" with the given prefix, the suffix is an
        unsigned >= idx. */
    name get_unused_name(name const & prefix, unsigned & idx) const;
    name get_unused_name(name const & suggestion) const;
    /** \brief Return true iff the given name is a hypothesis "user name". */
    bool uses_user_name(name const & n) const;

    /** \brief Remove the given local decl. */
    void clear(local_decl const & d);

    /** \brief Return true iff all locals in this context are in the set \c ls. */
    bool is_subset_of(name_set const & ls) const;
    /** \brief Return true iff all locals in this context are also in \c ctx. */
    bool is_subset_of(local_context const & ctx) const;

    void pop_local_decl();

    /** \brief We say a local context is well-formed iff all local declarations only
        contain local_decl references that were defined before them.

        \remark This method is for debugging purposes. */
    bool well_formed() const;

    /** \brief Return true iff \c e is well-formed with respect to this local context.
        That is, all local_decl references in \c e are defined in this context. */
    bool well_formed(expr const & e) const;

    format pp(formatter const & fmt, std::function<bool(local_decl const &)> const & pred) const; // NOLINT
    format pp(formatter const & fmt) const { return pp(fmt, [](local_decl const &) { return true; }); }

    /** \brief Replaced assigned metavariables with their values.
        This method is a little bit hackish since it reuses the names and ids of
        the existing local_decls. So, it may affect cached information.

        This method is mainly used in the elaborator for reporting errors,
        and for instantiating metavariables created by the elaborator before
        invoking the tactic framework. */
    local_context instantiate_mvars(metavar_context & ctx) const;

    friend bool is_decl_eqp(local_context const & ctx1, local_context const & ctx2) {
        return is_eqp(ctx1.m_name2local_decl, ctx2.m_name2local_decl);
    }

    friend bool equal_locals(local_context const & ctx1, local_context const & ctx2) {
        return is_decl_eqp(ctx1, ctx2) || ctx1.m_name2local_decl.equal_keys(ctx2.m_name2local_decl);
    }

    /** \brief Erase inaccessible annotations from the local context.
        This function is defined in the file library/equations_compiler/util.h.
        It is a little bit hackish (like instantiate_mvars) since it reuses the names
        and ids of existing local_decls. So, it may affect cached information.

        This function is used in the elaborator before invoking the tactic framework. */
    friend local_context erase_inaccessible_annotations(local_context const & lctx);
};

/** \brief Return true iff `e` contains a local_decl_ref that contains a value */
bool contains_let_local_decl(local_context const & lctx, expr const & e);

/** \brief Expand all local_decl_refs (that have values) in `e` */
expr zeta_expand(local_context const & lctx, expr const & e);

void initialize_local_context();
void finalize_local_context();
}




// ========== local_context.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "util/fresh_name.h"
#include "util/list_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "library/pp_options.h"
#include "library/local_context.h"
#include "library/metavar_context.h"
#include "library/trace.h"

namespace lean {
static name *       g_local_prefix;
static expr *       g_dummy_type;
static local_decl * g_dummy_decl;

DEF_THREAD_MEMORY_POOL(get_local_decl_allocator, sizeof(local_decl::cell));

void local_decl::cell::dealloc() {
    this->~cell();
    get_local_decl_allocator().recycle(this);
}
local_decl::cell::cell(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi):
    m_name(n), m_pp_name(pp_n), m_type(t), m_value(v), m_bi(bi), m_idx(idx), m_rc(1) {}

local_decl::local_decl():local_decl(*g_dummy_decl) {}
local_decl::local_decl(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi) {
    m_ptr = new (get_local_decl_allocator().allocate()) cell(idx, n, pp_n, t, v, bi);
}

local_decl::local_decl(local_decl const & d, expr const & t, optional<expr> const & v):
    local_decl(d.m_ptr->m_idx, d.m_ptr->m_name, d.m_ptr->m_pp_name, t, v, d.m_ptr->m_bi) {}

name mk_local_decl_name() {
    return mk_tagged_fresh_name(*g_local_prefix);
}

DEBUG_CODE(
static bool is_local_decl_name(name const & n) {
    return is_tagged_by(n, *g_local_prefix);
})

static expr mk_local_ref(name const & n, name const & pp_n, binder_info const & bi) {
    return mk_local(n, pp_n, *g_dummy_type, bi);
}

bool is_local_decl_ref(expr const & e) {
    return is_local(e) && mlocal_type(e) == *g_dummy_type;
}

expr local_decl::mk_ref() const {
    return mk_local_ref(m_ptr->m_name, m_ptr->m_pp_name, m_ptr->m_bi);
}

struct depends_on_fn {
    metavar_context const & m_mctx;
    local_context const *   m_lctx;
    unsigned                m_num;
    expr const *            m_locals;
    name_set                m_visited_mvars;
    name_set                m_visited_decls;

    depends_on_fn(metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals):
        m_mctx(mctx), m_lctx(&lctx), m_num(num), m_locals(locals) {
        lean_assert(std::all_of(locals, locals+num, is_local_decl_ref));
    }

    depends_on_fn(metavar_context const & mctx, unsigned num, expr const * locals):
        m_mctx(mctx), m_lctx(nullptr), m_num(num), m_locals(locals) {
        lean_assert(std::all_of(locals, locals+num, is_local_decl_ref));
    }

    bool visit_local(expr const & e) {
        lean_assert(is_local_decl_ref(e));
        if (std::any_of(m_locals, m_locals + m_num,
                        [&](expr const & l) { return mlocal_name(e) == mlocal_name(l); }))
            return true;

        if (!m_lctx || m_visited_decls.contains(mlocal_name(e)))
            return false;
        m_visited_decls.insert(mlocal_name(e));
        optional<local_decl> decl = m_lctx->find_local_decl(e);
        if (!decl)
            return false;
        if (visit(decl->get_type()))
            return true;
        if (optional<expr> v = decl->get_value())
            return visit(*v);
        else
            return false;
    }

    bool visit_metavar(expr const & e) {
        lean_assert(is_metavar_decl_ref(e));
        if (m_visited_mvars.contains(mlocal_name(e)))
            return false;
        m_visited_mvars.insert(mlocal_name(e));
        optional<metavar_decl> decl = m_mctx.find_metavar_decl(e);
        if (!decl)
            return false;
        if (visit(decl->get_type()))
            return true;
        if (auto v = m_mctx.get_assignment(e)) {
            if (visit(*v))
                return true;
        }
        return false;
    }

    bool visit(expr const & e) {
        if (!has_local(e) && !has_expr_metavar(e))
            return false;
        bool found = false;
        for_each(e, [&](expr const & e, unsigned) {
                if (found) return false;
                if (!has_local(e) && !has_expr_metavar(e)) return false;
                if (is_local_decl_ref(e) && visit_local(e)) {
                    found = true;
                    return false;
                }
                if (is_metavar_decl_ref(e) && visit_metavar(e)) {
                    found = true;
                    return false;
                }
                return true;
            });
        return found;
    }

    bool operator()(expr const & e) { return visit(e); }
};

bool depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals) {
    return depends_on_fn(mctx, num, locals)(e);
}

bool depends_on(local_decl const & d, metavar_context const & mctx, unsigned num, expr const * locals) {
    depends_on_fn fn(mctx, num, locals);
    if (fn(d.get_type()))
        return true;
    if (auto v = d.get_value()) {
        return fn(*v);
    }
    return false;
}

bool depends_on(expr const & e, metavar_context const & mctx, buffer<expr> const & locals) {
    return depends_on_fn(mctx, locals.size(), locals.data())(e);
}

bool depends_on(local_decl const & d, metavar_context const & mctx, buffer<expr> const & locals) {
    return depends_on(d, mctx, locals.size(), locals.data());
}

bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals) {
    return depends_on_fn(mctx, lctx, num, locals)(e);
}

void local_context::freeze_local_instances(local_instances const & lis) {
    m_local_instances = lis;
    lean_assert(std::all_of(lis.begin(), lis.end(), [&](local_instance const & inst) {
                return m_name2local_decl.contains(mlocal_name(inst.get_local()));
            }));
}

void local_context::unfreeze_local_instances() {
    m_local_instances = optional<local_instances>();
}

void local_context::insert_user_name(local_decl const &d) {
    unsigned_set idxs;
    if (auto existing_idxs = m_user_name2idxs.find(d.get_pp_name())) {
        idxs = *existing_idxs;
    } else {
        m_user_names.insert(d.get_pp_name());
    }
    idxs.insert(d.get_idx());
    m_user_name2idxs.insert(d.get_pp_name(), idxs);
}

void local_context::erase_user_name(local_decl const & d) {
    unsigned_set idxs = *m_user_name2idxs.find(d.get_pp_name());
    idxs.erase(d.get_idx());
    if (idxs.empty()) {
        m_user_name2idxs.erase(d.get_pp_name());
        m_user_names.erase(d.get_pp_name());
    } else {
        m_user_name2idxs.insert(d.get_pp_name(), idxs);
    }
}

expr local_context::mk_local_decl(name const & n, name const & ppn, expr const & type, optional<expr> const & value, binder_info const & bi) {
    lean_assert(is_local_decl_name(n));
    lean_assert(!m_name2local_decl.contains(n));
    unsigned idx = m_next_idx;
    m_next_idx++;
    local_decl l(idx, n, ppn, type, value, bi);
    m_name2local_decl.insert(n, l);
    m_idx2local_decl.insert(idx, l);
    insert_user_name(l);
    return mk_local_ref(n, ppn, bi);
}

expr local_context::mk_local_decl(expr const & type, binder_info const & bi) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, none_expr(), bi);
}

expr local_context::mk_local_decl(expr const & type, expr const & value) {
    name n = mk_local_decl_name();
    return mk_local_decl(n, n, type, some_expr(value), binder_info());
}

expr local_context::mk_local_decl(name const & ppn, expr const & type, binder_info const & bi) {
    return mk_local_decl(mk_local_decl_name(), ppn, type, none_expr(), bi);
}

expr local_context::mk_local_decl(name const & ppn, expr const & type, expr const & value) {
    return mk_local_decl(mk_local_decl_name(), ppn, type, some_expr(value), binder_info());
}

expr local_context::mk_local_decl(name const & n, name const & ppn, expr const & type, binder_info const & bi) {
    return mk_local_decl(n, ppn, type, none_expr(), bi);
}

expr local_context::mk_local_decl(name const & n, name const & ppn, expr const & type, expr const & value) {
    return mk_local_decl(n, ppn, type, some_expr(value), binder_info());
}

optional<local_decl> local_context::find_local_decl(name const & n) const {
    if (auto r = m_name2local_decl.find(n))
        return optional<local_decl>(*r);
    else
        return optional<local_decl>();
}

optional<local_decl> local_context::find_local_decl(expr const & e) const {
    lean_assert(is_local_decl_ref(e));
    return find_local_decl(mlocal_name(e));
}

local_decl const & local_context::get_local_decl(name const & n) const {
    if (local_decl const * r = m_name2local_decl.find(n))
        return *r;
    else
        throw exception(sstream() << "unknown local constant: " << n);
}

local_decl const & local_context::get_local_decl(expr const & e) const {
    lean_assert(is_local_decl_ref(e));
    return get_local_decl(mlocal_name(e));
}


expr local_context::get_local(name const & n) const {
    lean_assert(find_local_decl(n));
    return get_local_decl(n).mk_ref();
}

void local_context::for_each(std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) { fn(d); });
}

optional<local_decl> local_context::find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

optional<local_decl> local_context::back_find_if(std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    return m_idx2local_decl.back_find_if([&](unsigned, local_decl const & d) { return pred(d); });
}

optional<local_decl> local_context::find_local_decl_from_user_name(name const & n) const {
    if (auto idxs = m_user_name2idxs.find(n)) {
        if (auto m = idxs->max()) {
            return optional<local_decl>(*m_idx2local_decl.find(*m));
        }
    }
    return optional<local_decl>();
}

optional<local_decl> local_context::find_last_local_decl() const {
    if (m_idx2local_decl.empty()) return optional<local_decl>();
    return optional<local_decl>(m_idx2local_decl.max());
}

local_decl local_context::get_last_local_decl() const {
    if (m_idx2local_decl.empty()) throw("unknown local constant, context is empty");
    return m_idx2local_decl.max();
}

void local_context::for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const {
    m_idx2local_decl.for_each_greater(d.get_idx(), [&](unsigned, local_decl const & d) { return fn(d); });
}

void local_context::pop_local_decl() {
    lean_assert(!m_idx2local_decl.empty());
    local_decl d = m_idx2local_decl.max();
    m_name2local_decl.erase(d.get_name());
    m_idx2local_decl.erase(d.get_idx());
    erase_user_name(d);
}

bool local_context::rename_user_name(name const & from, name const & to) {
    if (auto d = find_local_decl_from_user_name(from)) {
        erase_user_name(*d);
        local_decl new_d(d->get_idx(), d->get_name(), to, d->get_type(), d->get_value(), d->get_info());
        m_idx2local_decl.insert(d->get_idx(), new_d);
        m_name2local_decl.insert(d->get_name(), new_d);
        insert_user_name(new_d);
        return true;
    } else {
        return false;
    }
}

optional<local_decl> local_context::has_dependencies(local_decl const & d, metavar_context const & mctx) const {
    lean_assert(find_local_decl(d.get_name()));
    expr l = d.mk_ref();
    optional<local_decl> r;
    for_each_after(d, [&](local_decl const & d2) {
            if (r) return;
            if (depends_on(d2, mctx, 1, &l))
                r = d2;
        });
    return r;
}

void local_context::clear(local_decl const & d) {
    lean_assert(find_local_decl(d.get_name()));
    m_idx2local_decl.erase(d.get_idx());
    m_name2local_decl.erase(d.get_name());
    erase_user_name(d);
}

bool local_context::is_subset_of(name_set const & ls) const {
    // TODO(Leo): we can improve performance by implementing the subset operation in the rb_map/rb_tree class
    return !static_cast<bool>(m_name2local_decl.find_if([&](name const & n, local_decl const &) {
                return !ls.contains(n);
            }));
}

bool local_context::is_subset_of(local_context const & ctx) const {
    // TODO(Leo): we can improve performance by implementing the subset operation in the rb_map/rb_tree class
    return !static_cast<bool>(m_name2local_decl.find_if([&](name const & n, local_decl const &) {
                return !ctx.m_name2local_decl.contains(n);
            }));
}

local_context local_context::remove(buffer<expr> const & locals) const {
    lean_assert(std::all_of(locals.begin(), locals.end(),
                            [&](expr const & l) {
                                return is_local_decl_ref(l) && find_local_decl(l);
                            }));
    /* TODO(Leo): check whether the following loop is a performance bottleneck. */
    local_context r          = *this;
    r.m_local_instances      = m_local_instances;
    for (expr const & l : locals) {
        local_decl d = get_local_decl(l);

        /* frozen local instances cannot be deleted */
        if (m_local_instances) {
            lean_assert(std::all_of(m_local_instances->begin(), m_local_instances->end(), [&](local_instance const & inst) {
                        return mlocal_name(inst.get_local()) != d.get_name();
                }));
        }

        r.m_name2local_decl.erase(mlocal_name(l));
        r.m_idx2local_decl.erase(d.get_idx());
        r.erase_user_name(d);
    }
    lean_assert(r.well_formed());
    return r;
}

/* Return true iff all local_decl references in \c e are in \c s. */
static bool locals_subset_of(expr const & e, name_set const & s) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false; // stop search
            if (is_local_decl_ref(e) && !s.contains(mlocal_name(e))) {
                ok = false;
                return false;
            }
            return true;
        });
    return ok;
}

bool local_context::well_formed() const {
    bool ok = true;
    name_set found_locals;
    for_each([&](local_decl const & d) {
            if (!locals_subset_of(d.get_type(), found_locals)) {
                ok = false;
                lean_unreachable();
            }
            if (auto v = d.get_value()) {
                if (!locals_subset_of(*v, found_locals)) {
                    ok = false;
                    lean_unreachable();
                }
            }
            if (!m_user_names.contains(d.get_pp_name())) {
                ok = false;
                lean_unreachable();
            }
            found_locals.insert(d.get_name());
        });
    return ok;
}

bool local_context::well_formed(expr const & e) const {
    bool ok = true;
    ::lean::for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (is_local_decl_ref(e) && !find_local_decl(e)) {
                ok = false;
            }
            return true;
        });
    return ok;
}

format local_context::pp(formatter const & fmt, std::function<bool(local_decl const &)> const & pred) const { // NOLINT
    options const & opts = fmt.get_options();
    unsigned indent      = get_pp_indent(opts);
    unsigned max_hs      = get_pp_goal_max_hyps(opts);
    bool first           = true;
    unsigned i           = 0;
    format ids;
    optional<expr> type;
    format r;
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            if (!pred(d))
                return;
            if (i >= max_hs)
                return;
            i++;
            if (type && (d.get_type() != *type || d.get_value())) {
                // add (ids : type) IF the d.get_type() != type OR d is a let-decl
                if (first) first = false;
                else r += comma() + line();

                r += group(ids + space() + colon() + nest(indent, line() + fmt(*type)));
                type = optional<expr>();
                ids  = format();
            }

            name n = sanitize_if_fresh(d.get_pp_name());
            n = sanitize_name_generator_name(n);

            if (d.get_value()) {
                if (first) first = false;
                else r += comma() + line();
                r += group(format(n) + space() + colon() + space() + fmt(d.get_type()) +
                           space() + format(":=") + nest(indent, line() + fmt(*d.get_value())));
            } else if (!type) {
                lean_assert(!d.get_value());
                ids  = format(n);
                type = d.get_type();
            } else {
                lean_assert(!d.get_value());
                lean_assert(type && d.get_type() == *type);
                ids += space() + format(n);
            }
        });
    if (type) {
        if (!first) r += comma() + line();
        r += group(ids + space() + colon() + nest(indent, line() + fmt(*type)));
    }
    if (get_pp_goal_compact(opts))
        r = group(r);
    return r;
}

bool local_context::uses_user_name(name const & n) const {
    return m_user_names.contains(n);
}

name local_context::get_unused_name(name const & prefix, unsigned & idx) const {
    return m_user_names.get_unused_name(prefix, idx);
}

name local_context::get_unused_name(name const & suggestion) const {
    return m_user_names.get_unused_name(suggestion);
}

local_context local_context::instantiate_mvars(metavar_context & mctx) const {
    local_context r;
    r.m_next_idx        = m_next_idx;
    r.m_local_instances = m_local_instances;
    m_idx2local_decl.for_each([&](unsigned, local_decl const & d) {
            expr new_type = mctx.instantiate_mvars(d.m_ptr->m_type);
            optional<expr> new_value;
            if (d.m_ptr->m_value)
                new_value = mctx.instantiate_mvars(*d.m_ptr->m_value);
            local_decl new_d(d, new_type, new_value);
            r.m_name2local_decl.insert(d.get_name(), new_d);
            r.m_idx2local_decl.insert(d.get_idx(), new_d);
            r.insert_user_name(d);
        });
    return r;
}

bool contains_let_local_decl(local_context const & lctx, expr const & e) {
    if (!has_local(e)) return false;
    return static_cast<bool>(find(e, [&](expr const & e, unsigned) {
                if (!is_local(e)) return false;
                optional<local_decl> d = lctx.find_local_decl(e);
                return d && d->get_value();
            }));
}

expr zeta_expand(local_context const & lctx, expr const & e) {
    if (!contains_let_local_decl(lctx, e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_local(e)) return some_expr(e);
            if (is_local(e)) {
                if (auto d = lctx.find_local_decl(e)) {
                    if (auto v = d->get_value())
                        return some_expr(zeta_expand(lctx, *v));
                }
            }
            return none_expr();
        });
}

void initialize_local_context() {
    g_local_prefix = new name(name::mk_internal_unique_name());
    g_dummy_type   = new expr(mk_constant(name::mk_internal_unique_name()));
    g_dummy_decl   = new local_decl(std::numeric_limits<unsigned>::max(),
                                    name("__local_decl_for_default_constructor"), name("__local_decl_for_default_constructor"),
                                    *g_dummy_type, optional<expr>(), binder_info());
}

void finalize_local_context() {
    delete g_local_prefix;
    delete g_dummy_type;
    delete g_dummy_decl;
}
}




// ========== kernel_serializer.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/serializer.h"
#include "kernel/declaration.h"
#include "kernel/inductive/inductive.h"

namespace lean {
serializer & operator<<(serializer & s, level const & l);
level read_level(deserializer & d);
inline deserializer & operator>>(deserializer & d, level & l) { l = read_level(d); return d; }

serializer & operator<<(serializer & s, levels const & ls);
levels read_levels(deserializer & d);

serializer & operator<<(serializer & s, level_param_names const & ps);
level_param_names read_level_params(deserializer & d);
inline deserializer & operator>>(deserializer & d, level_param_names & ps) { ps = read_level_params(d); return d; }

serializer & operator<<(serializer & s, expr const & e);
expr read_expr(deserializer & d);
inline deserializer & operator>>(deserializer & d, expr & e) { e = read_expr(d); return d; }

serializer & operator<<(serializer & s, declaration const & d);
declaration read_declaration(deserializer & d);

serializer & operator<<(serializer & s, inductive::certified_inductive_decl const & d);
inductive::certified_inductive_decl read_certified_inductive_decl(deserializer & d);

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd);
void initialize_kernel_serializer();
void finalize_kernel_serializer();
}




// ========== kernel_serializer.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/object_serializer.h"
#include "kernel/expr.h"
#include "kernel/declaration.h"
#include "library/kernel_serializer.h"

// Procedures for serializing and deserializing kernel objects (levels, exprs, declarations)
namespace lean {
// Universe level serialization
class level_serializer : public object_serializer<level, level::ptr_hash, level::ptr_eq> {
    typedef object_serializer<level, level::ptr_hash, level::ptr_eq> super;
public:
    void write(level const & l) {
        super::write(l, [&]() {
                serializer & s = get_owner();
                auto k = kind(l);
                s << static_cast<char>(k);
                switch (k) {
                case level_kind::Zero:     break;
                case level_kind::Param:    s << param_id(l);   break;
                case level_kind::Meta:     s << meta_id(l);    break;
                case level_kind::Max:      write(max_lhs(l));  write(max_rhs(l)); break;
                case level_kind::IMax:     write(imax_lhs(l)); write(imax_rhs(l)); break;
                case level_kind::Succ:     write(succ_of(l));  break;
                }
            });
    }
};

class level_deserializer : public object_deserializer<level> {
    typedef object_deserializer<level> super;
public:
    level read() {
        return super::read([&]() -> level {
                deserializer & d = get_owner();
                auto k = static_cast<level_kind>(d.read_char());
                switch (k) {
                case level_kind::Zero:
                    return mk_level_zero();
                case level_kind::Param:
                    return mk_param_univ(read_name(d));
                case level_kind::Meta:
                    return mk_meta_univ(read_name(d));
                case level_kind::Max: {
                    level lhs = read();
                    return mk_max(lhs, read());
                }
                case level_kind::IMax: {
                    level lhs = read();
                    return mk_imax(lhs, read());
                }
                case level_kind::Succ:
                    return mk_succ(read());
                }
                throw corrupted_stream_exception();
            });
    }
};

struct level_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    level_sd() {
        m_s_extid = serializer::register_extension([](){
                return std::unique_ptr<serializer::extension>(new level_serializer());
            });
        m_d_extid = deserializer::register_extension([](){
                return std::unique_ptr<deserializer::extension>(new level_deserializer());
            });
    }
};

static level_sd * g_level_sd = nullptr;

serializer & operator<<(serializer & s, level const & n) {
    s.get_extension<level_serializer>(g_level_sd->m_s_extid).write(n);
    return s;
}

level read_level(deserializer & d) { return d.get_extension<level_deserializer>(g_level_sd->m_d_extid).read(); }

serializer & operator<<(serializer & s, levels const & ls) { return write_list<level>(s, ls); }

levels read_levels(deserializer & d) { return read_list<level>(d, read_level); }

// Expression serialization
typedef std::unordered_map<std::string, macro_definition_cell::reader> macro_readers;
static macro_readers * g_macro_readers = nullptr;

macro_readers & get_macro_readers() {
    return *g_macro_readers;
}

void register_macro_deserializer(std::string const & k, macro_definition_cell::reader rd) {
    macro_readers & readers = get_macro_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = rd;
}

static expr read_macro_definition(deserializer & d, unsigned num, expr const * args) {
    auto k  = d.read_string();
    macro_readers & readers = get_macro_readers();
    auto it = readers.find(k);
    if (it == readers.end()) throw corrupted_stream_exception();
    return it->second(d, num, args);
}

serializer & operator<<(serializer & s, binder_info const & i) {
    unsigned w =
        (i.is_rec() ?             8 : 0) +
        (i.is_implicit() ?        4 : 0) +
        (i.is_strict_implicit() ? 2 : 0) +
        (i.is_inst_implicit() ?   1 : 0);
    s.write_char(w);
    return s;
}

static binder_info read_binder_info(deserializer & d) {
    unsigned w = d.read_char();
    bool rec   = (w & 8) != 0;
    bool imp   = (w & 4)  != 0;
    bool s_imp = (w & 2)  != 0;
    bool i_imp = (w & 1)  != 0;
    return binder_info(imp, s_imp, i_imp, rec);
}

static name * g_binder_name = nullptr;

class expr_serializer : public object_serializer<expr, expr_hash, is_bi_equal_proc> {
    typedef object_serializer<expr, expr_hash, is_bi_equal_proc> super;
    unsigned       m_next_id;

    void write_binder_name(serializer & s, name const & a) {
        // make sure binding names are atomic string
        if (!a.is_atomic() || a.is_numeral()) {
            s << g_binder_name->append_after(m_next_id);
            m_next_id++;
        } else {
            s << a;
        }
    }

    void write_core(expr const & a) {
        auto k = a.kind();
        super::write_core(a, static_cast<char>(k), [&]() {
                serializer & s = get_owner();
                switch (k) {
                case expr_kind::Var:
                    s << var_idx(a);
                    break;
                case expr_kind::Constant:
                    lean_assert(!const_name(a).is_anonymous());
                    s << const_name(a) << const_levels(a);
                    break;
                case expr_kind::Sort:
                    s << sort_level(a);
                    break;
                case expr_kind::Macro:
                    s << macro_num_args(a);
                    for (unsigned i = 0; i < macro_num_args(a); i++) {
                        write_core(macro_arg(a, i));
                    }
                    macro_def(a).write(s);
                    break;
                case expr_kind::App:
                    write_core(app_fn(a)); write_core(app_arg(a));
                    break;
                case expr_kind::Lambda: case expr_kind::Pi:
                    lean_assert(!binding_name(a).is_anonymous());
                    write_binder_name(s, binding_name(a));
                    s << binding_info(a); write_core(binding_domain(a)); write_core(binding_body(a));
                    break;
                case expr_kind::Let:
                    s << let_name(a);
                    write_core(let_type(a)); write_core(let_value(a)); write_core(let_body(a));
                    break;
                case expr_kind::Meta:
                    lean_assert(!mlocal_name(a).is_anonymous());
                    s << mlocal_name(a) << mlocal_pp_name(a); write_core(mlocal_type(a));
                    break;
                case expr_kind::Local:
                    lean_assert(!mlocal_name(a).is_anonymous());
                    lean_assert(!mlocal_pp_name(a).is_anonymous());
                    s << mlocal_name(a) << mlocal_pp_name(a) << local_info(a); write_core(mlocal_type(a));
                    break;
                }
            });
    }
public:
    expr_serializer() { m_next_id = 0; }
    void write(expr const & a) {
        write_core(a);
    }
};

class expr_deserializer : public object_deserializer<expr> {
    typedef object_deserializer<expr> super;
public:
    expr read_binding(expr_kind k) {
        deserializer & d   = get_owner();
        name n             = read_name(d);
        binder_info i      = read_binder_info(d);
        expr t             = read();
        return mk_binding(k, n, t, read(), i);
    }

    expr read() {
        return super::read_core([&](char c) {
                deserializer & d = get_owner();
                auto k = static_cast<expr_kind>(c);
                switch (k) {
                case expr_kind::Var:
                    return mk_var(d.read_unsigned());
                case expr_kind::Constant: {
                    auto n = read_name(d);
                    return mk_constant(n, read_levels(d));
                }
                case expr_kind::Sort:
                    return mk_sort(read_level(d));
                case expr_kind::Macro: {
                    unsigned n = d.read_unsigned();
                    buffer<expr> args;
                    for (unsigned i = 0; i < n; i++) {
                        args.push_back(read());
                    }
                    return read_macro_definition(d, args.size(), args.data());
                }
                case expr_kind::App: {
                    expr f = read();
                    return mk_app(f, read());
                }
                case expr_kind::Lambda: case expr_kind::Pi:
                    return read_binding(k);
                case expr_kind::Let: {
                    name n = read_name(d);
                    expr t = read();
                    expr v = read();
                    return mk_let(n, t, v, read());
                }
                case expr_kind::Meta: {
                    name n    = read_name(d);
                    name pp_n = read_name(d);
                    return mk_metavar(n, pp_n, read());
                }
                case expr_kind::Local: {
                    name n         = read_name(d);
                    name pp_n      = read_name(d);
                    binder_info bi = read_binder_info(d);
                    return mk_local(n, pp_n, read(), bi);
                }}
                throw corrupted_stream_exception(); // LCOV_EXCL_LINE
            });
    }
};

struct expr_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    expr_sd() {
        m_s_extid = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new expr_serializer()); });
        m_d_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new expr_deserializer()); });
    }
};
static expr_sd * g_expr_sd = nullptr;

serializer & operator<<(serializer & s, expr const & n) {
    s.get_extension<expr_serializer>(g_expr_sd->m_s_extid).write(n);
    return s;
}

expr read_expr(deserializer & d) {
    return d.get_extension<expr_deserializer>(g_expr_sd->m_d_extid).read();
}

serializer & operator<<(serializer & s, reducibility_hints const & h) {
    s << static_cast<char>(h.get_kind());
    if (h.is_regular())
        s << static_cast<char>(h.use_self_opt()) << h.get_height();
    return s;
}

reducibility_hints read_hints(deserializer & d) {
    char k;
    d >> k;
    reducibility_hints::kind kind = static_cast<reducibility_hints::kind>(k);
    if (kind == reducibility_hints::Regular) {
        char use_conv; unsigned height;
        d >> use_conv >> height;
        return reducibility_hints::mk_regular(height, static_cast<bool>(use_conv));
    } else if (kind == reducibility_hints::Opaque) {
        return reducibility_hints::mk_opaque();
    } else {
        return reducibility_hints::mk_abbreviation();
    }
}

// Declaration serialization
serializer & operator<<(serializer & s, level_param_names const & ps) { return write_list<name>(s, ps); }
level_param_names read_level_params(deserializer & d) { return read_list<name>(d); }
serializer & operator<<(serializer & s, declaration const & d) {
    char k = 0;
    if (d.is_definition())
        k |= 1;
    if (d.is_theorem() || d.is_axiom())
        k |= 2;
    if (d.is_trusted())
        k |= 4;
    s << k << d.get_name() << d.get_univ_params() << d.get_type();
    if (d.is_definition()) {
        s << d.get_value();
        if (!d.is_theorem())
            s << d.get_hints();
    }
    return s;
}

declaration read_declaration(deserializer & d) {
    char k               = d.read_char();
    bool has_value       = (k & 1) != 0;
    bool is_th_ax        = (k & 2) != 0;
    bool is_trusted      = (k & 4) != 0;
    name n               = read_name(d);
    level_param_names ps = read_level_params(d);
    expr t               = read_expr(d);
    if (has_value) {
        expr v      = read_expr(d);
        if (is_th_ax) {
            return mk_theorem(n, ps, t, v);
        } else {
            reducibility_hints hints = read_hints(d);
            return mk_definition(n, ps, t, v, hints, is_trusted);
        }
    } else {
        if (is_th_ax)
            return mk_axiom(n, ps, t);
        else
            return mk_constant_assumption(n, ps, t, is_trusted);
    }
}

using inductive::certified_inductive_decl;
using inductive::inductive_decl;
using inductive::intro_rule;
using inductive::intro_rule_name;
using inductive::intro_rule_type;

serializer & operator<<(serializer & s, certified_inductive_decl::comp_rule const & r) {
    s << r.m_num_bu << r.m_comp_rhs;
    return s;
}

certified_inductive_decl::comp_rule read_comp_rule(deserializer & d) {
    unsigned n; expr e;
    d >> n >> e;
    return certified_inductive_decl::comp_rule(n, e);
}

serializer & operator<<(serializer & s, inductive_decl const & d) {
    s << d.m_name << d.m_level_params << d.m_num_params << d.m_type << length(d.m_intro_rules);
    for (intro_rule const & r : d.m_intro_rules)
        s << intro_rule_name(r) << intro_rule_type(r);
    return s;
}

inductive_decl read_inductive_decl(deserializer & d) {
    name d_name                 = read_name(d);
    level_param_names d_lparams = read_level_params(d);
    unsigned d_nparams          = d.read_unsigned();
    expr d_type                 = read_expr(d);
    unsigned num_intros         = d.read_unsigned();
    buffer<intro_rule> rules;
    for (unsigned j = 0; j < num_intros; j++) {
        name r_name = read_name(d);
        expr r_type = read_expr(d);
        rules.push_back(inductive::mk_intro_rule(r_name, r_type));
    }
    return inductive_decl(d_name, d_lparams, d_nparams, d_type, to_list(rules.begin(), rules.end()));
}

serializer & operator<<(serializer & s, certified_inductive_decl const & d) {
    s << d.get_num_ACe() << d.elim_prop_only() << d.has_dep_elim()
      << d.get_elim_levels() << d.get_elim_type() << d.get_decl()
      << d.is_K_target() << d.get_num_indices() << d.is_trusted();
    write_list<certified_inductive_decl::comp_rule>(s, d.get_comp_rules());
    return s;
}

class read_certified_inductive_decl_fn {
public:
    certified_inductive_decl operator()(deserializer & d) {
        unsigned nACe        = d.read_unsigned();
        bool elim_prop       = d.read_bool();
        bool dep_elim        = d.read_bool();
        level_param_names ls = read_list<name>(d, read_name);
        expr elim_type       = read_expr(d);
        inductive_decl decl  = read_inductive_decl(d);
        bool       K         = d.read_bool();
        unsigned   nind      = d.read_unsigned();
        bool is_trusted      = d.read_bool();
        auto rs              = read_list<certified_inductive_decl::comp_rule>(d, read_comp_rule);
        return certified_inductive_decl(nACe, elim_prop, dep_elim, ls, elim_type, decl,
                                        K, nind, rs, is_trusted);
    }
};

certified_inductive_decl read_certified_inductive_decl(deserializer & d) {
    return read_certified_inductive_decl_fn()(d);
}

void initialize_kernel_serializer() {
    g_level_sd      = new level_sd();
    g_macro_readers = new macro_readers();
    g_binder_name   = new name("a");
    g_expr_sd       = new expr_sd();
}

void finalize_kernel_serializer() {
    delete g_expr_sd;
    delete g_binder_name;
    delete g_macro_readers;
    delete g_level_sd;
}
}




// ========== discr_tree.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
/**
   \brief (Imperfect) discrimination trees.
   The edges are labeled with:
   1- Constant names (the universes are ignored)
   2- Local names (e.g., hypotheses)
   3- Star/Wildcard (we use them to encode metavariables). We use the same symbol
      for all metavariables. Remark: in the discrimination tree literature, our
      metavariables are called variables.
   4- Unsupported. We use them to encode nested lambda's, Pi's, Sort's
      Anything that is not an application, constant or local.
   When indexing terms, we ignore propositions and instance implicit
   arguments. We use get_fun_info procedure for retrieving
   this information. */
class discr_tree {
public:
    struct node_cell;
private:
    enum class edge_kind { Local, Constant, Star, Unsupported };
    struct edge;
    struct edge_cmp;
    struct node_cmp;
    struct node {
        node_cell * m_ptr;
        node():m_ptr(nullptr) {}
        node(node_cell * ptr);
        node(node const & s);
        node(node && s);

        ~node();
        node & operator=(node const & n);
        node & operator=(node&& n);
        operator bool() const { return m_ptr != nullptr; }
        bool is_shared() const;
        node steal() { node r; swap(r, *this); return r; }
        void trace(optional<edge> const & e, unsigned depth, bool disj) const;
    };
    static void swap(node & n1, node & n2);
    static node ensure_unshared(node && n);
    static node insert_erase_atom(type_context_old & ctx, node && n, edge const & e, buffer<pair<expr, bool>> & todo, expr const & v, buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase_star(type_context_old & ctx, node && n, buffer<pair<expr, bool>> & todo, expr const & v, buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase_app(type_context_old & ctx, node && n, bool is_root, expr const & e, buffer<pair<expr, bool>> & todo, expr const & v,
                                 buffer<pair<node, node>> & skip, bool ins);
    static node insert_erase(type_context_old & ctx, node && n, bool is_root, buffer<pair<expr, bool>> & todo,
                             expr const & v, buffer<pair<node, node>> & skip, bool ins);
    void insert_erase(type_context_old & ctx, expr const & k, expr const & v, bool ins);

    static bool find_atom(type_context_old & ctx, node const & n, edge const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find_star(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find_app(type_context_old & ctx, node const & n, expr const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT
    static bool find(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn); // NOLINT

    node m_root;
public:
    void insert(type_context_old & ctx, expr const & k, expr const & v) { insert_erase(ctx, k, v, true); }
    void insert(type_context_old & ctx, expr const & k) { insert(ctx, k, k); }
    void erase(type_context_old & ctx, expr const & k, expr const & v) { insert_erase(ctx, k, v, false); }
    void erase(type_context_old & ctx, expr const & k) { erase(ctx, k, k); }

    void find(type_context_old & ctx, expr const & e, std::function<bool(expr const &)> const & fn) const; // NOLINT
    void collect(type_context_old & ctx, expr const & e, buffer<expr> & r) const;

    void trace() const;
};
void initialize_discr_tree();
void finalize_discr_tree();
}




// ========== discr_tree.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "util/rb_map.h"
#include "util/memory_pool.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/fun_info.h"
#include "library/discr_tree.h"

namespace lean {
/* Auxiliary expr used to implement insert/erase operations.
   When adding the children of an application into the todo stack,
   we use g_delimiter to indicate where the arguments end.
   For example, suppose the current stack is S, and we want
   to add the children of (f a b). Then, the new stack will
   be [S, *g_delimiter, b, a]
   \remark g_delimiter is an unique expression. */
static expr * g_delimiter = nullptr;

struct discr_tree::node_cmp {
    int operator()(node const & n1, node const & n2) const;
};

void discr_tree::swap(node & n1, node & n2) {
    std::swap(n1.m_ptr, n2.m_ptr);
}

struct discr_tree::edge {
    edge_kind m_kind;
    bool      m_fn;
    name      m_name; // only relevant for Local/Const
    edge(edge_kind k):m_kind(k), m_fn(false) {}
    edge(expr const & e, bool fn) {
        m_fn = fn;
        lean_assert(is_constant(e) || is_local(e));
        if (is_constant(e)) {
            m_kind = edge_kind::Constant;
            m_name = const_name(e);
        } else {
            lean_assert(is_local(e));
            m_kind = edge_kind::Local;
            m_name = mlocal_name(e);
        }
    }
};

struct discr_tree::edge_cmp {
    int operator()(edge const & e1, edge const & e2) const {
        if (e1.m_fn != e2.m_fn)
           return static_cast<int>(e1.m_fn) - static_cast<int>(e2.m_fn);
        if (e1.m_kind != e2.m_kind)
            return static_cast<int>(e1.m_kind) - static_cast<int>(e2.m_kind);
        return quick_cmp(e1.m_name, e2.m_name);
    }
};

struct discr_tree::node_cell {
    MK_LEAN_RC();
    /* Unique id. We use it to implement node_cmp */
    unsigned                      m_id;
    /* We use a map based tree to map edges to nodes, we should investigate whether we really need a tree here.
       We suspect the set of edges is usually quite small. So, an assoc-list may be enough.
       We should also investigate whether a small array + hash code based on the edge is not enough.
       Note that we may even ignore collisions since this is an imperfect discrimination tree anyway. */
    rb_map<edge, node, edge_cmp>  m_children;
    node                          m_star_child;
    /* The skip set is needed when searching for the set of terms stored in the discrimination tree
       that may match an input term containing metavariables. In the literature, they are called
       skip set/list. */
    rb_tree<node, node_cmp>       m_skip;
    rb_expr_tree                  m_values;
    void dealloc();
    node_cell();
    node_cell(node_cell const & s);
};

DEF_THREAD_MEMORY_POOL(get_allocator, sizeof(discr_tree::node_cell));
LEAN_THREAD_VALUE(unsigned, g_next_id, 0);
MK_THREAD_LOCAL_GET_DEF(std::vector<unsigned>, get_recycled_ids);

static unsigned mk_id() {
    auto & ids = get_recycled_ids();
    unsigned r;
    if (ids.empty()) {
        r = g_next_id;
        g_next_id++;
    } else {
        r = ids.back();
        ids.pop_back();
    }
    return r;
}

discr_tree::node_cell::node_cell():m_rc(0), m_id(mk_id()) {
}

discr_tree::node_cell::node_cell(node_cell const & s):
    m_rc(0), m_id(mk_id()),
    m_children(s.m_children),
    m_star_child(s.m_star_child),
    m_values(s.m_values) {
}

void discr_tree::node_cell::dealloc() {
    this->~node_cell();
    get_recycled_ids().push_back(m_id);
    get_allocator().recycle(this);
}

auto discr_tree::ensure_unshared(node && n) -> node {
    if (!n.m_ptr)
        return node(new (get_allocator().allocate()) node_cell());
    else if (n.is_shared())
        return node(new (get_allocator().allocate()) node_cell(*n.m_ptr));
    else
        return n;
}

discr_tree::node::node(node_cell * ptr):m_ptr(ptr) { if (m_ptr) ptr->inc_ref(); }
discr_tree::node::node(node const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
discr_tree::node::node(node && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
discr_tree::node::~node() { if (m_ptr) m_ptr->dec_ref(); }

discr_tree::node & discr_tree::node::operator=(node const & n) { LEAN_COPY_REF(n); }
discr_tree::node & discr_tree::node::operator=(node&& n) { LEAN_MOVE_REF(n); }
bool discr_tree::node::is_shared() const { return m_ptr && m_ptr->get_rc() > 1; }

int discr_tree::node_cmp::operator()(node const & n1, node const & n2) const {
    if (n1.m_ptr) {
        return n2.m_ptr ? unsigned_cmp()(n1.m_ptr->m_id, n2.m_ptr->m_id) : 1;
    } else {
        return n2.m_ptr ? -1 : 0;
    }
}

auto discr_tree::insert_erase_atom(type_context_old & ctx, node && n, edge const & e, buffer<pair<expr, bool>> & todo,
                                   expr const & v, buffer<pair<node, node>> & skip, bool ins) -> node {
    node new_n = ensure_unshared(n.steal());
    if (auto child = new_n.m_ptr->m_children.find(e)) {
        node new_child(*child);
        new_n.m_ptr->m_children.erase(e);
        new_child = insert_erase(ctx, new_child.steal(), false, todo, v, skip, ins);
        new_n.m_ptr->m_children.insert(e, new_child);
        return new_n;
    } else {
        node new_child = insert_erase(ctx, node(), false, todo, v, skip, ins);
        new_n.m_ptr->m_children.insert(e, new_child);
        return new_n;
    }
}

auto discr_tree::insert_erase_star(type_context_old & ctx, node && n, buffer<pair<expr, bool>> & todo, expr const & v,
                                   buffer<pair<node, node>> & skip, bool ins) -> node {
    node new_n = ensure_unshared(n.steal());
    new_n.m_ptr->m_star_child = insert_erase(ctx, new_n.m_ptr->m_star_child.steal(), false, todo, v, skip, ins);
    return new_n;
}

auto discr_tree::insert_erase_app(type_context_old & ctx,
                                  node && n, bool is_root, expr const & e, buffer<pair<expr, bool>> & todo, expr const & v,
                                  buffer<pair<node, node>> & skip, bool ins) -> node {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) || is_local(fn)) {
        if (!is_root)
            todo.push_back(mk_pair(*g_delimiter, false));
        fun_info info = get_fun_info(ctx, fn, args.size());
        buffer<param_info> pinfos;
        to_buffer(info.get_params_info(), pinfos);
        lean_assert(pinfos.size() == args.size());
        unsigned i = args.size();
        while (i > 0) {
            --i;
            if (pinfos[i].is_prop() || pinfos[i].is_inst_implicit() || pinfos[i].is_implicit())
                continue; // We ignore propositions, implicit and inst-implict arguments
            todo.push_back(mk_pair(args[i], false));
        }
        todo.push_back(mk_pair(fn, true));
        node new_n = insert_erase(ctx, std::move(n), false, todo, v, skip, ins);
        if (!is_root) {
            lean_assert(!skip.empty());
            // Update skip set.
            pair<node, node> const & p = skip.back();
            new_n.m_ptr->m_skip.erase(p.first);   // remove old skip node
            new_n.m_ptr->m_skip.insert(p.second); // insert new skip node
            skip.pop_back();
        }
        return new_n;
    } else if (is_meta(fn)) {
        return insert_erase_star(ctx, std::move(n), todo, v, skip, ins);
    } else {
        return insert_erase_atom(ctx, std::move(n), edge(edge_kind::Unsupported), todo, v, skip, ins);
    }
}

auto discr_tree::insert_erase(type_context_old & ctx,
                              node && n, bool is_root, buffer<pair<expr, bool>> & todo,
                              expr const & v, buffer<pair<node, node>> & skip, bool ins) -> node {
    if (todo.empty()) {
        node new_n = ensure_unshared(n.steal());
        if (ins)
            new_n.m_ptr->m_values.insert(v);
        else
            new_n.m_ptr->m_values.erase(v);
        return new_n;
    }

    pair<expr, bool> p = todo.back();
    todo.pop_back();
    expr const & e = p.first;
    bool fn        = p.second;

    if (is_eqp(e, *g_delimiter)) {
        node old_n(n);
        node new_n = insert_erase(ctx, std::move(n), false, todo, v, skip, ins);
        skip.emplace_back(old_n, new_n);
        return new_n;
    }

    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Local:
        return insert_erase_atom(ctx, std::move(n), edge(e, fn), todo, v, skip, ins);
    case expr_kind::Meta:
        return insert_erase_star(ctx, std::move(n), todo, v, skip, ins);
    case expr_kind::App:
        return insert_erase_app(ctx, std::move(n), is_root, e, todo, v, skip, ins);
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Sort: case expr_kind::Lambda:
    case expr_kind::Pi:   case expr_kind::Macro:
    case expr_kind::Let:
        // unsupported
        return insert_erase_atom(ctx, std::move(n), edge(edge_kind::Unsupported), todo, v, skip, ins);
    }
    lean_unreachable();
}

void discr_tree::insert_erase(type_context_old & ctx, expr const & k, expr const & v, bool ins) {
    // insert & erase operations.
    // The erase operation is not optimal because it does not eliminate dead branches from the tree.
    // If this becomes an issue, we can remove dead branches from time to time and/or reconstruct
    // the tree from time to time.
    buffer<pair<expr, bool>> todo;
    buffer<pair<node, node>> skip;
    todo.push_back(mk_pair(k, false));
    m_root = insert_erase(ctx, m_root.steal(), true, todo, v, skip, ins);
    lean_trace("discr_tree", tout() << "\n"; trace(););
}

bool discr_tree::find_atom(type_context_old & ctx, node const & n, edge const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    if (auto child = n.m_ptr->m_children.find(e)) {
        return find(ctx, *child, todo, fn);
    } else {
        return true; // continue
    }
}

bool discr_tree::find_star(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    bool cont = true;
    n.m_ptr->m_skip.for_each([&](node const & skip_child) {
            if (cont && !find(ctx, skip_child, todo, fn))
                cont = false;
        });
    if (!cont)
        return false;
    // we also have to traverse children whose edge is an atom.
    n.m_ptr->m_children.for_each([&](edge const & e, node const & child) {
            if (cont && !e.m_fn && !find(ctx, child, todo, fn))
                cont = false;
        });
    return cont;
}

bool discr_tree::find_app(type_context_old & ctx, node const & n, expr const & e, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    if (is_constant(f) || is_local(f)) {
        fun_info info = get_fun_info(ctx, f, args.size());
        buffer<param_info> pinfos;
        to_buffer(info.get_params_info(), pinfos);
        lean_assert(pinfos.size() == args.size());
        unsigned i = args.size();
        list<pair<expr, bool>> new_todo = todo;
        while (i > 0) {
            --i;
            if (pinfos[i].is_prop() || pinfos[i].is_inst_implicit() || pinfos[i].is_implicit())
                continue; // We ignore propositions, implicit and inst-implict arguments
            new_todo = cons(mk_pair(args[i], false), new_todo);
        }
        new_todo = cons(mk_pair(f, true), new_todo);
        return find(ctx, n, new_todo, fn);
    } else if (is_meta(f)) {
        return find_star(ctx, n, todo, fn);
    } else {
        return find_atom(ctx, n, edge(edge_kind::Unsupported), todo, fn);
    }
}

bool discr_tree::find(type_context_old & ctx, node const & n, list<pair<expr, bool>> todo, std::function<bool(expr const &)> const & fn) { // NOLINT
    if (!todo) {
        bool cont = true;
        n.m_ptr->m_values.for_each([&](expr const & v) {
                if (cont && !fn(v))
                    cont = false;
            });
        return cont;
    }

    if (n.m_ptr->m_star_child && !find(ctx, n.m_ptr->m_star_child, tail(todo), fn))
        return false; // stop search

    pair<expr, bool> const & p = head(todo);
    expr const & e = p.first;
    bool is_fn     = p.second;

    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Local:
        return find_atom(ctx, n, edge(e, is_fn), tail(todo), fn);
    case expr_kind::Meta:
        return find_star(ctx, n, tail(todo), fn);
    case expr_kind::App:
        return find_app(ctx, n, e, tail(todo), fn);
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Sort: case expr_kind::Lambda:
    case expr_kind::Pi:   case expr_kind::Macro:
    case expr_kind::Let:
        // unsupported
        return find_atom(ctx, n, edge(edge_kind::Unsupported), tail(todo), fn);
    }
    lean_unreachable();
}

void discr_tree::find(type_context_old & ctx, expr const & e, std::function<bool(expr const &)> const & fn) const { // NOLINT
    if (m_root)
        find(ctx, m_root, to_list(mk_pair(e, false)), fn);
}

void discr_tree::collect(type_context_old & ctx, expr const & e, buffer<expr> & r) const {
    find(ctx, e, [&](expr const & v) { r.push_back(v); return true; });
}

static void indent(unsigned depth) {
    for (unsigned i = 0; i < depth; i++) tout() << "  ";
}

void discr_tree::node::trace(optional<edge> const & e, unsigned depth, bool disj) const {
    if (!m_ptr) {
        tout() << "[null]\n";
        return;
    }
    indent(depth);
    if (disj)
        tout() << "| ";
    else if (depth > 0)
        tout() << "  ";
    if (e) {
        switch (e->m_kind) {
        case edge_kind::Constant:
            tout() << e->m_name;
            break;
        case edge_kind::Local:
            tout() << e->m_name;
            break;
        case edge_kind::Star:
            tout() << "*";
            break;
        case edge_kind::Unsupported:
            tout() << "#";
            break;
        }
        if (e->m_fn)
            tout() << " (fn)";
        tout() << " -> ";
    }
    tout() << "[" << m_ptr->m_id << "] {";
    bool first = true;
    m_ptr->m_skip.for_each([&](node const & s) {
            if (first) first = false; else tout() << ", ";
            tout() << s.m_ptr->m_id;
        });
    tout() << "}";
    if (!m_ptr->m_values.empty()) {
        tout() << " {";
        first = true;
        m_ptr->m_values.for_each([&](expr const & v) {
                if (first) first = false; else tout() << ", ";
                tout() << v;
            });
        tout() << "}";
    }
    tout() << "\n";
    unsigned new_depth = depth;
    unsigned num_children = m_ptr->m_children.size();
    if (m_ptr->m_star_child)
        num_children++;
    if (num_children > 1)
        new_depth++;
    m_ptr->m_children.for_each([&](edge const & e, node const & n) {
            n.trace(optional<edge>(e), new_depth, num_children > 1);
        });
    if (m_ptr->m_star_child) {
        m_ptr->m_star_child.trace(optional<edge>(edge_kind::Star), new_depth, num_children > 1);
    }
}

void discr_tree::trace() const {
    m_root.trace(optional<edge>(), 0, false);
}

void initialize_discr_tree() {
    register_trace_class(name{"discr_tree"});
    g_delimiter = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_discr_tree() {
    delete g_delimiter;
}
}




// ========== context_cache.h ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include <unordered_set>
#include "kernel/expr_maps.h"
#include "kernel/equiv_manager.h"
#include "library/expr_unsigned_map.h"
#include "library/expr_pair_maps.h"
#include "library/abstract_context_cache.h"

namespace lean {
class context_cache : public context_cacheless {
    typedef std::unordered_map<name, optional<declaration>, name_hash> transparency_cache;
    typedef std::unordered_map<name, bool, name_hash> name2bool;

    /** We use expr_cond_bi_struct_map because sometimes we want the inferred type to
        contain precise binder information (e.g., in the elaborator).
        Binder information includes the the binder annotations: {}, [], etc.

        That is, we want the type of (fun {A : Type} (a : A), a) to be (Pi {A : Type}, A -> A).

        When binder information is considered in the infer_cache, we can't reuse the
        cached value for (fun {A : Type} (a : A), a) when inferring the type of
        (fun (A : Type) (a : A), a). This is wasteful in modules such as the tactic framework.

        So, when we create a type_context_old_cache object we can specify whether this extra
        level of precision is required or not. */
    typedef expr_cond_bi_map<expr> infer_cache;
    typedef expr_map<expr> whnf_cache;
    typedef expr_map<optional<expr>> instance_cache;
    typedef expr_map<optional<expr>> subsingleton_cache;
    typedef std::unordered_set<expr_pair, expr_pair_hash, expr_pair_eq> failure_cache;

    /* Remark: we only cache inferred types if the metavariable assignment was not accessed.
       This restriction is sufficient to make sure the cached information can be reused. */
    infer_cache                   m_infer_cache;

    /* Mapping from name to optional<declaration>, this mapping is faster than the one
       at environment. Moreover, it takes into account constant reducibility annotations.
       We have four different modes.
       - All (everything is transparent).
       - Semireducible (semireducible and reducible constants are considered transparent).
       - Instances (instances and reducible constants are considered transparent).
       - Reducible (only reducible constants are considered transparent).
       - None (everything is opaque).

       \remark In Semireducible, Instances and Reducible modes, projections and theorems are considered
       opaque independently of annotations. Actually, theorems will not be treated as opaque
       IF option `type_context_old.unfold_lemmas` is set to true.
       In All mode, projections are still considered opaque,
       this is not a problem since type_context_old implements a custom reduction rule for projections.

       The All mode is used for type inference where it is unacceptable to fail to infer a type.
       The Semireducible mode is used for scenarios where an `is_def_eq` is expected to succeed
       (e.g., exact and apply tactics).
       The Reducible mode (more restrictive) is used during search (e.g., type class resolution,
       simp, etc).
       The None mode is used when normalizing expressions without using delta-reduction. */
    transparency_cache            m_transparency_cache[LEAN_NUM_TRANSPARENCY_MODES];
    equiv_manager                 m_equiv_manager[LEAN_NUM_TRANSPARENCY_MODES];
    failure_cache                 m_failure_cache[LEAN_NUM_TRANSPARENCY_MODES];
    whnf_cache                    m_whnf_cache[LEAN_NUM_TRANSPARENCY_MODES];
    name2bool                     m_aux_recursor_cache;

    /* We use the following approach for caching type class instances.

       Whenever a type_context_old object is initialized with a local_context lctx

       1) If lctx has an instance_fingerprint, then we compare with the instance_fingerprint
          stored in this cache, if they are equal, we keep m_local_instances,
          m_instance_cache and m_subsingleton_cache.

          New local instances added using methods type_context_old::push_local and type_context_old::push_let will
          be ignored.

       2) If lctx doesn't have one, we clear m_local_instances, m_instance_cache and m_subsingleton_cache.
          We also traverse lctx and collect the local instances.

          The methods type_context_old::push_local and type_context_old::push_let will flush the cache
          whenever new local instances are pushed into the local context.

          m_instance_cache and m_subsingleton_cache are flushed before the cache is returned to the
          cache manager. */
    instance_cache                m_instance_cache;
    subsingleton_cache            m_subsingleton_cache;

    optional<unification_hints>   m_uhints;

    /* Cache datastructures for fun_info */

    typedef expr_map<fun_info>                fi_cache;
    typedef expr_unsigned_map<fun_info>       fi_cache_nargs;
    typedef expr_map<ss_param_infos>          ss_cache;
    typedef expr_unsigned_map<ss_param_infos> ss_cache_nargs;
    typedef expr_unsigned_map<unsigned>       prefix_cache;
    fi_cache                      m_fi_cache[LEAN_NUM_TRANSPARENCY_MODES];
    fi_cache_nargs                m_fi_cache_nargs[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache                      m_ss_cache[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache_nargs                m_ss_cache_nargs[LEAN_NUM_TRANSPARENCY_MODES];
    ss_cache_nargs                m_ss_cache_spec[LEAN_NUM_TRANSPARENCY_MODES];
    prefix_cache                  m_prefix_cache[LEAN_NUM_TRANSPARENCY_MODES];

public:
    context_cache();
    context_cache(options const & o);
    context_cache(context_cache const &) = delete;
    context_cache(context_cache &&) = default;
    virtual ~context_cache();

    context_cache & operator=(context_cache const &) = delete;
    context_cache & operator=(context_cache &&) = default;

    virtual optional<declaration> get_decl(type_context_old &, transparency_mode, name const &) override;
    virtual projection_info const * get_proj_info(type_context_old &, name const &) override;
    virtual bool get_aux_recursor(type_context_old &, name const &) override;
    virtual void get_unification_hints(type_context_old &, name const & f1, name const & f2, buffer<unification_hint> & hints) override;

    /* Cache support for type_context_old module */

    virtual optional<expr> get_infer(expr const &) override;
    virtual void set_infer(expr const &, expr const &) override;

    virtual bool get_equiv(transparency_mode, expr const &, expr const &) override;
    virtual void set_equiv(transparency_mode, expr const &, expr const &) override;

    virtual bool get_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;
    virtual void set_is_def_eq_failure(transparency_mode, expr const &, expr const &) override;

    virtual optional<expr> get_whnf(transparency_mode, expr const &) override;
    virtual void set_whnf(transparency_mode, expr const &, expr const &) override;

    virtual optional<optional<expr>> get_instance(expr const &) override;
    virtual void set_instance(expr const &, optional<expr> const &) override;

    virtual optional<optional<expr>> get_subsingleton(expr const &) override;
    virtual void set_subsingleton(expr const &, optional<expr> const &) override;

    virtual void flush_instances() override;

    /* Cache support for fun_info module */

    virtual optional<fun_info> get_fun_info(transparency_mode, expr const &) override;
    virtual void set_fun_info(transparency_mode, expr const &, fun_info const &) override;

    virtual optional<fun_info> get_fun_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_fun_info_nargs(transparency_mode, expr const &, unsigned, fun_info const &) override;

    virtual optional<unsigned> get_specialization_prefix_size(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_prefix_size(transparency_mode, expr const &, unsigned, unsigned) override;

    virtual optional<ss_param_infos> get_subsingleton_info(transparency_mode, expr const &) override;
    virtual void set_subsingleton_info(transparency_mode, expr const &, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;

    virtual optional<ss_param_infos> get_specialized_subsingleton_info_nargs(transparency_mode, expr const &, unsigned) override;
    virtual void set_specialization_subsingleton_info_nargs(transparency_mode, expr const &, unsigned, ss_param_infos const &) override;
};
}




// ========== context_cache.cpp ==========

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context_cache.h"
#include "library/type_context.h"

namespace lean {
context_cache::context_cache():
    context_cacheless() {
}

context_cache::context_cache(options const & o):
    context_cacheless(o) {
}

context_cache::~context_cache() {
}

optional<declaration> context_cache::get_decl(type_context_old & ctx, transparency_mode m, name const & n) {
    auto & cache = m_transparency_cache[static_cast<unsigned>(m)];
    auto it = cache.find(n);
    if (it != cache.end()) {
        return it->second;
    }
    optional<declaration> r = context_cacheless::get_decl(ctx, m, n);
    cache.insert(mk_pair(n, r));
    return r;
}

projection_info const * context_cache::get_proj_info(type_context_old & ctx, name const & n) {
    // TODO(Leo): check if we really need a cache for get_proj_info
    return context_cacheless::get_proj_info(ctx, n);
}

bool context_cache::get_aux_recursor(type_context_old & ctx, name const & n) {
    auto it = m_aux_recursor_cache.find(n);
    if (it != m_aux_recursor_cache.end())
        return it->second;
    bool r = context_cacheless::get_aux_recursor(ctx, n);
    m_aux_recursor_cache.insert(mk_pair(n, r));
    return r;
}

void context_cache::get_unification_hints(type_context_old & ctx, name const & f1, name const & f2, buffer<unification_hint> & hints) {
    if (!m_uhints)
        m_uhints = ::lean::get_unification_hints(ctx.env());
    ::lean::get_unification_hints(*m_uhints, f1, f2, hints);
}

template<typename R, typename C, typename K>
optional<R> find_at(C const & c, K const & e) {
    auto it = c.find(e);
    if (it != c.end())
        return optional<R>(it->second);
    else
        return optional<R>();
}

optional<expr> context_cache::get_infer(expr const & e) {
    return find_at<expr>(m_infer_cache, e);
}

void context_cache::set_infer(expr const & e, expr const & ty) {
    m_infer_cache.insert(mk_pair(e, ty));
}

bool context_cache::get_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    return m_equiv_manager[static_cast<unsigned>(m)].is_equiv(e1, e2);
}

void context_cache::set_equiv(transparency_mode m, expr const & e1, expr const & e2) {
    m_equiv_manager[static_cast<unsigned>(m)].add_equiv(e1, e2);
}

bool context_cache::get_is_def_eq_failure(transparency_mode m, expr const & t, expr const & s) {
    auto const & fcache = m_failure_cache[static_cast<unsigned>(m)];
    if (t.hash() < s.hash()) {
        return fcache.find(mk_pair(t, s)) != fcache.end();
    } else if (t.hash() > s.hash()) {
        return fcache.find(mk_pair(s, t)) != fcache.end();
    } else {
        return
            fcache.find(mk_pair(t, s)) != fcache.end() ||
            fcache.find(mk_pair(s, t)) != fcache.end();
    }
}

void context_cache::set_is_def_eq_failure(transparency_mode m, expr const & t, expr const & s) {
    auto & fcache = m_failure_cache[static_cast<unsigned>(m)];
    if (t.hash() <= s.hash())
        fcache.insert(mk_pair(t, s));
    else
        fcache.insert(mk_pair(s, t));
}

optional<expr> context_cache::get_whnf(transparency_mode m, expr const & e) {
    return find_at<expr>(m_whnf_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_whnf(transparency_mode m, expr const & e, expr const & r) {
    m_whnf_cache[static_cast<unsigned>(m)].insert(mk_pair(e, r));
}

optional<optional<expr>> context_cache::get_instance(expr const & e) {
    return find_at<optional<expr>>(m_instance_cache, e);
}

void context_cache::set_instance(expr const & e, optional<expr> const & r) {
    m_instance_cache.insert(mk_pair(e, r));
}

optional<optional<expr>> context_cache::get_subsingleton(expr const & e) {
    return find_at<optional<expr>>(m_subsingleton_cache, e);
}

void context_cache::set_subsingleton(expr const & e, optional<expr> const & r) {
    m_subsingleton_cache.insert(mk_pair(e, r));
}

void context_cache::flush_instances() {
    m_instance_cache.clear();
    m_subsingleton_cache.clear();
}

optional<fun_info> context_cache::get_fun_info(transparency_mode m, expr const & e) {
    return find_at<fun_info>(m_fi_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_fun_info(transparency_mode m, expr const & e, fun_info const & fi) {
    m_fi_cache[static_cast<unsigned>(m)].insert(mk_pair(e, fi));
}

optional<fun_info> context_cache::get_fun_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<fun_info>(m_fi_cache_nargs[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_fun_info_nargs(transparency_mode m, expr const & e, unsigned nargs, fun_info const & fi) {
    m_fi_cache_nargs[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), fi));
}

optional<unsigned> context_cache::get_specialization_prefix_size(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<unsigned>(m_prefix_cache[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_specialization_prefix_size(transparency_mode m, expr const & e, unsigned nargs, unsigned sz) {
    m_prefix_cache[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), sz));
}

optional<ss_param_infos> context_cache::get_subsingleton_info(transparency_mode m, expr const & e) {
    return find_at<ss_param_infos>(m_ss_cache[static_cast<unsigned>(m)], e);
}

void context_cache::set_subsingleton_info(transparency_mode m, expr const & e, ss_param_infos const & ss) {
    m_ss_cache[static_cast<unsigned>(m)].insert(mk_pair(e, ss));
}

optional<ss_param_infos> context_cache::get_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<ss_param_infos>(m_ss_cache_nargs[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs, ss_param_infos const & ss) {
    m_ss_cache_nargs[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), ss));
}

optional<ss_param_infos> context_cache::get_specialized_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs) {
    return find_at<ss_param_infos>(m_ss_cache_spec[static_cast<unsigned>(m)], expr_unsigned(e, nargs));
}

void context_cache::set_specialization_subsingleton_info_nargs(transparency_mode m, expr const & e, unsigned nargs, ss_param_infos const & ss) {
    m_ss_cache_spec[static_cast<unsigned>(m)].insert(mk_pair(expr_unsigned(e, nargs), ss));
}
}




// ========== parray.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <memory>
#include <algorithm>
#include "util/memory_pool.h"
#include "util/debug.h"
#include "util/buffer.h"
#include "util/thread.h"
#include "library/trace.h"

namespace lean {
// TODO(Leo) add compilation flag for enabling this trace message
#define lean_array_trace(CODE) lean_trace(name({"array", "update"}), CODE)

template<typename T, bool ThreadSafe = false>
class parray {
    enum cell_kind { Set, PushBack, PopBack, Root };

    static size_t capacity(T * vs) {
        return vs == nullptr ? 0 : (reinterpret_cast<size_t*>(vs))[-1];
    }

    static T * allocate_raw_array(size_t c) {
        size_t * mem = static_cast<size_t*>(malloc(sizeof(T)*c + sizeof(size_t)));
        *mem = c;
        ++mem;
        T * r = reinterpret_cast<T*>(mem);
        lean_assert(capacity(r) == c);
        return r;
    }

    static void deallocate_raw_array(T * vs) {
        if (vs == nullptr)
            return;
        size_t * mem = reinterpret_cast<size_t*>(vs);
        --mem;
        free(mem);
    }

    static void deallocate_array(T * vs, size_t sz) {
        std::for_each(vs, vs + sz, [](T & e) { e.~T(); });
        deallocate_raw_array(vs);
    }

    static T * expand(T * vs, size_t sz) {
        size_t curr_capacity = capacity(vs);
        size_t new_capacity  = curr_capacity == 0 ? 2 : (3 * curr_capacity + 1) >> 1;
        T * new_vs           = allocate_raw_array(new_capacity);
        std::uninitialized_copy(vs, vs + sz, new_vs);
        deallocate_array(vs, sz);
        return new_vs;
    }

    struct cell {
        atomic<unsigned> m_rc;
        cell_kind        m_kind;
        union {
            size_t       m_idx;
            size_t       m_size;
        };
        cell  *          m_next;
        union {
            T *          m_values; /* If m_kind == Root */
            T *          m_elem; /* If m_kind == PushBack or m_kind == Set */
        };

        cell_kind kind() const { return static_cast<cell_kind>(m_kind); }
        unsigned idx() const { lean_assert(kind() != Root); return m_idx; }
        unsigned size() const { lean_assert(kind() == Root); return m_size; }
        cell * next() const { lean_assert(kind() != Root); return m_next; }
        T const & elem() const { lean_assert(kind() == Set || kind() == PushBack); return *m_elem; }

        mutex ** get_mutex_field_addr() {
            return reinterpret_cast<mutex**>(reinterpret_cast<char*>(this) + sizeof(cell));
        }

        mutex * get_mutex() { return *get_mutex_field_addr(); }

        void set_mutex(mutex * m) { *get_mutex_field_addr() = m; }

        cell():m_rc(1), m_kind(Root), m_size(0), m_values(nullptr) {}
    };

    static memory_pool & get_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(sizeof(cell) + (ThreadSafe ? sizeof(mutex*) : 0)); // NOLINT
        return *g_allocator;
    }

    static memory_pool & get_elem_allocator() {
        LEAN_THREAD_PTR(memory_pool, g_allocator);
        if (!g_allocator)
            g_allocator = allocate_thread_memory_pool(std::max(sizeof(T), sizeof(size_t)));
        return *g_allocator;
    }

    static void del_elem(T * ptr) {
        ptr->~T();
        get_elem_allocator().recycle(ptr);
    }

    static void deallocate_cell(cell * c) {
        while (true) {
            cell * next = nullptr;
            switch (c->kind()) {
            case Set:
            case PushBack:
                del_elem(c->m_elem);
                next = c->next();
                break;
            case PopBack:
                next = c->next();
                break;
            case Root:
                deallocate_array(c->m_values, c->m_size);
                if (ThreadSafe)
                    delete c->get_mutex();
                break;
            }
            c->~cell();
            get_allocator().recycle(c);
            if (next == nullptr)
                return;
            lean_assert(next->m_rc > 0);
            next->m_rc--;
            if (next->m_rc > 0)
                return;
            c = next;
        }
    }

    static unsigned get_rc(cell * c) {
        if (ThreadSafe)
            return atomic_load(&c->m_rc);
        else
            return c->m_rc;
    }

    static void inc_ref(cell * c) {
        if (c == nullptr) return;
        if (ThreadSafe)
            atomic_fetch_add_explicit(&c->m_rc, 1u, memory_order_relaxed);
        else
            c->m_rc++;
    }

    static void dec_ref(cell * c) {
        if (c == nullptr) return;
        lean_assert(get_rc(c) > 0);
        if (ThreadSafe) {
            if (atomic_fetch_sub_explicit(&c->m_rc, 1u, memory_order_release) == 1u) {
                atomic_thread_fence(memory_order_acquire);
                deallocate_cell(c);
            }
        } else {
            c->m_rc--;
            if (c->m_rc == 0)
                deallocate_cell(c);
        }
    }

    static cell * mk_cell() {
        return new (get_allocator().allocate()) cell();
    }

    static T * mk_elem_copy(T const & e) {
        return new (get_elem_allocator().allocate()) T(e);
    }

    typedef buffer<cell *, 1024> cell_buffer;

    static cell * collect_cells(cell * r, cell_buffer & cs) {
        cell * c   = r;
        while (c->kind() != Root) {
            cs.push_back(c);
            c = c->next();
        }
        return c;
    }

    /* Given r -> ... -> c  where cs is the path from r to c,
       revert links, i.e., update it to r <- ... <- c */
    static void reroot(cell * r, cell * c, cell_buffer const & cs) {
        lean_assert(c->m_kind == Root);
        cell * last = c;
        size_t sz   = c->m_size;
        T * vs      = c->m_values;
        unsigned i  = cs.size();
        while (i > 0) {
            --i;
            cell * p = cs[i];
            lean_assert(p->m_kind != Root);
            lean_assert(p->m_next == c);
            switch (p->kind()) {
            case Set:
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem  = mk_elem_copy(vs[p->m_idx]);
                } else {
                    *c->m_elem = vs[p->m_idx];
                }
                c->m_kind    = Set;
                c->m_idx     = p->m_idx;
                vs[p->m_idx] = p->elem();
                break;
            case PushBack:
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem = nullptr;
                } else {
                    del_elem(c->m_elem);
                }
                c->m_kind = PopBack;
                if (sz == capacity(vs))
                    vs = expand(vs, sz);
                c->m_idx  = sz;
                new (vs + sz) T(p->elem());
                sz++;
                break;
            case PopBack:
                --sz;
                if (c->m_kind == PopBack || c->m_kind == Root) {
                    c->m_elem  = mk_elem_copy(vs[sz]);
                } else {
                    *c->m_elem = vs[sz];
                }
                (vs + sz)->~T();
                c->m_kind = PushBack;
                c->m_idx  = sz;
                break;
            case Root:
                lean_unreachable();
                break;
            }
            c->m_next   = p;
            c = p;
        }
        lean_assert(c == r);
        if (r->m_kind == Set || r->m_kind == PushBack) {
            del_elem(r->m_elem);
        }
        lean_assert(r != last);
        lean_assert(last->m_kind != Root);
        r->m_kind   = Root;
        r->m_values = vs;
        r->m_size   = sz;
        DEBUG_CODE({
                cell * it = last;
                while (it->m_kind != Root) {
                    it = it->m_next;
                }
                lean_assert(it == r);
            });
        lean_assert(r->m_kind == Root);
        inc_ref(r);
        dec_ref(last);
        lean_assert(r->m_kind == Root);
    }

    /* Given a path cs to c,
       create a copy of the vector applying the operations occurring after >= from_idx. */
    static cell * copy(unsigned from_idx, cell * c, cell_buffer const & cs) {
        lean_assert(from_idx <= cs.size());
        cell * r    = mk_cell();
        lean_assert(r->m_kind == Root);
        r->m_rc     = 0;
        r->m_size   = c->m_size;
        r->m_values = allocate_raw_array(capacity(c->m_values));
        if (ThreadSafe)
            r->set_mutex(new mutex());
        std::uninitialized_copy(c->m_values, c->m_values + c->m_size, r->m_values);
        unsigned i  = cs.size();
        while (i > from_idx) {
            --i;
            cell * p = cs[i];
            lean_assert(p->kind() != Root);
            lean_assert(p->m_next == c);
            switch (p->kind()) {
            case Set:
                r->m_values[p->m_idx] = p->elem();
                break;
            case PushBack:
                if (r->m_size == capacity(r->m_values))
                    r->m_values = expand(r->m_values, r->m_size);
                new (r->m_values + r->m_size) T(p->elem());
                r->m_size++;
                break;
            case PopBack:
                r->m_size--;
                (r->m_values + r->m_size)->~T();
                break;
            case Root:
                lean_unreachable();
                break;
            }
            DEBUG_CODE(c = p;);
        }
        lean_assert(r->m_kind == Root);
        return r;
    }

    /* Return the size of the array after applying operations in cs to c */
    static size_t get_size(cell * c, cell_buffer const & cs) {
        lean_assert(c->m_kind == Root);
        size_t r = c->m_size;
        unsigned i = cs.size();
        while (i > 0) {
            --i;
            switch (cs[i]->m_kind) {
            case PushBack:  r++; break;
            case PopBack:   r--; break;
            case Set:       break;
            case Root:      lean_unreachable();
            }
        }
        return r;
    }

    static bool should_split(size_t sz, size_t num_ops) {
        return num_ops > 4 && 2 * sz < 3 * num_ops;
    }

    static void reroot(cell * r) {
        lean_assert(get_rc(r) > 0);
        lean_assert(r->kind() != Root);
        cell_buffer cs;
        cell * c    = collect_cells(r, cs);
        if (!ThreadSafe &&
            /* Should we keep this optimization? */
            should_split(c->size(), cs.size()) &&
            should_split(get_size(c, cs), cs.size())) {
            /* Split the path r -> ... -> m_1 -> m_2 -> ... -> c in two

               1) r <- ... <- m_1
               2) m_2 -> ... -> c

               This operation is not safe when ThreadSafe == true.
               In ThreadSafe mode, each cell contains a reference to
               the mutex stored in the Root cell, but we don't know
               all cells that point to a Root cell.
            */
            unsigned midx = cs.size() / 2;
            DEBUG_CODE(cell * m = cs[midx];);
            cell * new_m = copy(midx, c, cs);
            inc_ref(new_m);
            cs.resize(midx);
            lean_assert(cs.back()->m_next == m);
            dec_ref(cs.back()->m_next);
            cs.back()->m_next = new_m;
            lean_assert(midx > 0);
            reroot(r, new_m, cs);
        } else {
            reroot(r, c, cs);
        }
        lean_assert(r->kind() == Root);
    }

    static cell * ensure_unshared_aux(cell * c) {
        cell_buffer cs;
        c = collect_cells(c, cs);
        return copy(0, c, cs);
    }

    static cell * ensure_unshared(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root)
            return c;
        if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            return ensure_unshared_aux(c);
        } else {
            return ensure_unshared_aux(c);
        }
    }

    static T const & read_aux(cell * c, size_t i) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        lean_assert(i < c->size());
        return c->m_values[i];
    }

    static T read(cell * c, size_t i) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_assert(i < c->size());
            return c->m_values[i];
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            return read_aux(c, i);
        } else {
            return read_aux(c, i);
        }
    }

    static size_t size(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            return c->size();
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            if (c->kind() != Root)
                reroot(c);
            return c->size();
        } else {
            if (c->kind() != Root)
                reroot(c);
            return c->size();
        }
    }

    static cell * write_aux(cell * c, size_t i, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(i < c->size());
        if (get_rc(c) == 1) {
            c->m_values[i] = v;
            return c;
        } else {
            lean_array_trace(tout() << "non-destructive write at #" << i << "\n";);
            lean_assert(c->kind() == Root);
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            if (ThreadSafe)
                new_cell->set_mutex(c->get_mutex());
            c->m_kind             = Set;
            c->m_idx              = i;
            c->m_elem             = mk_elem_copy(new_cell->m_values[i]);
            c->m_next             = new_cell;
            /* It is safe to update m_rc directly here because
               we are protected by a semaphore */
            c->m_rc--;
            new_cell->m_rc++;
            new_cell->m_values[i] = v;
            return new_cell;
        }
    }

    static cell * write(cell * c, size_t i, T const & v) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_array_trace(tout() << "destructive write at #" << i << "\n";);
            lean_assert(i < c->size());
            c->m_values[i] = v;
            return c;
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            return write_aux(c, i, v);
        } else {
            return write_aux(c, i, v);
        }
    }

    static void push_back_core(cell * c, T const & v) {
        if (c->m_size == capacity(c->m_values))
            c->m_values = expand(c->m_values, c->m_size);
        new (c->m_values + c->m_size) T(v);
        c->m_size++;
    }

    static cell * push_back_aux(cell * c, T const & v) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        if (get_rc(c) == 1) {
            push_back_core(c, v);
            return c;
        }
        lean_array_trace(tout() << "non-destructive push_back\n";);
        cell * new_cell       = mk_cell();
        new_cell->m_values    = c->m_values;
        new_cell->m_size      = c->m_size;
        if (ThreadSafe)
            new_cell->set_mutex(c->get_mutex());
        c->m_kind             = PopBack;
        c->m_next             = new_cell;
        c->m_elem             = nullptr;
        /* It is safe to update m_rc directly here because
           we are protected by a semaphore */
        c->m_rc--;
        new_cell->m_rc++;
        push_back_core(new_cell, v);
        return new_cell;
    }

    static cell * push_back(cell * c, T const & v) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_array_trace(tout() << "destructive push_back\n";);
            push_back_core(c, v);
            return c;
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            return push_back_aux(c, v);
        } else {
            return push_back_aux(c, v);
        }
    }

    static void pop_back_core(cell * c) {
        lean_assert(c->m_size > 0);
        c->m_size--;
        c->m_values[c->m_size].~T();
    }

    static cell * pop_back_aux(cell * c) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        lean_assert(c->m_size > 0);
        if (get_rc(c) == 1) {
            pop_back_core(c);
            return c;
        } else {
            lean_array_trace(tout() << "non-destructive pop_back\n";);
            cell * new_cell       = mk_cell();
            new_cell->m_values    = c->m_values;
            new_cell->m_size      = c->m_size;
            if (ThreadSafe)
                new_cell->set_mutex(c->get_mutex());
            c->m_kind             = PushBack;
            c->m_elem             = mk_elem_copy(new_cell->m_values[c->m_size - 1]);
            c->m_next             = new_cell;
            /* It is safe to update m_rc directly here because
               we are protected by a semaphore */
            c->m_rc--;
            new_cell->m_rc++;
            pop_back_core(new_cell);
            return new_cell;
        }
    }

    static cell * pop_back(cell * c) {
        if (get_rc(c) == 1 && c->kind() == Root) {
            lean_assert(c->m_size > 0);
            lean_array_trace(tout() << "destructive pop_back\n";);
            pop_back_core(c);
            return c;
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*c->get_mutex());
            return pop_back_aux(c);
        } else {
            return pop_back_aux(c);
        }
    }

    template<typename F>
    static void for_each(cell * c, F && fn) {
        if (c->kind() != Root)
            reroot(c);
        lean_assert(c->kind() == Root);
        size_t sz = c->m_size;
        for (size_t i = 0; i < sz; i++) {
            fn(c->m_values[i]);
        }
    }

    void init() {
        lean_assert(m_cell->m_kind == Root);
        if (ThreadSafe)
            m_cell->set_mutex(new mutex());
    }

    cell * m_cell;
public:
    parray():m_cell(mk_cell()) { init(); }
    parray(size_t sz, T const & v):m_cell(mk_cell()) {
        m_cell->m_size   = sz;
        m_cell->m_values = allocate_raw_array(sz);
        std::uninitialized_fill(m_cell->m_values, m_cell->m_values + sz, v);
        init();
    }
    parray(parray const & s):m_cell(s.m_cell) { if (m_cell) inc_ref(m_cell); }
    parray(parray && s):m_cell(s.m_cell) { s.m_cell = nullptr; }
    ~parray() { if (m_cell) dec_ref(m_cell); }

    parray & operator=(parray const & s) {
        if (s.m_cell)
            inc_ref(s.m_cell);
        cell * new_cell = s.m_cell;
        if (m_cell)
            dec_ref(m_cell);
        m_cell = new_cell;
        return *this;
    }

    parray & operator=(parray && s) {
        if (m_cell)
            dec_ref(m_cell);
        m_cell = s.m_ptr;
        s.m_ptr = nullptr;
        return *this;
    }

    size_t size() const {
        return size(m_cell);
    }

    T operator[](size_t i) const {
        return read(m_cell, i);
    }

    void set(size_t i, T const & v) {
        m_cell = write(m_cell, i, v);
    }

    void push_back(T const & v) {
        m_cell = push_back(m_cell, v);
    }

    void pop_back() {
        m_cell = pop_back(m_cell);
    }

    void ensure_unshared() {
        cell * new_cell = ensure_unshared(m_cell);
        inc_ref(new_cell);
        dec_ref(m_cell);
        m_cell = new_cell;
        lean_assert(get_rc(m_cell) == 1 && m_cell->m_kind == Root);
    }

    unsigned get_rc() const {
        return m_cell->m_rc;
    }

    static unsigned sizeof_cell() {
        return get_allocator().obj_size();
    }

    friend void swap(parray & a1, parray & a2) {
        std::swap(a1.m_cell, a2.m_cell);
    }

    template<typename F>
    void for_each(F && fn) const {
        if (get_rc(m_cell) == 1 && m_cell->m_kind == Root) {
            for_each(m_cell, fn);
        } else if (ThreadSafe) {
            lock_guard<mutex> lock(*m_cell->get_mutex());
            for_each(m_cell, fn);
        } else {
            for_each(m_cell, fn);
        }
    }

    class exclusive_access {
        parray<T, ThreadSafe> & m_array;

        bool check_invariant() const {
            lean_assert(m_array.m_cell->m_kind == Root);
            return true;
        }

    public:
        exclusive_access(parray<T, ThreadSafe> & a):m_array(a) {
            if (ThreadSafe)
                m_array.m_cell->get_mutex()->lock();
            if (m_array.m_cell->m_kind != Root)
                reroot(m_array.m_cell);
            lean_assert(m_array.m_cell->m_kind == Root);
        }

        ~exclusive_access() {
            if (ThreadSafe)
                m_array.m_cell->get_mutex()->unlock();
        }

        unsigned size() const {
            lean_assert(check_invariant());
            return m_array.m_cell->m_size;
        }

        T const & operator[](size_t i) const {
            lean_assert(check_invariant());
            lean_assert(i < size());
            return m_array.m_cell->m_values[i];
        }

        void set(size_t i, T const & v) {
            lean_assert(check_invariant());
            lean_assert(i < size());
            m_array.m_cell = write_aux(m_array.m_cell, i, v);
            lean_assert(check_invariant());
        }
    };
};
void initialize_parray();
void finalize_parray();
}




// ========== parray.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
namespace lean {
void initialize_parray() {
    register_trace_class(name{"array", "update"});
}
void finalize_parray() {
}
}




// ========== handle.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author:  Leonardo de Moura & Jared Roesch
*/
#pragma once

#include <string>
#include <stdio.h>
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean {

class handle_exception : exception {
public:
    handle_exception(std::string msg) : exception(msg) {}
};

class handle {
public:
    FILE * m_file;
    bool m_binary;
    handle(FILE * file_desc, bool binary):m_file(file_desc), m_binary(binary) {}

    void close();

    ~handle();

    void write(buffer<char> & data);
    void flush();

    bool is_stdin();
    bool is_stdout();
    bool is_stderr();
    bool is_closed();
};

typedef std::shared_ptr<handle> handle_ref;

}




// ========== handle.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author:  Leonardo de Moura & Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <stdio.h>

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
#include <windows.h>
#include <tchar.h>
#include <strsafe.h>
#else
#include <sys/wait.h>
#include <unistd.h>
#endif

#include "library/process.h"
#include "library/handle.h"
#include "util/buffer.h"
#include "library/pipe.h"


namespace lean {

void handle::write(buffer<char> & buf) {
    auto sz = buf.size();
    if (fwrite(buf.data(), 1, sz, m_file) != sz) {
        std::cout << "write_error: " << errno << std::endl;
        clearerr(m_file);
        throw handle_exception("write failed");
    }
}

void handle::flush() {
    if (fflush(m_file) != 0) {
        clearerr(m_file);
        throw handle_exception("flush failed");
    }
}

handle::~handle() {
    if (m_file && m_file != stdin &&
        m_file != stderr && m_file != stdout) {
        fclose(m_file);
        m_file = nullptr;
    }
}

bool handle::is_stdin() {
    return m_file == stdin;
}

bool handle::is_stdout() {
    return m_file == stdout;
}

bool handle::is_stderr() {
    return m_file == stderr;
}

void handle::close() {
    if (m_file == nullptr) {
        // double close
    } else if (fclose(m_file) == 0) {
        m_file = nullptr;
    } else {
        clearerr(m_file);
        throw handle_exception("close failed");
    }
}

bool handle::is_closed() { return !m_file; }

}




// ========== pp_options.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"
namespace lean {
name const & get_pp_implicit_name();
name const & get_pp_proofs_name();
name const & get_pp_coercions_name();
name const & get_pp_full_names_name();
name const & get_pp_universes_name();
name const & get_pp_notation_name();
name const & get_pp_purify_metavars_name();
name const & get_pp_purify_locals_name();
name const & get_pp_locals_full_names_name();
name const & get_pp_beta_name();
name const & get_pp_preterm_name();
name const & get_pp_numerals_name();
name const & get_pp_strings_name();
name const & get_pp_binder_types_name();
name const & get_pp_use_holes_name();

unsigned get_pp_max_depth(options const & opts);
unsigned get_pp_max_steps(options const & opts);
bool     get_pp_notation(options const & opts);
bool     get_pp_implicit(options const & opts);
bool     get_pp_proofs(options const & opts);
bool     get_pp_coercions(options const & opts);
bool     get_pp_universes(options const & opts);
bool     get_pp_full_names(options const & opts);
bool     get_pp_private_names(options const & opts);
bool     get_pp_beta(options const & opts);
bool     get_pp_purify_metavars(options const & opts);
bool     get_pp_purify_locals(options const & opts);
bool     get_pp_locals_full_names(options const & opts);
bool     get_pp_numerals(options const & opts);
bool     get_pp_strings(options const & opts);
bool     get_pp_preterm(options const & opts);
bool     get_pp_goal_compact(options const & opts);
unsigned get_pp_goal_max_hyps(options const & opts);
bool     get_pp_binder_types(options const & opts);
bool     get_pp_hide_comp_irrel(options const & opts);
bool     get_pp_delayed_abstraction(options const & opts);
bool     get_pp_structure_instances(options const & opts);
bool     get_pp_structure_instances_qualifier(options const & opts);
bool     get_pp_structure_projections(options const & opts);
bool     get_pp_instantiate_mvars(options const & o);
bool     get_pp_use_holes(options const & o);
bool     get_pp_annotations(options const & o);
bool     get_pp_all(options const & opts);

void initialize_pp_options();
void finalize_pp_options();
}




// ========== pp_options.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/error_msgs.h"
#include "library/pp_options.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH 64
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS 5000
#endif

#ifndef LEAN_DEFAULT_PP_NOTATION
#define LEAN_DEFAULT_PP_NOTATION true
#endif

#ifndef LEAN_DEFAULT_PP_IMPLICIT
#define LEAN_DEFAULT_PP_IMPLICIT false
#endif

#ifndef LEAN_DEFAULT_PP_PROOFS
#define LEAN_DEFAULT_PP_PROOFS true
#endif

#ifndef LEAN_DEFAULT_PP_COERCIONS
#define LEAN_DEFAULT_PP_COERCIONS true
#endif

#ifndef LEAN_DEFAULT_PP_UNIVERSES
#define LEAN_DEFAULT_PP_UNIVERSES false
#endif

#ifndef LEAN_DEFAULT_PP_FULL_NAMES
#define LEAN_DEFAULT_PP_FULL_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_PRIVATE_NAMES
#define LEAN_DEFAULT_PP_PRIVATE_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_PURIFY_METAVARS
#define LEAN_DEFAULT_PP_PURIFY_METAVARS true
#endif

#ifndef LEAN_DEFAULT_PP_PURIFY_LOCALS
#define LEAN_DEFAULT_PP_PURIFY_LOCALS true
#endif

#ifndef LEAN_DEFAULT_PP_LOCALS_FULL_NAMES
#define LEAN_DEFAULT_PP_LOCALS_FULL_NAMES false
#endif

#ifndef LEAN_DEFAULT_PP_BETA
#define LEAN_DEFAULT_PP_BETA false
#endif

#ifndef LEAN_DEFAULT_PP_NUMERALS
#define LEAN_DEFAULT_PP_NUMERALS true
#endif

#ifndef LEAN_DEFAULT_PP_STRINGSS
#define LEAN_DEFAULT_PP_STRINGS true
#endif

#ifndef LEAN_DEFAULT_PP_PRETERM
#define LEAN_DEFAULT_PP_PRETERM false
#endif

#ifndef LEAN_DEFAULT_PP_GOAL_COMPACT
#define LEAN_DEFAULT_PP_GOAL_COMPACT false
#endif

#ifndef LEAN_DEFAULT_PP_GOAL_MAX_HYPS
#define LEAN_DEFAULT_PP_GOAL_MAX_HYPS 200
#endif

#ifndef LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT
#define LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT true
#endif

#ifndef LEAN_DEFAULT_PP_BINDER_TYPES
#define LEAN_DEFAULT_PP_BINDER_TYPES true
#endif

#ifndef LEAN_DEFAULT_PP_DELAYED_ABSTRACTION
#define LEAN_DEFAULT_PP_DELAYED_ABSTRACTION true
#endif

#ifndef LEAN_DEFAULT_PP_ALL
#define LEAN_DEFAULT_PP_ALL false
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_INSTANCES
#define LEAN_DEFAULT_PP_STRUCTURE_INSTANCES true
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER
#define LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER false
#endif

#ifndef LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS
#define LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS true
#endif

#ifndef LEAN_DEFAULT_PP_INSTANTIATE_MVARS
#define LEAN_DEFAULT_PP_INSTANTIATE_MVARS true
#endif

#ifndef LEAN_DEFAULT_PP_USE_HOLES
#define LEAN_DEFAULT_PP_USE_HOLES false
#endif

#ifndef LEAN_DEFAULT_PP_ANNOTATIONS
#define LEAN_DEFAULT_PP_ANNOTATIONS false
#endif

namespace lean {
static name * g_pp_max_depth         = nullptr;
static name * g_pp_max_steps         = nullptr;
static name * g_pp_notation          = nullptr;
static name * g_pp_implicit          = nullptr;
static name * g_pp_proofs            = nullptr;
static name * g_pp_coercions         = nullptr;
static name * g_pp_universes         = nullptr;
static name * g_pp_full_names        = nullptr;
static name * g_pp_private_names     = nullptr;
static name * g_pp_purify_metavars   = nullptr;
static name * g_pp_purify_locals     = nullptr;
static name * g_pp_locals_full_names = nullptr;
static name * g_pp_beta              = nullptr;
static name * g_pp_numerals          = nullptr;
static name * g_pp_strings           = nullptr;
static name * g_pp_preterm           = nullptr;
static name * g_pp_goal_compact      = nullptr;
static name * g_pp_goal_max_hyps     = nullptr;
static name * g_pp_binder_types      = nullptr;
static name * g_pp_hide_comp_irrel   = nullptr;
static name * g_pp_delayed_abstraction = nullptr;
static name * g_pp_structure_instances = nullptr;
static name * g_pp_structure_instances_qualifier = nullptr;
static name * g_pp_structure_projections    = nullptr;
static name * g_pp_instantiate_mvars = nullptr;
static name * g_pp_use_holes         = nullptr;
static name * g_pp_annotations       = nullptr;
static name * g_pp_all               = nullptr;
static list<options> * g_distinguishing_pp_options = nullptr;

void initialize_pp_options() {
    g_pp_max_depth         = new name{"pp", "max_depth"};
    g_pp_max_steps         = new name{"pp", "max_steps"};
    g_pp_notation          = new name{"pp", "notation"};
    g_pp_implicit          = new name{"pp", "implicit"};
    g_pp_proofs            = new name{"pp", "proofs"};
    g_pp_coercions         = new name{"pp", "coercions"};
    g_pp_universes         = new name{"pp", "universes"};
    g_pp_full_names        = new name{"pp", "full_names"};
    g_pp_private_names     = new name{"pp", "private_names"};
    g_pp_purify_metavars   = new name{"pp", "purify_metavars"};
    g_pp_purify_locals     = new name{"pp", "purify_locals"};
    g_pp_locals_full_names = new name{"pp", "locals_full_names"};
    g_pp_beta              = new name{"pp", "beta"};
    g_pp_numerals          = new name{"pp", "numerals"};
    g_pp_strings           = new name{"pp", "strings"};
    g_pp_preterm           = new name{"pp", "preterm"};
    g_pp_binder_types      = new name{"pp", "binder_types"};
    g_pp_hide_comp_irrel   = new name{"pp", "hide_comp_irrelevant"};
    g_pp_all               = new name{"pp", "all"};
    g_pp_delayed_abstraction  = new name{"pp", "delayed_abstraction"};
    g_pp_goal_compact      = new name{"pp", "goal", "compact"};
    g_pp_goal_max_hyps     = new name{"pp", "goal", "max_hypotheses"};
    g_pp_structure_instances = new name{"pp", "structure_instances"};
    g_pp_structure_instances_qualifier = new name{"pp", "structure_instances_qualifier"};
    g_pp_structure_projections = new name{"pp", "structure_projections"};
    g_pp_instantiate_mvars = new name{"pp", "instantiate_mvars"};
    g_pp_use_holes         = new name{"pp", "use_holes"};
    g_pp_annotations       = new name{"pp", "annotations"};

    register_unsigned_option(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH,
                             "(pretty printer) maximum expression depth, after that it will use ellipsis");
    register_unsigned_option(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS,
                             "(pretty printer) maximum number of visited expressions, after that it will use ellipsis");
    register_bool_option(*g_pp_notation,  LEAN_DEFAULT_PP_NOTATION,
                         "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
    register_bool_option(*g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT,
                         "(pretty printer) display implicit parameters");
    register_bool_option(*g_pp_proofs,  LEAN_DEFAULT_PP_PROOFS,
                         "(pretty printer) if set to false, the type will be displayed instead of the value for every proof appearing as an argument to a function");
    register_bool_option(*g_pp_coercions,  LEAN_DEFAULT_PP_COERCIONS,
                         "(pretty printer) display coercionss");
    register_bool_option(*g_pp_universes,  LEAN_DEFAULT_PP_UNIVERSES,
                         "(pretty printer) display universes");
    register_bool_option(*g_pp_full_names,  LEAN_DEFAULT_PP_FULL_NAMES,
                         "(pretty printer) display fully qualified names");
    register_bool_option(*g_pp_private_names,  LEAN_DEFAULT_PP_PRIVATE_NAMES,
                         "(pretty printer) display internal names assigned to private declarations");
    register_bool_option(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS,
                         "(pretty printer) rename internal metavariable names (with \"user-friendly\" ones) "
                         "before pretty printing");
    register_bool_option(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS,
                         "(pretty printer) rename local names to avoid name capture, "
                         "before pretty printing");
    register_bool_option(*g_pp_locals_full_names, LEAN_DEFAULT_PP_LOCALS_FULL_NAMES,
                         "(pretty printer) show full names of locals");
    register_bool_option(*g_pp_beta,  LEAN_DEFAULT_PP_BETA,
                         "(pretty printer) apply beta-reduction when pretty printing");
    register_bool_option(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS,
                         "(pretty printer) display nat/num numerals in decimal notation");
    register_bool_option(*g_pp_strings, LEAN_DEFAULT_PP_STRINGS,
                         "(pretty printer) pretty print string and character literals");
    register_bool_option(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM,
                         "(pretty printer) assume the term is a preterm (i.e., a term before elaboration)");
    register_bool_option(*g_pp_goal_compact, LEAN_DEFAULT_PP_GOAL_COMPACT,
                         "(pretty printer) try to display goal in a single line when possible");
    register_unsigned_option(*g_pp_goal_max_hyps, LEAN_DEFAULT_PP_GOAL_MAX_HYPS,
                             "(pretty printer) maximum number of hypotheses to be displayed");
    register_bool_option(*g_pp_hide_comp_irrel, LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT,
                         "(pretty printer) hide terms marked as computationally irrelevant, these marks are introduced by the code generator");
    register_bool_option(*g_pp_binder_types, LEAN_DEFAULT_PP_BINDER_TYPES,
                         "(pretty printer) display types of lambda and Pi parameters");
    register_bool_option(*g_pp_delayed_abstraction, LEAN_DEFAULT_PP_DELAYED_ABSTRACTION,
                         "(pretty printer) display the location of delayed-abstractions (for debugging purposes)");
    register_bool_option(*g_pp_structure_instances, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES,
                         "(pretty printer) display structure instances using the '{ field_name := field_value, ... }' notation "
                         "or '⟨field_value, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute");
    register_bool_option(*g_pp_structure_instances_qualifier, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER,
                         "(pretty printer) include qualifier 'struct_name .' "
                         "when displaying structure instances using the '{ struct_name . field_name := field_value, ... }' notation, "
                         "this option is ignored when pp.structure_instances is false");
    register_bool_option(*g_pp_structure_projections, LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS,
                         "(pretty printer) display structure projections using field notation");
    register_bool_option(*g_pp_all, LEAN_DEFAULT_PP_ALL,
                         "(pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universes, "
                         "and disable beta reduction and notation during pretty printing");
    register_bool_option(*g_pp_instantiate_mvars, LEAN_DEFAULT_PP_INSTANTIATE_MVARS,
                         "(pretty printer) instantiate assigned metavariables before pretty printing terms and goals");
    register_bool_option(*g_pp_use_holes, LEAN_DEFAULT_PP_USE_HOLES,
                         "(pretty printer) use holes '{! !}' when pretty printing metavariables and `sorry`");
    register_bool_option(*g_pp_annotations, LEAN_DEFAULT_PP_ANNOTATIONS,
                         "(pretty printer) display internal annotations (for debugging purposes only)");

    options universes_true(*g_pp_universes, true);
    options full_names_true(*g_pp_full_names, true);
    options implicit_true(*g_pp_implicit, true);
    options proofs_true(*g_pp_proofs, true);
    options coercions_true(*g_pp_coercions, true);
    options notation_false(*g_pp_notation, false);
    options binder_types_true(*g_pp_binder_types, true);
    options implicit_coercions = join(coercions_true, implicit_true);
    options implicit_notation  = join(notation_false, implicit_true);
    options all = universes_true + implicit_true + proofs_true + coercions_true + notation_false + full_names_true + binder_types_true;
    g_distinguishing_pp_options = new list<options>({implicit_true, full_names_true, coercions_true, implicit_coercions,
                implicit_notation, universes_true, all});

    set_distinguishing_pp_options(*g_distinguishing_pp_options);
}

void finalize_pp_options() {
    delete g_pp_preterm;
    delete g_pp_numerals;
    delete g_pp_strings;
    delete g_pp_max_depth;
    delete g_pp_max_steps;
    delete g_pp_notation;
    delete g_pp_implicit;
    delete g_pp_proofs;
    delete g_pp_coercions;
    delete g_pp_universes;
    delete g_pp_full_names;
    delete g_pp_private_names;
    delete g_pp_purify_metavars;
    delete g_pp_purify_locals;
    delete g_pp_locals_full_names;
    delete g_pp_beta;
    delete g_pp_goal_compact;
    delete g_pp_goal_max_hyps;
    delete g_pp_binder_types;
    delete g_pp_hide_comp_irrel;
    delete g_pp_structure_instances;
    delete g_pp_structure_instances_qualifier;
    delete g_pp_structure_projections;
    delete g_pp_all;
    delete g_pp_delayed_abstraction;
    delete g_pp_instantiate_mvars;
    delete g_pp_use_holes;
    delete g_pp_annotations;
    delete g_distinguishing_pp_options;
}

name const & get_pp_implicit_name() { return *g_pp_implicit; }
name const & get_pp_proofs_name() { return *g_pp_proofs; }
name const & get_pp_coercions_name() { return *g_pp_coercions; }
name const & get_pp_full_names_name() { return *g_pp_full_names; }
name const & get_pp_universes_name() { return *g_pp_universes; }
name const & get_pp_notation_name() { return *g_pp_notation; }
name const & get_pp_purify_metavars_name() { return *g_pp_purify_metavars; }
name const & get_pp_purify_locals_name() { return *g_pp_purify_locals; }
name const & get_pp_locals_full_names_name() { return *g_pp_locals_full_names; }
name const & get_pp_beta_name() { return *g_pp_beta; }
name const & get_pp_preterm_name() { return *g_pp_preterm; }
name const & get_pp_numerals_name() { return *g_pp_numerals; }
name const & get_pp_strings_name() { return *g_pp_strings; }
name const & get_pp_use_holes_name() { return *g_pp_use_holes; }
name const & get_pp_binder_types_name() { return *g_pp_binder_types; }

unsigned get_pp_max_depth(options const & opts)         { return opts.get_unsigned(*g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)         { return opts.get_unsigned(*g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_notation(options const & opts)          { return opts.get_bool(*g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_implicit(options const & opts)          { return opts.get_bool(*g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_proofs(options const & opts)            { return opts.get_bool(*g_pp_proofs, LEAN_DEFAULT_PP_PROOFS); }
bool     get_pp_coercions(options const & opts)         { return opts.get_bool(*g_pp_coercions, LEAN_DEFAULT_PP_COERCIONS); }
bool     get_pp_universes(options const & opts)         { return opts.get_bool(*g_pp_universes, LEAN_DEFAULT_PP_UNIVERSES); }
bool     get_pp_full_names(options const & opts)        { return opts.get_bool(*g_pp_full_names, LEAN_DEFAULT_PP_FULL_NAMES); }
bool     get_pp_private_names(options const & opts)     { return opts.get_bool(*g_pp_private_names, LEAN_DEFAULT_PP_PRIVATE_NAMES); }
bool     get_pp_purify_metavars(options const & opts)   { return opts.get_bool(*g_pp_purify_metavars, LEAN_DEFAULT_PP_PURIFY_METAVARS); }
bool     get_pp_purify_locals(options const & opts)     { return opts.get_bool(*g_pp_purify_locals, LEAN_DEFAULT_PP_PURIFY_LOCALS); }
bool     get_pp_locals_full_names(options const & opts) { return opts.get_bool(*g_pp_locals_full_names, LEAN_DEFAULT_PP_LOCALS_FULL_NAMES); }
bool     get_pp_beta(options const & opts)              { return opts.get_bool(*g_pp_beta, LEAN_DEFAULT_PP_BETA); }
bool     get_pp_numerals(options const & opts)          { return opts.get_bool(*g_pp_numerals, LEAN_DEFAULT_PP_NUMERALS); }
bool     get_pp_strings(options const & opts)           { return opts.get_bool(*g_pp_strings, LEAN_DEFAULT_PP_STRINGS); }
bool     get_pp_preterm(options const & opts)           { return opts.get_bool(*g_pp_preterm, LEAN_DEFAULT_PP_PRETERM); }
bool     get_pp_goal_compact(options const & opts)      { return opts.get_bool(*g_pp_goal_compact, LEAN_DEFAULT_PP_GOAL_COMPACT); }
unsigned get_pp_goal_max_hyps(options const & opts)     { return opts.get_unsigned(*g_pp_goal_max_hyps, LEAN_DEFAULT_PP_GOAL_MAX_HYPS); }
bool     get_pp_binder_types(options const & opts)      { return opts.get_bool(*g_pp_binder_types, LEAN_DEFAULT_PP_BINDER_TYPES); }
bool     get_pp_hide_comp_irrel(options const & opts)   { return opts.get_bool(*g_pp_hide_comp_irrel, LEAN_DEFAULT_PP_HIDE_COMP_IRRELEVANT); }
bool     get_pp_delayed_abstraction(options const & opts) { return opts.get_bool(*g_pp_delayed_abstraction, LEAN_DEFAULT_PP_DELAYED_ABSTRACTION); }
bool     get_pp_structure_instances(options const & opts) { return opts.get_bool(*g_pp_structure_instances, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES); }
bool     get_pp_structure_instances_qualifier(options const & opts) { return opts.get_bool(*g_pp_structure_instances_qualifier, LEAN_DEFAULT_PP_STRUCTURE_INSTANCES_QUALIFIER); }
bool     get_pp_structure_projections(options const & opts) { return opts.get_bool(*g_pp_structure_projections, LEAN_DEFAULT_PP_STRUCTURE_PROJECTIONS); }
bool     get_pp_instantiate_mvars(options const & o)    { return o.get_bool(*g_pp_instantiate_mvars, LEAN_DEFAULT_PP_INSTANTIATE_MVARS); }
bool     get_pp_use_holes(options const & o)            { return o.get_bool(*g_pp_use_holes, LEAN_DEFAULT_PP_USE_HOLES); }
bool     get_pp_annotations(options const & o)          { return o.get_bool(*g_pp_annotations, LEAN_DEFAULT_PP_ANNOTATIONS); }
bool     get_pp_all(options const & opts)               { return opts.get_bool(*g_pp_all, LEAN_DEFAULT_PP_ALL); }
}




// ========== attribute_manager.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/sstream.h"
#include "util/priority_queue.h"
#include "kernel/environment.h"
#include "library/abstract_parser.h"
#include "library/io_state.h"

#ifndef LEAN_DEFAULT_PRIORITY
#define LEAN_DEFAULT_PRIORITY 1000u
#endif

namespace lean {
struct attr_data {
    virtual unsigned hash() const {
        return 0;
    }
    virtual void parse(abstract_parser &) {}
    virtual void print(std::ostream &) {}
    virtual ~attr_data() {}
};

typedef std::shared_ptr<attr_data> attr_data_ptr;
struct attr_config;

/* Return an instance of the basic attr_data */
attr_data_ptr get_default_attr_data();

typedef std::function<environment(environment const &, io_state const &, name const &, unsigned, bool)> after_set_proc;
typedef std::function<void(environment const &, name const &, bool)> after_set_check_proc;
typedef std::function<environment(environment const &, io_state const &, name const &, bool)> before_unset_proc;

class attribute {
    friend struct attr_config;
    friend class  decl_attributes;
private:
    name              m_id;
    std::string       m_descr;
    after_set_proc    m_after_set;
    before_unset_proc m_before_unset;
protected:
    environment set_core(environment const &, io_state const &, name const &, unsigned, attr_data_ptr, bool) const;

    virtual environment set_untyped(environment const &, io_state const &, name const &, unsigned, attr_data_ptr, bool) const = 0;
    virtual void write_entry(serializer &, attr_data const &) const = 0;
    virtual attr_data_ptr read_entry(deserializer &) const = 0;
public:
    attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            m_id(id), m_descr(descr), m_after_set(after_set), m_before_unset(before_unset) {}
    virtual ~attribute() {}

    name const & get_name() const { return m_id; }
    std::string const & get_description() const { return m_descr; }

    virtual attr_data_ptr get_untyped(environment const &, name const &) const;
    bool is_instance(environment const & env, name const & n) const {
        return static_cast<bool>(get_untyped(env, n));
    }
    unsigned get_prio(environment const &, name const &) const;
    virtual void get_instances(environment const &, buffer<name> &) const;
    priority_queue<name, name_quick_cmp> get_instances_by_prio(environment const &) const;
    virtual attr_data_ptr parse_data(abstract_parser &) const;

    virtual environment unset(environment env, io_state const & ios, name const & n, bool persistent) const;
    virtual unsigned get_fingerprint(environment const & env) const;
};

typedef std::shared_ptr<attribute const> attribute_ptr;

/** \brief An attribute without associated data */
class basic_attribute : public attribute {
protected:
    virtual void write_entry(serializer &, attr_data const &) const override final {}
    virtual attr_data_ptr read_entry(deserializer &) const override final { return get_default_attr_data(); }
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, unsigned prio, attr_data_ptr,
                                    bool persistent) const override final {
        return set(env, ios, n, prio, persistent);
    }
public:
    basic_attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            attribute(id, descr, after_set, before_unset) {}

    static basic_attribute with_check(name const & id, char const * descr, after_set_check_proc after_set) {
        return basic_attribute(
                id, descr,
                [=](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                    after_set(env, n, persistent);
                    return env;
                },
                [](environment const & env, io_state const &, name const &, bool) {
                    return env;
                });
    }

    virtual environment set(environment const & env, io_state const & ios,
                            name const & n, unsigned prio, bool persistent) const {
        return set_core(env, ios, n, prio, get_default_attr_data(), persistent);
    }
};

template<typename Data>
class typed_attribute : public attribute {
protected:
    virtual environment set_untyped(environment const & env, io_state const & ios, name const & n, unsigned prio,
                                    attr_data_ptr data, bool persistent) const final override {
        lean_assert(dynamic_cast<Data const *>(&*data));
        return set(env, ios, n, prio, static_cast<Data const &>(*data), persistent);
    }

    virtual void write_entry(serializer & s, attr_data const & data) const final override {
        lean_assert(dynamic_cast<Data const *>(&data));
        static_cast<Data const &>(data).write(s);
    }
    virtual attr_data_ptr read_entry(deserializer & d) const final override {
        auto data = new Data;
        data->read(d);
        return attr_data_ptr(data);
    }
public:
    typed_attribute(name const & id, char const * descr, after_set_proc after_set = {}, before_unset_proc before_unset = {}) :
            attribute(id, descr, after_set, before_unset) {}

    virtual attr_data_ptr parse_data(abstract_parser & p) const override {
        auto data = new Data;
        data->parse(p);
        return attr_data_ptr(data);
    }

    virtual environment set(environment const & env, io_state const & ios, name const & n, unsigned prio,
                            Data const & data, bool persistent) const {
        return set_core(env, ios, n, prio, std::unique_ptr<attr_data>(new Data(data)), persistent);
    }
    std::shared_ptr<Data> get(environment const & env, name const & n) const {
        auto data = get_untyped(env, n);
        if (!data)
            return {};
        lean_assert(std::dynamic_pointer_cast<Data>(data));
        return std::static_pointer_cast<Data>(data);
    }
};

template<typename Data>
class proxy_attribute : public basic_attribute {
private:
    Data m_status;
public:
    proxy_attribute(char const * id, char const * descr, Data const & status):
        basic_attribute(id, descr), m_status(status) {}

    virtual typed_attribute<Data> const & get_attribute() const = 0;

    virtual attr_data_ptr get_untyped(environment const & env, name const & n) const override {
        if (auto data = get_attribute().get(env, n)) {
            if (data->m_status == m_status)
                return get_default_attr_data();
        }
        return attr_data_ptr();
    }

    virtual environment set(environment const & env, io_state const & ios, name const & n,
                            unsigned prio, bool persistent) const override {
        return get_attribute().set(env, ios, n, prio, m_status, persistent);
    }

    virtual environment unset(environment, io_state const &, name const &, bool) const override {
        throw exception(sstream() << "cannot remove attribute [" << get_name() << "]");
    }

    virtual void get_instances(environment const & env, buffer<name> & r) const override {
        buffer<name> tmp;
        get_attribute().get_instances(env, tmp);
        for (name const & n : tmp)
            if (is_instance(env, n))
                r.push_back(n);
    }

    virtual unsigned get_fingerprint(environment const & env) const override {
        return get_attribute().get_fingerprint(env);
    }
};

struct indices_attribute_data : public attr_data {
    list<unsigned> m_idxs;
    indices_attribute_data(list<unsigned> const & idxs) : m_idxs(idxs) {}
    indices_attribute_data() : indices_attribute_data(list<unsigned>()) {}

    virtual unsigned hash() const override {
        unsigned h = 0;
        for (unsigned i : m_idxs)
            h = ::lean::hash(h, i);
        return h;
    }
    void write(serializer & s) const {
        write_list(s, m_idxs);
    }
    void read(deserializer & d) {
        m_idxs = read_list<unsigned>(d);
    }
    void parse(abstract_parser & p) override;
    virtual void print(std::ostream & out) override {
        for (auto p : m_idxs) {
            out << " " << p + 1;
        }
    }
};

struct key_value_data : public attr_data {
    // generalize: name_map<std::string> m_pairs;
    std::string m_symbol;
    std::string m_library;

    virtual unsigned hash() const override {
        // unsigned h = 0;
        // // This isn't right ..., well maybe? I don't really know.
        // // Rust's Hash trait is super good at this.
        // m_pairs.for_each([&] (name const & n, std::string const & value) {
        //         h += n.hash();
        //         // h += ::lean::hash_str(value, h);
        // });
        return 0;
    }

    void write(serializer & s) const {
        s << m_symbol;
        s << m_library;
    }

    void read(deserializer & d) {
        std::string m_symbol, m_library;
        d >> m_symbol;
        d >> m_library;
    }

    void parse(abstract_parser & p) override {
        std::cout << "in extern parser" << std::endl;
        std::string n = p.parse_string_lit();
        std::string l = p.parse_string_lit();
        std::cout << "link symbol: " << n << std::endl;
        std::cout << "library symbol: " << l << std::endl;
        this->m_symbol = n;
        this->m_library = l;
    }

    virtual void print(std::ostream & out) override {
        out << "external";
        // for (auto p : m_idxs) {
        //    out << " " << p + 1;
        // }
    }
};

/** \brief Attribute that represents a list of indices. input and output are 1-indexed for convenience. */
typedef typed_attribute<indices_attribute_data> indices_attribute;

/** \brief Attribute that represents a list of indices. input and output are 1-indexed for convenience. */
typedef typed_attribute<key_value_data> key_value_attribute;

class user_attribute_ext {
public:
    virtual ~user_attribute_ext() {}
    virtual name_map<attribute_ptr> get_attributes(environment const & env);
    virtual void write_entry(serializer &, attr_data const &) {
        lean_unreachable();
    }
    virtual attr_data_ptr read_entry(deserializer &) {
        lean_unreachable();
    }
};

/** \brief Register the user_attribute handlers, if included in the compilation */
void set_user_attribute_ext(std::unique_ptr<user_attribute_ext>);

void register_system_attribute(attribute_ptr);
template<typename Attribute>
void register_system_attribute(Attribute attr) {
    register_system_attribute(attribute_ptr(new Attribute(attr)));
}
void register_incompatible(char const * attr1, char const * attr2);

bool is_system_attribute(name const & attr_name);
bool is_attribute(environment const & env, name const & attr);
attribute const & get_attribute(environment const & env, name const & attr);
attribute const & get_system_attribute(name const & attr);
void get_attributes(environment const & env, buffer<attribute const *> &);

bool has_attribute(environment const & env, name const & attr, name const & d);

bool are_incompatible(attribute const & attr1, attribute const & attr2);

unsigned get_attribute_fingerprint(environment const & env, name const & attr);

void initialize_attribute_manager();
void finalize_attribute_manager();
}




// ========== attribute_manager.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <algorithm>
#include <unordered_map>
#include "util/priority_queue.h"
#include "util/sstream.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"

namespace lean {
template class typed_attribute<indices_attribute_data>;
template class typed_attribute<key_value_data>;

static name_map<attribute_ptr> * g_system_attributes = nullptr;
static user_attribute_ext * g_user_attribute_ext     = nullptr;
static attr_data_ptr * g_default_attr_data_ptr       = nullptr;

attr_data_ptr get_default_attr_data() {
    return *g_default_attr_data_ptr;
}

name_map<attribute_ptr> user_attribute_ext::get_attributes(environment const &) {
    return {};
}
void set_user_attribute_ext(std::unique_ptr<user_attribute_ext> ext) {
    if (g_user_attribute_ext) delete g_user_attribute_ext;
    g_user_attribute_ext = ext.release();
}

static std::vector<pair<name, name>> * g_incomp = nullptr;

bool is_system_attribute(name const & attr) {
    return g_system_attributes->contains(attr);
}
void register_system_attribute(attribute_ptr attr) {
    lean_assert(!is_system_attribute(attr->get_name()));
    (*g_system_attributes)[attr->get_name()] = attr;
}
bool is_attribute(environment const & env, name const & attr) {
    return is_system_attribute(attr) || g_user_attribute_ext->get_attributes(env).find(attr) != nullptr;
}

attribute const & get_system_attribute(name const & attr) {
    auto it = g_system_attributes->find(attr);
    if (it)
        return **it;
    throw exception(sstream() << "unknown system attribute '" << attr << "'");
}

attribute const & get_attribute(environment const & env, name const & attr) {
    auto it = g_system_attributes->find(attr);
    if (it)
        return **it;
    it = g_user_attribute_ext->get_attributes(env).find(attr);
    if (it)
        return **it;
    throw exception(sstream() << "unknown attribute '" << attr << "'");
}

struct attr_record {
    name          m_decl;
    attr_data_ptr m_data; // no data -> deleted

    attr_record() {}
    attr_record(name decl, attr_data_ptr data):
            m_decl(decl), m_data(data) {}

    unsigned hash() const {
        unsigned h = m_decl.hash();
        if (m_data)
            h = ::lean::hash(h, m_data->hash());
        return h;
    }

    bool deleted() const {
        return !static_cast<bool>(m_data);
    }
};

struct attr_record_cmp {
    int operator()(attr_record const & r1, attr_record const & r2) const {
        // Adding a new record with different arguments should override the old one
        return quick_cmp(r1.m_decl, r2.m_decl);
    }
};

struct attr_entry {
    name        m_attr;
    unsigned    m_prio;
    attr_record m_record;

    attr_entry() {}
    attr_entry(name const & attr, unsigned prio, attr_record const & record):
            m_attr(attr), m_prio(prio), m_record(record) {}
};

typedef priority_queue<attr_record, attr_record_cmp> attr_records;
typedef name_map<pair<attr_records, unsigned>> attr_state;

struct attr_config {
    typedef attr_state state;
    typedef attr_entry entry;

    static unsigned get_entry_hash(entry const & e) {
        return hash(hash(e.m_attr.hash(), e.m_record.hash()), e.m_prio);
    }

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        attr_records m;
        unsigned h = 0;
        if (auto q = s.find(e.m_attr)) {
            m = q->first;
            h = q->second;
        }
        m.insert(e.m_record, e.m_prio);
        h = hash(h, get_entry_hash(e));
        s.insert(e.m_attr, mk_pair(m, h));
    }

    static const char * get_serialization_key() { return "ATTR"; }

    static void write_entry(serializer & s, entry const & e) {
        s << e.m_attr << e.m_prio << e.m_record.m_decl << e.m_record.deleted();
        if (!e.m_record.deleted()) {
            if (is_system_attribute(e.m_attr))
                get_system_attribute(e.m_attr).write_entry(s, *e.m_record.m_data);
            else
                // dispatch over the extension, since we can't call get_attribute without an env
                g_user_attribute_ext->write_entry(s, *e.m_record.m_data);
        }
    }

    static entry read_entry(deserializer & d) {
        entry e; bool deleted;
        d >> e.m_attr >> e.m_prio >> e.m_record.m_decl >> deleted;
        if (!deleted) {
            if (is_system_attribute(e.m_attr))
                e.m_record.m_data = get_system_attribute(e.m_attr).read_entry(d);
            else
                // dispatch over the extension, since we can't call get_attribute without an env
                e.m_record.m_data = g_user_attribute_ext->read_entry(d);
        }
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        return optional<unsigned>(get_entry_hash(e));
    }
};

template class scoped_ext<attr_config>;
typedef scoped_ext<attr_config> attribute_ext;

environment attribute::set_core(environment const & env, io_state const & ios, name const & n, unsigned prio,
                                attr_data_ptr data, bool persistent) const {
    auto env2 = attribute_ext::add_entry(env, ios, attr_entry(m_id, prio, attr_record(n, data)), persistent);
    if (m_after_set)
        env2 = m_after_set(env2, ios, n, prio, persistent);
    return env2;
}

environment attribute::unset(environment env, io_state const & ios, name const & n, bool persistent) const {
    if (m_before_unset) {
        env = m_before_unset(env, ios, n, persistent);
    } else {
        if (m_after_set)
            throw exception(sstream() << "cannot remove attribute [" << get_name() << "]");
    }
    return attribute_ext::add_entry(env, ios, attr_entry(m_id, get_prio(env, n), attr_record(n, {})), persistent);
}

attr_data_ptr attribute::get_untyped(environment const & env, name const & n) const {
    if (auto p = attribute_ext::get_state(env).find(m_id)) {
        attr_records const & records = p->first;
        if (auto record = records.get_key({n, {}}))
            return record->m_data;
    }
    return {};
}

unsigned attribute::get_prio(environment const & env, name const & n) const {
    if (auto p = attribute_ext::get_state(env).find(get_name())) {
        attr_records const & records = p->first;
        if (auto prio = records.get_prio({n, {}}))
            return prio.value();
    }
    return LEAN_DEFAULT_PRIORITY;
}

void attribute::get_instances(environment const & env, buffer<name> & r) const {
    if (auto p = attribute_ext::get_state(env).find(m_id)) {
        attr_records const & records = p->first;
        records.for_each([&](attr_record const & rec) {
                if (!rec.deleted())
                    r.push_back(rec.m_decl);
            });
    }
}

unsigned attribute::get_fingerprint(environment const & env) const {
    if (auto p = attribute_ext::get_state(env).find(m_id)) {
        return p->second;
    }
    return 0;
}

priority_queue<name, name_quick_cmp> attribute::get_instances_by_prio(environment const & env) const {
    priority_queue<name, name_quick_cmp> q;
    buffer<name> b;
    get_instances(env, b);
    for (auto const & n : b)
        q.insert(n, get_prio(env, n));
    return q;
}

attr_data_ptr attribute::parse_data(abstract_parser &) const {
    return get_default_attr_data();
}

void indices_attribute_data::parse(abstract_parser & p) {
    buffer<unsigned> vs;
    while (p.curr_is_numeral()) {
        auto pos = p.pos();
        unsigned v = p.parse_small_nat();
        if (v == 0)
            throw parser_error("invalid attribute parameter, value must be positive", pos);
        vs.push_back(v - 1);
    }
    m_idxs = to_list(vs);
}

void register_incompatible(char const * attr1, char const * attr2) {
    lean_assert(is_system_attribute(attr1));
    lean_assert(is_system_attribute(attr2));
    name s1(attr1);
    name s2(attr2);
    if (s1 > s2)
        std::swap(s1, s2);
    g_incomp->emplace_back(s1, s2);
}

void get_attributes(environment const & env, buffer<attribute const *> & r) {
    g_system_attributes->for_each([&](name const &, attribute_ptr const & attr) {
        r.push_back(&*attr);
    });
    g_user_attribute_ext->get_attributes(env).for_each([&](name const &, attribute_ptr const & attr) {
        r.push_back(&*attr);
    });
}

bool has_attribute(environment const & env, name const & attr, name const & d) {
    return get_attribute(env, attr).is_instance(env, d);
}

bool are_incompatible(attribute const & attr1, attribute const & attr2) {
    name s1(attr1.get_name());
    name s2(attr2.get_name());
    if (s1 > s2)
        std::swap(s1, s2);
    return std::find(g_incomp->begin(), g_incomp->end(), mk_pair(s1, s2)) != g_incomp->end();
}

unsigned get_attribute_fingerprint(environment const & env, name const & attr) {
    return get_attribute(env, attr).get_fingerprint(env);
}

void initialize_attribute_manager() {
    g_default_attr_data_ptr = new attr_data_ptr(new attr_data);
    g_system_attributes     = new name_map<attribute_ptr>();
    g_user_attribute_ext    = new user_attribute_ext();
    g_incomp                = new std::vector<pair<name, name>>();
    attribute_ext::initialize();
}

void finalize_attribute_manager() {
    attribute_ext::finalize();
    delete g_incomp;
    delete g_user_attribute_ext;
    delete g_system_attributes;
    delete g_default_attr_data_ptr;
}
}




// ========== check.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/* Type check 'e' using the given type context.
   It throws an exception in case of failure.

   This procedure is use to check the proof-term produced by tactics such as
   rewrite.
*/
void check(type_context_old & ctx, expr const & e);
void initialize_check();
void finalize_check();
}




// ========== check.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_sets.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/type_context.h"

namespace lean {
struct check_fn {
    type_context_old &   m_ctx;
    expr_set             m_visited;

    void visit_constant(expr const & e) {
        declaration d = m_ctx.env().get(const_name(e));
        if (d.get_num_univ_params() != length(const_levels(e))) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "incorrect of universe levels at " << e << "\n";);
            throw exception("check failed, incorrect number of universe levels "
                            "(use 'set_option trace.check true' for additional details)");
        }
    }

    void visit_macro(expr const & e) {
        for (unsigned i = 0; i < macro_num_args(e); i++)
            visit(macro_arg(e, i));
    }

    void ensure_type(expr const & e) {
        expr S = m_ctx.relaxed_whnf(m_ctx.infer(e));
        if (is_sort(S)) return;
        if (is_metavar(S)) {
            level u = m_ctx.mk_univ_metavar_decl();
            if (m_ctx.is_def_eq(S, mk_sort(u)))
                return;
        }
        lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                   tout() << "type expected at " << e << "\n";);
        throw exception("check failed, type expected "
                        "(use 'set_option trace.check true' for additional details)");
    }

    void visit_binding(expr const & e, bool is_pi) {
        type_context_old::tmp_locals locals(m_ctx);
        expr it = e;
        while (it.kind() == e.kind()) {
            expr d = instantiate_rev(binding_domain(it), locals.size(), locals.data());
            visit(d);
            locals.push_local(binding_name(it), d, binding_info(it));
            ensure_type(d);
            it = binding_body(it);
        }
        expr b = instantiate_rev(it, locals.size(), locals.data());
        visit(b);
        if (is_pi)
            ensure_type(b);
    }

    void visit_lambda(expr const & e) {
        visit_binding(e, false);
    }

    void visit_pi(expr const & e) {
        visit_binding(e, true);
    }

    void visit_let(expr const & e) {
        visit(let_value(e));
        visit(let_type(e));
        expr v_type = m_ctx.infer(let_value(e));
        if (!m_ctx.relaxed_is_def_eq(let_type(e), v_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "type mismatch at let binder\n  " << e << "\n";);
            throw exception("check failed, type mismatch at let binder "
                            "(use 'set_option trace.check true' for additional details)");
        }
        /* Improve performance if bottleneck */
        type_context_old::tmp_locals locals(m_ctx);
        expr local = locals.push_local_from_let(e);
        visit(instantiate(let_body(e), local));
    }

    void visit_app(expr const & e) {
        visit(app_fn(e));
        visit(app_arg(e));
        expr f_type = m_ctx.relaxed_whnf(m_ctx.infer(app_fn(e)));
        if (!is_pi(f_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "function expected at\n  " << e << "\ntype\n  " << f_type << "\n";);
            throw exception("check failed, function expected (use 'set_option trace.check true' for additional details)");
        }
        expr a_type = m_ctx.infer(app_arg(e));
        expr d_type = binding_domain(f_type);
        if (!m_ctx.relaxed_is_def_eq(a_type, d_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "application type mismatch at\n  " << e << "\nargument type\n  "
                       << a_type << "\nexpected type\n  " << d_type;);
            throw exception("check failed, application type mismatch "
                            "(use 'set_option trace.check true' for additional details)");
        }
    }

    void visit(expr const & e) {
        if (m_visited.find(e) != m_visited.end())
            return;
        m_visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Local:
        case expr_kind::Meta:
        case expr_kind::Sort:
            break; /* do nothing */
        case expr_kind::Constant:
            return visit_constant(e);
        case expr_kind::Var:
            lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Macro:
            return visit_macro(e);
        case expr_kind::Lambda:
            return visit_lambda(e);
        case expr_kind::Pi:
            return visit_pi(e);
        case expr_kind::App:
            return visit_app(e);
        case expr_kind::Let:
            return visit_let(e);
        }
    }

public:
    check_fn(type_context_old & ctx):m_ctx(ctx) {}
    void operator()(expr const & e) { return visit(e); }
};

void check(type_context_old & ctx, expr const & e) {
    metavar_context mctx = ctx.mctx();
    check_fn checker(ctx);
    checker(e);
    ctx.set_mctx(mctx);
}

void initialize_check() {
    register_trace_class("check");
}

void finalize_check() {
}
}




// ========== idx_metavar.h ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/** \brief Create a universe level metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
level mk_idx_metauniv(unsigned i);
/** \brief Return true iff \c l is a metauniverse created using \c mk_idx_metauniv */
bool is_idx_metauniv(level const & l);
unsigned to_meta_idx(level const & l);

/** \brief Create a special metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
expr mk_idx_metavar(unsigned i, expr const & type);
/** \brief Return true iff \c l is a metavariable created using \c mk_idx_metavar */
bool is_idx_metavar(expr const & l);
unsigned to_meta_idx(expr const & e);

/** \brief Return true iff \c e contains idx metavariables or universe metavariables */
bool has_idx_metavar(expr const & e);
bool has_idx_expr_metavar(expr const & e);
bool has_idx_metauniv(level const & l);

class metavar_context;

/** \brief Convert metavariables occurring in \c e into indexed/temporary metavariables.
    New metavariables are added to new_us and new_ms. */
expr to_idx_metavars(metavar_context const & mctx, expr const & e, buffer<level> & new_us, buffer<expr> & new_ms);

void initialize_idx_metavar();
void finalize_idx_metavar();
}




// ========== idx_metavar.cpp ==========

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/for_each_fn.h"
#include "library/idx_metavar.h"
#include "library/metavar_context.h"
#include "library/replace_visitor.h"

#ifndef LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY 1024*8
#endif

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_idx_metavar() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_idx_metavar() {
    delete g_tmp_prefix;
}

level mk_idx_metauniv(unsigned i) {
    return mk_meta_univ(name(*g_tmp_prefix, i));
}

expr mk_idx_metavar(unsigned i, expr const & type) {
    return mk_metavar(name(*g_tmp_prefix, i), type);
}

bool is_idx_metauniv(level const & l) {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_metauniv(l));
    return meta_id(l).get_numeral();
}

bool is_idx_metavar(expr const & e) {
    if (!is_metavar(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(expr const & e) {
    lean_assert(is_idx_metavar(e));
    return mlocal_name(e).get_numeral();
}

bool has_idx_metauniv(level const & l) {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (!has_meta(l)) return false;
            if (is_idx_metauniv(l))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_metavar(expr const & e) {
    if (!has_univ_metavar(e) && !has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (!has_univ_metavar(e) && !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e))
                found = true;
            else if (is_constant(e) && std::any_of(const_levels(e).begin(), const_levels(e).end(), has_idx_metauniv))
                found = true;
            else if (is_sort(e) && has_idx_metauniv(sort_level(e)))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_expr_metavar(expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e)) found = true;
            return true;
        });
    return found;
}

struct to_idx_metavars_fn : public replace_visitor {
    metavar_context const & m_mctx;
    buffer<level> &         m_new_us;
    buffer<expr> &          m_new_ms;
    name_map<level>         m_lvl_cache;

    to_idx_metavars_fn(metavar_context const & mctx, buffer<level> & new_us, buffer<expr> & new_ms):
        m_mctx(mctx), m_new_us(new_us), m_new_ms(new_ms) {}

    level visit(level const & l) {
        if (!has_meta(l)) return l;
        return replace(l, [&](level const & l) {
                if (is_meta(l) && !is_idx_metauniv(l)) {
                    if (auto it = m_lvl_cache.find(meta_id(l)))
                        return some_level(*it);
                    level new_l = mk_idx_metauniv(m_new_us.size());
                    m_lvl_cache.insert(meta_id(l), new_l);
                    m_new_us.push_back(new_l);
                    return some_level(new_l);
                }
                return none_level();
            });
    }

    levels visit(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit(l); });
    }

    virtual expr visit_meta(expr const & m) override {
        if (is_idx_metavar(m)) {
            return m;
        } else if (auto decl = m_mctx.find_metavar_decl(m)) {
            expr new_type = visit(decl->get_type());
            unsigned i    = m_new_ms.size();
            expr new_m    = mk_idx_metavar(i, new_type);
            m_new_ms.push_back(new_m);
            return new_m;
        } else {
            throw exception("unexpected occurrence of metavariable");
        }
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, visit(const_levels(e)));
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, visit(sort_level(e)));
    }

    virtual expr visit(expr const & e) override {
        if (!has_metavar(e)) return e;
        return replace_visitor::visit(e);
    }
};

expr to_idx_metavars(metavar_context const & mctx, expr const & e, buffer<level> & new_us, buffer<expr> & new_ms) {
    if (!has_metavar(e))
        return e;
    return to_idx_metavars_fn(mctx, new_us, new_ms)(e);
}
}




// ========== init_module.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
void initialize_library_core_module();
void finalize_library_core_module();
void initialize_library_module();
void finalize_library_module();
}




// ========== init_module.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/class.h"
#include "library/num.h"
#include "library/string.h"
#include "library/annotation.h"
#include "library/quote.h"
#include "library/explicit.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/aliases.h"
#include "library/export_decl.h"
#include "library/io_state.h"
#include "library/idx_metavar.h"
#include "library/sorry.h"
#include "library/placeholder.h"
#include "library/print.h"
#include "library/fingerprint.h"
#include "library/util.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/relation_manager.h"
#include "library/user_recursors.h"
#include "library/noncomputable.h"
#include "library/aux_recursors.h"
#include "library/abstract_context_cache.h"
#include "library/type_context.h"
#include "library/local_context.h"
#include "library/metavar_context.h"
#include "library/attribute_manager.h"
#include "library/unification_hint.h"
#include "library/delayed_abstraction.h"
#include "library/app_builder.h"
#include "library/fun_info.h"
#include "library/inverse.h"
#include "library/pattern_attribute.h"
#include "library/comp_val.h"
#include "library/documentation.h"
#include "library/defeq_canonizer.h"
#include "library/congr_lemma.h"
#include "library/check.h"
#include "library/parray.h"
#include "library/profiling.h"
#include "library/time_task.h"
#include "library/unique_id.h"

namespace lean {
void initialize_library_core_module() {
    initialize_constants();
    initialize_profiling();
    initialize_trace();
    initialize_module();
    initialize_scoped_ext();
    initialize_attribute_manager();
}

void finalize_library_core_module() {
    finalize_attribute_manager();
    finalize_scoped_ext();
    finalize_module();
    finalize_trace();
    finalize_profiling();
    finalize_constants();
}

void initialize_library_module() {
    initialize_unique_id();
    initialize_local_context();
    initialize_metavar_context();
    initialize_fingerprint();
    initialize_print();
    initialize_placeholder();
    initialize_idx_metavar();
    initialize_io_state();
    initialize_kernel_serializer();
    initialize_typed_expr();
    initialize_choice();
    initialize_string();
    initialize_num();
    initialize_annotation();
    initialize_explicit();
    initialize_protected();
    initialize_private();
    initialize_reducible();
    initialize_aliases();
    initialize_export_decl();
    initialize_sorry();
    initialize_class();
    initialize_library_util();
    initialize_quote();
    initialize_pp_options();
    initialize_projection();
    initialize_relation_manager();
    initialize_user_recursors();
    initialize_noncomputable();
    initialize_aux_recursors();
    initialize_app_builder();
    initialize_fun_info();
    initialize_unification_hint();
    initialize_abstract_context_cache();
    initialize_type_context();
    initialize_delayed_abstraction();
    initialize_inverse();
    initialize_pattern_attribute();
    initialize_comp_val();
    initialize_documentation();
    initialize_defeq_canonizer();
    initialize_check();
    initialize_congr_lemma();
    initialize_parray();
    initialize_time_task();
}

void finalize_library_module() {
    finalize_time_task();
    finalize_parray();
    finalize_congr_lemma();
    finalize_check();
    finalize_defeq_canonizer();
    finalize_documentation();
    finalize_comp_val();
    finalize_pattern_attribute();
    finalize_inverse();
    finalize_delayed_abstraction();
    finalize_type_context();
    finalize_abstract_context_cache();
    finalize_unification_hint();
    finalize_fun_info();
    finalize_app_builder();
    finalize_aux_recursors();
    finalize_noncomputable();
    finalize_user_recursors();
    finalize_relation_manager();
    finalize_projection();
    finalize_pp_options();
    finalize_quote();
    finalize_library_util();
    finalize_class();
    finalize_sorry();
    finalize_export_decl();
    finalize_aliases();
    finalize_reducible();
    finalize_private();
    finalize_protected();
    finalize_explicit();
    finalize_annotation();
    finalize_num();
    finalize_string();
    finalize_choice();
    finalize_typed_expr();
    finalize_kernel_serializer();
    finalize_io_state();
    finalize_idx_metavar();
    finalize_placeholder();
    finalize_print();
    finalize_fingerprint();
    finalize_metavar_context();
    finalize_local_context();
    finalize_unique_id();
}
}




// ========== class.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"
namespace lean {
/** \brief Add a new 'class' to the environment (if it is not already declared) */
environment add_class(environment const &env, name const &n, bool persistent);
/** \brief Add a new 'class instance' to the environment. */
environment add_instance(environment const & env, name const & n, unsigned priority, bool persistent);
/** \brief Return true iff \c c was declared with \c add_class. */
bool is_class(environment const & env, name const & c);
/** \brief Return true iff \c i was declared with \c add_instance. */
bool is_instance(environment const & env, name const & i);
/** \brief Return the set of active classes (as a predicate) for the given environment */
name_predicate mk_class_pred(environment const & env);
/** \brief Return the set of active instances (as a predicate) for the given environment */
name_predicate mk_instance_pred(environment const & env);
/** \brief Return the instances of the given class. */
list<name> get_class_instances(environment const & env, name const & c);
/** \brief Return the classes in the given environment. */
void get_classes(environment const & env, buffer<name> & classes);
name get_class_name(environment const & env, expr const & e);

/** \brief Return name for attribute [instance] */
name const & get_instance_attr_name();
unsigned get_instance_fingerprint(environment const & env);

name const & get_anonymous_instance_prefix();
name mk_anonymous_inst_name(unsigned idx);
bool is_anonymous_inst_name(name const & n);

/** \brief Return true iff e is of the form `out_param a` */
bool is_class_out_param(expr const & e);

/** \brief Return true iff c is a type class that contains an `out_param` */
bool has_class_out_params(environment const & env, name const & c);

/** \brief Add a new attribute for tracking symbols occurring in instances of type classes.

    We use this feature for tracking "algebraic" symbols.
    For example, the class is_commutative is marked with the [algebra] attribute
    registered with this procedure.
    Then, whenever we declarare an is_commutative instance, we store the symbols
    occuring in the application (is_commutative ...) in a set.

    \remark We ignore symbols occurring in types.

    For more details see:
    https://github.com/leanprover/lean/wiki/Refactoring-structures */
void register_class_symbol_tracking_attribute(name const & n, char const * descr);

/** \brief Return true iff \c n is the name of an attribute created with register_class_symbol_tracking_attribute. */
bool is_class_symbol_tracking_attribute(name const & n);

/** \brief Given an attribute created with register_class_symbol_tracking_attribute,
    this function returns the symbols that occur in instances of any class marked with the attribute. */
name_set get_class_attribute_symbols(environment const & env, name const & attr_name);

void initialize_class();
void finalize_class();
}




// ========== class.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/lbool.h"
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "util/name_set.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/type_context.h"
#include "library/class.h"
#include "library/attribute_manager.h"
#include "library/trace.h"

namespace lean {
enum class class_entry_kind { Class, Instance, Tracker };
struct class_entry {
    class_entry_kind m_kind;
    name             m_class;
    name             m_instance;    // only relevant if m_kind == Instance
    unsigned         m_priority{0}; // only relevant if m_kind == Instance
    name             m_track_attr;  // only relevant if m_kind == Tracker
    class_entry():m_kind(class_entry_kind::Class) {}
    explicit class_entry(name const & c):m_kind(class_entry_kind::Class), m_class(c) {}
    class_entry(class_entry_kind k, name const & c, name const & i, unsigned p):
        m_kind(k), m_class(c), m_instance(i), m_priority(p) {}
    class_entry(name const & c, name const & track_attr):
        m_kind(class_entry_kind::Tracker), m_class(c), m_track_attr(track_attr) {}
};

struct class_state {
    typedef name_map<list<name>> class_instances;
    typedef name_map<unsigned>   instance_priorities;
    typedef name_map<list<name>> class_track_attrs;
    typedef name_map<name_set>   attr_symbols;

    class_instances       m_instances;
    instance_priorities   m_priorities;
    class_track_attrs     m_class_track_attrs;
    attr_symbols          m_attr_symbols;
    name_set              m_has_out_params;

    unsigned get_priority(name const & i) const {
        if (auto it = m_priorities.find(i))
            return *it;
        else
            return LEAN_DEFAULT_PRIORITY;
    }

    bool is_instance(name const & i) const {
        return m_priorities.contains(i);
    }

    list<name> insert(name const & inst, unsigned priority, list<name> const & insts) const {
        if (!insts)
            return to_list(inst);
        else if (priority >= get_priority(head(insts)))
            return list<name>(inst, insts);
        else
            return list<name>(head(insts), insert(inst, priority, tail(insts)));
    }

    void add_class(environment const & env, name const & c) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, list<name>());
        expr type = env.get(c).get_type();
        bool has_out_param = false;
        while (is_pi(type)) {
            if (is_class_out_param(binding_domain(type))) {
                has_out_param = true;
                break;
            }
            type = binding_body(type);
        }
        if (has_out_param)
            m_has_out_params.insert(c);
    }

    void collect_symbols(type_checker & tc, name const & inst, name const & attr) {
        environment const & env = tc.env();
        name_set S;
        if (auto curr_S = m_attr_symbols.find(attr))
            S = *curr_S;
        buffer<expr> params;
        expr type = to_telescope(tc, env.get(inst).get_type(), params);
        buffer<expr> args;
        get_app_args(type, args);
        for (expr const & arg : args) {
            expr arg_type = tc.whnf(tc.infer(arg));
            if (!is_sort(arg_type)) {
                /* We only track symbols that are not occurring in types */
                for_each(arg, [&](expr const & e, unsigned) {
                        if (is_constant(e))
                            S.insert(const_name(e));
                        return true;
                    });
            }
        }
        if (!S.empty())
            m_attr_symbols.insert(attr, S);
    }

    void add_instance(environment const & env, name const & c, name const & i, unsigned p) {
        auto it = m_instances.find(c);
        if (!it) {
            m_instances.insert(c, to_list(i));
        } else {
            auto lst = filter(*it, [&](name const & i1) { return i1 != i; });
            m_instances.insert(c, insert(i, p, lst));
        }
        m_priorities.insert(i, p);
        if (auto attrs = m_class_track_attrs.find(c)) {
            type_checker tc(env);
            for (name const & attr : *attrs) {
                collect_symbols(tc, i, attr);
            }
        }
    }

    void track_symbols(name const & c, name const & attr_name) {
        if (auto s = m_class_track_attrs.find(c)) {
            m_class_track_attrs.insert(c, cons(attr_name, *s));
        } else {
            m_class_track_attrs.insert(c, to_list(attr_name));
        }
    }
};

static name * g_class_name = nullptr;

struct class_config {
    typedef class_state state;
    typedef class_entry entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s.add_class(env, e.m_class);
            break;
        case class_entry_kind::Instance:
            s.add_instance(env, e.m_class, e.m_instance, e.m_priority);
            break;
        case class_entry_kind::Tracker:
            s.track_symbols(e.m_class, e.m_track_attr);
            break;
        }
    }

    static name const & get_class_name() {
        return *g_class_name;
    }

    static const char * get_serialization_key() { return "class"; }

    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind);
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s << e.m_class;
            break;
        case class_entry_kind::Instance:
            s << e.m_class << e.m_instance << e.m_priority;
            break;
        case class_entry_kind::Tracker:
            s << e.m_class << e.m_track_attr;
            break;
        }
    }

    static entry read_entry(deserializer & d) {
        entry e; char k;
        d >> k;
        e.m_kind = static_cast<class_entry_kind>(k);
        switch (e.m_kind) {
        case class_entry_kind::Class:
            d >> e.m_class;
            break;
        case class_entry_kind::Instance:
            d >> e.m_class >> e.m_instance >> e.m_priority;
            break;
        case class_entry_kind::Tracker:
            d >> e.m_class >> e.m_track_attr;
            break;
        }
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            return some(e.m_class.hash());
        case class_entry_kind::Instance:
            return some(hash(hash(e.m_class.hash(), e.m_instance.hash()), e.m_priority));
        case class_entry_kind::Tracker:
            return some(hash(e.m_class.hash(), e.m_track_attr.hash()));
        }
        lean_unreachable();
    }
};

template class scoped_ext<class_config>;
typedef scoped_ext<class_config> class_ext;

static void check_class(environment const & env, name const & c_name) {
    env.get(c_name);
}

static void check_is_class(environment const & env, name const & c_name) {
    class_state const & s = class_ext::get_state(env);
    if (!s.m_instances.contains(c_name))
        throw exception(sstream() << "'" << c_name << "' is not a class");
}

name get_class_name(environment const & env, expr const & e) {
    if (!is_constant(e))
        throw exception("class expected, expression is not a constant");
    name const & c_name = const_name(e);
    check_is_class(env, c_name);
    return c_name;
}

environment add_class_core(environment const & env, name const &n, bool persistent) {
    check_class(env, n);
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(n), persistent);
}

void get_classes(environment const & env, buffer<name> & classes) {
    class_state const & s = class_ext::get_state(env);
    s.m_instances.for_each([&](name const & c, list<name> const &) {
            classes.push_back(c);
        });
}

bool is_class(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_instances.contains(c);
}

bool has_class_out_params(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_has_out_params.contains(c);
}

environment add_instance_core(environment const & env, name const & n, unsigned priority, bool persistent) {
    declaration d = env.get(n);
    expr type = d.get_type();
    type_context_old ctx(env, transparency_mode::All);
    class_state S = class_ext::get_state(env);
    type_context_old::tmp_locals locals(ctx);
    while (true) {
        type = ctx.whnf_head_pred(type, [&](expr const & e) {
                expr const & fn = get_app_fn(e);
                return !is_constant(fn) || !S.m_instances.contains(const_name(fn)); });
        if (!is_pi(type))
            break;
        expr x = locals.push_local_from_binding(type);
        type = instantiate(binding_body(type), x);
    }
    name c = get_class_name(env, get_app_fn(type));
    check_is_class(env, c);
    environment new_env = class_ext::add_entry(env, get_dummy_ios(), class_entry(class_entry_kind::Instance, c, n, priority),
                                               persistent);
    return new_env;
}

bool is_instance(environment const & env, name const & i) {
    class_state const & s = class_ext::get_state(env);
    return s.is_instance(i);
}

unsigned get_instance_priority(environment const & env, name const & n) {
    class_state const & s                  = class_ext::get_state(env);
    class_state::instance_priorities insts = s.m_priorities;
    if (auto r = insts.find(n))
        return *r;
    return LEAN_DEFAULT_PRIORITY;
}

name_predicate mk_class_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::class_instances cs = s.m_instances;
    return [=](name const & n) { return cs.contains(n); }; // NOLINT
}

name_predicate mk_instance_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::instance_priorities insts = s.m_priorities;
    return [=](name const & n) { return insts.contains(n); }; // NOLINT
}

list<name> get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return ptr_to_list(s.m_instances.find(c));
}

static name * g_class_attr_name    = nullptr;
static name * g_instance_attr_name = nullptr;

environment add_class(environment const &env, name const &n, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_class_attr_name)).set(env, get_global_ios(), n, LEAN_DEFAULT_PRIORITY, persistent);
}

environment add_instance(environment const & env, name const & n, unsigned priority, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_instance_attr_name)).set(env, get_global_ios(), n, priority, persistent);
}

name const & get_instance_attr_name() {
    return *g_instance_attr_name;
}

unsigned get_instance_fingerprint(environment const & env) {
    return get_attribute_fingerprint(env, get_instance_attr_name());
}

static name * g_anonymous_inst_name_prefix = nullptr;

name const & get_anonymous_instance_prefix() {
    return *g_anonymous_inst_name_prefix;
}

name mk_anonymous_inst_name(unsigned idx) {
    return g_anonymous_inst_name_prefix->append_after(idx);
}

bool is_anonymous_inst_name(name const & n) {
    if (!n.is_atomic() || !n.is_string()) return false;
    return strncmp(n.get_string(),
                   g_anonymous_inst_name_prefix->get_string(),
                   strlen(g_anonymous_inst_name_prefix->get_string())) == 0;
}

bool is_class_out_param(expr const & e) {
    return is_app_of(e, get_out_param_name(), 1);
}

static name_set * g_tracking_attributes = nullptr;

void register_class_symbol_tracking_attribute(name const & n, char const * descr) {
    if (g_tracking_attributes->contains(n))
        throw exception(sstream() << "invalid type class tracking attribute '" << n << "', attribute has already been defined");
    g_tracking_attributes->insert(n);
    register_system_attribute(basic_attribute(n, descr,
                                              [=](environment const & env, io_state const &, name const & d, unsigned, bool persistent) {
                                                  if (!persistent) {
                                                      throw exception(sstream() << "invalid attribute [" << n << "] at '" << d << "', "
                                                                      << "it must not be 'local'");
                                                  }
                                                  if (!is_class(env, d)) {
                                                      throw exception(sstream() << "invalid attribute [" << n << "] at '" << d << "', "
                                                                      << "declaration is not a class");
                                                  }
                                                  return class_ext::add_entry(env, get_dummy_ios(), class_entry(d, n), persistent);
                                              }));
}

bool is_class_symbol_tracking_attribute(name const & n) {
    return g_tracking_attributes->contains(n);
}

name_set get_class_attribute_symbols(environment const & env, name const & attr_name) {
    class_state const & s = class_ext::get_state(env);
    if (name_set const * S = s.m_attr_symbols.find(attr_name))
        return *S;
    else
        return name_set();
}

void initialize_class() {
    g_class_attr_name = new name("class");
    g_instance_attr_name = new name("instance");
    g_class_name = new name("class");
    g_tracking_attributes = new name_set();
    class_ext::initialize();

    register_system_attribute(basic_attribute(*g_class_attr_name, "type class",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_class_core(env, d, persistent);
                                             }));

    register_system_attribute(basic_attribute(*g_instance_attr_name, "type class instance",
                                              [](environment const & env, io_state const &, name const & d,
                                                 unsigned prio, bool persistent) {
                                                  return add_instance_core(env, d, prio, persistent);
                                              }));

    g_anonymous_inst_name_prefix = new name("_inst");
}

void finalize_class() {
    class_ext::finalize();
    delete g_class_name;
    delete g_class_attr_name;
    delete g_instance_attr_name;
    delete g_anonymous_inst_name_prefix;
    delete g_tracking_attributes;
}
}




// ========== sorry.h ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff the given environment contains a sorry macro. */
bool has_sorry(environment const & env);
bool has_sorry(expr const &);
bool has_sorry(declaration const &);
bool has_synthetic_sorry(expr const &);

/** \brief Returns the sorry macro with the specified type.
 * \param synthetic Synthetic macros are created by parser and
 *  elaborator during error recovery.  Non-synthetic macros are
 *  entered by the user using the `sorry` keyword.
 */
expr mk_sorry(expr const & ty, bool synthetic = false);
/** \brief Return true iff \c e is a sorry macro. */
bool is_sorry(expr const & e);
/** \brief Return true iff \c e is a synthetic sorry macro */
bool is_synthetic_sorry(expr const & e);
/** \brief Type of the sorry macro. */
expr const & sorry_type(expr const & sry);
void initialize_sorry();
void finalize_sorry();
}




// ========== sorry.cpp ==========

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/sorry.h"
#include <string>
#include <kernel/find_fn.h>
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "library/module.h"
#include "kernel/for_each_fn.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_sorry_name = nullptr;
static std::string * g_sorry_opcode = nullptr;

class sorry_macro_cell : public macro_definition_cell {
    bool m_synthetic;

public:
    sorry_macro_cell(bool synthetic) : m_synthetic(synthetic) {}

    bool is_synthetic() const { return m_synthetic; }

    virtual name get_name() const override { return *g_sorry_name; }

    unsigned int trust_level() const override { return 1; }

    virtual expr check_type(expr const & sry, abstract_type_context & ctx, bool infer_only) const override {
        if (!is_sorry(sry)) throw exception("invalid sorry macro");
        auto sort = ctx.whnf(ctx.check(sorry_type(sry), infer_only));
        if (!is_sort(sort)) throw exception("type of sorry macro is not a sort");
        return sorry_type(sry);
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return {};
    }

    virtual void write(serializer & s) const override {
        s.write_string(*g_sorry_opcode);
        s.write_bool(m_synthetic);
    }
};

void initialize_sorry() {
    g_sorry_name = new name{"sorry"};
    g_sorry_opcode = new std::string("Sorry");

    register_macro_deserializer(*g_sorry_opcode,
        [] (deserializer & d, unsigned num, expr const * args) {
            if (num != 1) throw corrupted_stream_exception();
            bool synthetic = d.read_bool();
            return mk_sorry(args[0], synthetic);
        });
}

void finalize_sorry() {
    delete g_sorry_opcode;
    delete g_sorry_name;
}

expr mk_sorry(expr const & ty, bool synthetic) {
    return mk_macro(macro_definition(new sorry_macro_cell(synthetic)), 1, &ty);
}
bool is_sorry(expr const & e) {
    return is_macro(e) && macro_num_args(e) == 1 && dynamic_cast<sorry_macro_cell const *>(macro_def(e).raw());
}
bool is_synthetic_sorry(expr const & e) {
    return is_sorry(e) && static_cast<sorry_macro_cell const *>(macro_def(e).raw())->is_synthetic();
}

bool has_synthetic_sorry(expr const & ex) {
    return !!find(ex, [] (expr const & e, unsigned) { return is_synthetic_sorry(e); });
}

bool has_sorry(expr const & ex) {
    return !!find(ex, [] (expr const & e, unsigned) { return is_sorry(e); });
}

bool has_sorry(declaration const & decl) {
    return has_sorry(decl.get_type()) || (decl.is_definition() && has_sorry(decl.get_value()));
}

expr const & sorry_type(expr const & sry) {
    return macro_arg(sry, 0);
}

bool has_sorry(environment const & env) {
    bool found_sorry = false;
    env.for_each_declaration([&] (declaration const & decl) {
        if (!found_sorry && has_sorry(decl)) found_sorry = true;
    });
    return found_sorry;
}
}




// ========== metavar_context.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/local_context.h"

namespace lean {
class metavar_decl {
    local_context m_context;
    expr          m_type;
    friend class metavar_context;
    metavar_decl(local_context const & ctx, expr const & type):m_context(ctx), m_type(type) {}
public:
    metavar_decl() {}
    expr const & get_type() const { return m_type; }
    local_context const & get_context() const { return m_context; }
};

bool is_metavar_decl_ref(level const & l);
bool is_metavar_decl_ref(expr const & e);

name get_metavar_decl_ref_suffix(level const & l);
name get_metavar_decl_ref_suffix(expr const & e);

class metavar_context {
    name_map<metavar_decl>    m_decls;
    name_map<level>           m_uassignment;
    name_map<expr>            m_eassignment;

    struct interface_impl;
    friend struct interface_impl;
    expr mk_metavar_decl(optional<name> const & pp_n, local_context const & ctx, expr const & type);
public:
    level mk_univ_metavar_decl();

    expr mk_metavar_decl(local_context const & ctx, expr const & type) {
        return mk_metavar_decl(optional<name>(), ctx, type);
    }
    expr mk_metavar_decl(name const & pp_name, local_context const & ctx, expr const & type) {
        return mk_metavar_decl(optional<name>(pp_name), ctx, type);
    }

    optional<metavar_decl> find_metavar_decl(expr const & mvar) const;

    metavar_decl const & get_metavar_decl(expr const & mvar) const;

    /** \brief Return the local_decl for `n` in the local context for the metavariable `mvar`
        \pre is_metavar(mvar) */
    optional<local_decl> find_local_decl(expr const & mvar, name const & n) const;

    local_decl get_local_decl(expr const & mvar, name const & n) const;

    /** \brief Return the local_decl_ref for `n` in the local context for the metavariable `mvar`

        \pre is_metavar(mvar)
        \pre find_metavar_decl(mvar)
        \pre find_metavar_decl(mvar)->get_context().get_local_decl(n) */
    expr get_local(expr const & mvar, name const & n) const;

    bool is_assigned(level const & l) const {
        lean_assert(is_metavar_decl_ref(l));
        return m_uassignment.contains(meta_id(l));
    }

    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar_decl_ref(m));
        return m_eassignment.contains(mlocal_name(m));
    }

    void assign(level const & u, level const & l);
    void assign(expr const & e, expr const & v);

    level instantiate_mvars(level const & l);
    expr instantiate_mvars(expr const & e, bool postpone_push_delayed = false);

    bool has_assigned(level const & l) const;
    bool has_assigned(levels const & ls) const;
    bool has_assigned(expr const & e) const;

    optional<level> get_assignment(level const & l) const;
    optional<expr> get_assignment(expr const & e) const;

    /** \brief Instantiate the assigned meta-variables in the type of \c m
        \pre get_metavar_decl(m) is not none */
    void instantiate_mvars_at_type_of(expr const & m);

    /** \brief Return true iff \c ctx is well-formed with respect to this metavar context.
        That is, every metavariable ?M occurring in \c ctx is declared here, and
        for every metavariable ?M occurring in a declaration \c d, the context of ?M
        must be a subset of the declarations declared *before* \c d.

        \remark This method is used for debugging purposes. */
    bool well_formed(local_context const & ctx) const;

    /** \brief Return true iff all metavariables ?M in \c e are declared in this metavar context,
        and context of ?M is a subset of \c ctx */
    bool well_formed(local_context const & ctx, expr const & e) const;

    friend bool is_eqp(metavar_context const & ctx1, metavar_context const & ctx2) {
        return
            is_eqp(ctx1.m_decls, ctx2.m_decls) &&
            is_eqp(ctx1.m_uassignment, ctx2.m_uassignment) &&
            is_eqp(ctx1.m_eassignment, ctx2.m_eassignment);
    }
};

/** \brief Check whether the local context lctx is well-formed and well-formed with respect to \c mctx.
    \remark This procedure is used for debugging purposes. */
bool well_formed(local_context const & lctx, metavar_context const & mctx);

/** \brief Check whether \c e is well-formed with respect to \c lctx and \c mctx. */
bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e);

void initialize_metavar_context();
void finalize_metavar_context();
}




// ========== metavar_context.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/for_each_fn.h"
#include "library/metavar_util.h"
#include "library/metavar_context.h"

namespace lean {
static name *       g_meta_prefix;
static expr *       g_dummy_type;

static expr mk_meta_ref(name const & n, optional<name> const & pp_n) {
    if (pp_n)
        return mk_metavar(n, *pp_n, *g_dummy_type);
    else
        return mk_metavar(n, *g_dummy_type);
}

bool is_metavar_decl_ref(level const & u) {
    return is_meta(u) && is_prefix_of(*g_meta_prefix, meta_id(u));
}

bool is_metavar_decl_ref(expr const & e) {
    return is_metavar(e) && mlocal_type(e) == *g_dummy_type;
}

name get_metavar_decl_ref_suffix(level const & u) {
    lean_assert(is_metavar_decl_ref(u));
    return meta_id(u).replace_prefix(*g_meta_prefix, name());
}

name get_metavar_decl_ref_suffix(expr const & e) {
    lean_assert(is_metavar_decl_ref(e));
    return mlocal_name(e).replace_prefix(*g_meta_prefix, name());
}

// TODO(Leo): fix this
static name mk_meta_decl_name() {
    return mk_tagged_fresh_name(*g_meta_prefix);
}

level metavar_context::mk_univ_metavar_decl() {
    // TODO(Leo): should use name_generator
    return mk_meta_univ(mk_meta_decl_name());
}

expr metavar_context::mk_metavar_decl(optional<name> const & pp_n, local_context const & ctx, expr const & type) {
    // TODO(Leo): should use name_generator
    name n = mk_meta_decl_name();
    m_decls.insert(n, metavar_decl(ctx, head_beta_reduce(type)));
    return mk_meta_ref(n, pp_n);
}

optional<metavar_decl> metavar_context::find_metavar_decl(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto r = m_decls.find(mlocal_name(e)))
        return optional<metavar_decl>(*r);
    else
        return optional<metavar_decl>();
}

metavar_decl const & metavar_context::get_metavar_decl(expr const & e) const {
    if (auto r = m_decls.find(mlocal_name(e)))
        return *r;
    else
        throw exception("unknown metavariable");
}

optional<local_decl> metavar_context::find_local_decl(expr const & mvar, name const & n) const {
    auto mdecl = find_metavar_decl(mvar);
    if (!mdecl) return optional<local_decl>();
    return mdecl->get_context().find_local_decl(n);
}

local_decl metavar_context::get_local_decl(expr const & mvar, name const & n) const {
    return get_metavar_decl(mvar).get_context().get_local_decl(n);
}

expr metavar_context::get_local(expr const & mvar, name const & n) const {
    return get_local_decl(mvar, n).mk_ref();
}

void metavar_context::assign(level const & u, level const & l) {
    m_uassignment.insert(meta_id(u), l);
}

void metavar_context::assign(expr const & e, expr const & v) {
    m_eassignment.insert(mlocal_name(e), v);
}

optional<level> metavar_context::get_assignment(level const & l) const {
    lean_assert(is_metavar_decl_ref(l));
    if (auto v = m_uassignment.find(meta_id(l)))
        return some_level(*v);
    else
        return none_level();
}

optional<expr> metavar_context::get_assignment(expr const & e) const {
    lean_assert(is_metavar_decl_ref(e));
    if (auto v = m_eassignment.find(mlocal_name(e)))
        return some_expr(*v);
    else
        return none_expr();
}

struct metavar_context::interface_impl {
    metavar_context & m_ctx;
    interface_impl(metavar_context const & ctx):m_ctx(const_cast<metavar_context&>(ctx)) {}

    static bool is_mvar(level const & l) { return is_metavar_decl_ref(l); }
    bool is_assigned(level const & l) const { return m_ctx.is_assigned(l); }
    optional<level> get_assignment(level const & l) const { return m_ctx.get_assignment(l); }
    void assign(level const & u, level const & v) { m_ctx.assign(u, v); }

    static bool is_mvar(expr const & e) { return is_metavar_decl_ref(e); }
    bool is_assigned(expr const & e) const { return m_ctx.is_assigned(e); }
    optional<expr> get_assignment(expr const & e) const { return m_ctx.get_assignment(e); }
    void assign(expr const & m, expr const & v) { m_ctx.assign(m, v); }

    bool in_tmp_mode() const { return false; }
};


bool metavar_context::has_assigned(level const & l) const {
    return ::lean::has_assigned(interface_impl(*this), l);
}

bool metavar_context::has_assigned(expr const & e) const {
    return ::lean::has_assigned(interface_impl(*this), e);
}

level metavar_context::instantiate_mvars(level const & l) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, l);
}

expr metavar_context::instantiate_mvars(expr const & e, bool postpone_push_delayed) {
    interface_impl impl(*this);
    return ::lean::instantiate_mvars(impl, e, postpone_push_delayed);
}

void metavar_context::instantiate_mvars_at_type_of(expr const & m) {
    metavar_decl d = get_metavar_decl(m);
    expr type      = d.get_type();
    expr new_type  = instantiate_mvars(type);
    if (new_type != type) {
        m_decls.insert(mlocal_name(m), metavar_decl(d.get_context(), new_type));
    }
}

template<typename C>
static bool well_formed_metavar_occs(expr const & e, C const & ds, metavar_context const & ctx) {
    bool ok = true;
    for_each(e, [&](expr const & e, unsigned) {
            if (!ok) return false;
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e)) {
                if (auto d = ctx.find_metavar_decl(e)) {
                    if (!d->get_context().is_subset_of(ds)) {
                        /* invalid metavariable context */
                        ok = false;
                        return false;
                    }
                } else {
                    /* undefined metavariable */
                    ok = false;
                    return false;
                }
            }
            return true;
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx) const {
    bool ok = true;
    name_set visited;
    ctx.for_each([&](local_decl const & d) {
            if (!well_formed_metavar_occs(d.get_type(), visited, *this)) {
                ok = false;
                lean_unreachable();
            }
            if (auto v = d.get_value()) {
                if (!well_formed_metavar_occs(*v, visited, *this)) {
                    ok = false;
                    lean_unreachable();
                }
            }
            visited.insert(d.get_name());
        });
    return ok;
}

bool metavar_context::well_formed(local_context const & ctx, expr const & e) const {
    return well_formed_metavar_occs(e, ctx, *this);
}

bool well_formed(local_context const & lctx, metavar_context const & mctx) {
    if (!lctx.well_formed()) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx)) {
        lean_unreachable();
        return false;
    }
    return true;
}

bool well_formed(local_context const & lctx, metavar_context const & mctx, expr const & e) {
    if (!lctx.well_formed(e)) {
        lean_unreachable();
        return false;
    }
    if (!mctx.well_formed(lctx, e)) {
        lean_unreachable();
        return false;
    }
    return true;
}

void initialize_metavar_context() {
    g_meta_prefix = new name("_mlocal");
    register_name_generator_prefix(*g_meta_prefix);
    g_dummy_type  = new expr(mk_constant(name::mk_internal_unique_name()));
}

void finalize_metavar_context() {
    delete g_meta_prefix;
    delete g_dummy_type;
}
}




// ========== metavar_util.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/replace_visitor.h"
#include "library/delayed_abstraction.h"

namespace lean {
/*
Helper functions for metavariable assignments.
The template parameter CTX must be an object that
provides the following API:

bool is_mvar(level const & l) const;
bool is_assigned(level const & l) const;
optional<level> get_assignment(level const & l) const;
void assign(level const & u, level const & v);

bool is_mvar(expr const & e) const;
bool is_assigned(expr const & e) const;
optional<expr> get_assignment(expr const & e) const;
void assign(expr const & m, expr const & v);

push_delayed_abstraction

bool in_tmp_mode() const;
*/

template<typename CTX>
bool has_assigned(CTX const & ctx, level const & l) {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (ctx.is_mvar(l) && ctx.is_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

template<typename CTX>
bool has_assigned(CTX const & ctx, levels const & ls) {
    for (level const & l : ls) {
        if (has_assigned(ctx, l))
            return true;
    }
    return false;
}

template<typename CTX>
bool has_assigned(CTX const & ctx, expr const & e) {
    if (!has_expr_metavar(e) && !has_univ_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((ctx.is_mvar(e) && ctx.is_assigned(e)) ||
                (is_constant(e) && has_assigned(ctx, const_levels(e))) ||
                (is_sort(e) && has_assigned(ctx, sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            if (is_metavar(e))
                return false; // do not search type
            return true; // continue search
        });
    return found;
}

template<typename CTX>
level instantiate_mvars(CTX & ctx, level const & l) {
    if (!has_assigned(ctx, l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (ctx.is_mvar(l)) {
                if (auto v1 = ctx.get_assignment(l)) {
                    level v2 = instantiate_mvars(ctx, *v1);
                    if (*v1 != v2) {
                        if (!ctx.in_tmp_mode())
                            ctx.assign(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

template<typename CTX>
class instantiate_mvars_fn : public replace_visitor {
    CTX & m_ctx;
    bool  m_postpone_push_delayed;
    bool  m_found_delayed_abstraction{false};


    level visit_level(level const & l) {
        return instantiate_mvars(m_ctx, l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) override {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) override {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) override {
        return update_mlocal(e, visit(mlocal_type(e)));
    }

    virtual expr visit_meta(expr const & m) override {
        if (m_ctx.is_mvar(m)) {
            if (auto v1 = m_ctx.get_assignment(m)) {
                if (!has_metavar(*v1)) {
                    return *v1;
                } else {
                    expr v2 = visit(*v1);
                    if (!m_ctx.in_tmp_mode() && v2 != *v1)
                        m_ctx.assign(m, v2);
                    return v2;
                }
            } else {
                return m;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (m_ctx.is_mvar(f)) {
            if (auto v = m_ctx.get_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_metavar(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) override {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        expr r = update_macro(e, new_args.size(), new_args.data());
        if (is_delayed_abstraction(r)) {
            if (m_postpone_push_delayed) {
                m_found_delayed_abstraction = true;
            } else {
                return push_delayed_abstraction(r);
            }
        }
        return r;
    }

    virtual expr visit(expr const & e) override {
        if (!has_expr_metavar(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_mvars_fn(CTX & ctx, bool postpone_push_delayed):m_ctx(ctx), m_postpone_push_delayed(postpone_push_delayed) {}
    expr operator()(expr const & e) {
        expr r = visit(e);
        if (m_found_delayed_abstraction) {
            buffer<name> ns; buffer<expr> es;
            r = append_delayed_abstraction(r, ns, es);
        }
        return r;
    }
};

template<typename CTX>
expr instantiate_mvars(CTX & ctx, expr const & e, bool postpone_push_delayed) {
    if (!has_assigned(ctx, e))
        return e;
    expr r = instantiate_mvars_fn<CTX>(ctx, postpone_push_delayed)(e);
    lean_assert(!has_assigned(ctx, r));
    return r;
}
}




// ========== message_builder.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "library/io_state_stream.h"
#include "library/messages.h"
#include "library/type_context.h"

namespace lean {

/** Builder for a message object. */
class message_builder {
    std::shared_ptr<abstract_type_context> m_tc;
    std::string                            m_file_name;
    pos_info                               m_pos;
    optional<pos_info>                     m_end_pos;
    message_severity                       m_severity;
    std::string                            m_caption;
    std::shared_ptr<string_output_channel> m_text;
    io_state_stream                        m_text_stream;

public:
    message_builder(std::shared_ptr<abstract_type_context> const & tc,
                    environment const & env, io_state const & ios,
                    std::string const & file_name, pos_info const & pos,
                    message_severity severity);
    message_builder(environment const & env, io_state const & ios,
                    std::string const & file_name, pos_info const & pos,
                    message_severity severity);

    message build();
    void report();

    message_builder & set_file_name(std::string const & file_name) { m_file_name = file_name; return *this; }
    message_builder & set_pos(pos_info const & pos) { m_pos = pos; return *this; }
    message_builder & set_end_pos(pos_info const & pos) { m_end_pos = pos; return *this; }
    message_builder & set_severity(message_severity severity) { m_severity = severity; return *this; }
    message_builder & set_caption(std::string const & caption) { m_caption = caption; return *this; }

    formatter const & get_formatter() const { return m_text_stream.get_formatter(); }

    io_state_stream & get_text_stream() { return m_text_stream; }
    template <typename T>
    message_builder & operator<<(T const & t) { m_text_stream << t; return *this; }

    message_builder & set_exception(std::exception const & ex, bool use_pos = true);
};

}




// ========== message_builder.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/message_builder.h"
#include "library/type_context.h"

namespace lean {

message_builder::message_builder(std::shared_ptr<abstract_type_context> const & tc,
                                 environment const & env, io_state const & ios,
                                 std::string const & file_name, const pos_info & pos,
                                 message_severity severity) :
    m_tc(tc), m_file_name(file_name), m_pos(pos), m_severity(severity),
    m_caption(), m_text(std::make_shared<string_output_channel>()),
    m_text_stream(env, ios.get_formatter_factory()(env, ios.get_options(), *tc), m_text) {}

message_builder::message_builder(environment const & env, io_state const & ios,
                                 std::string const & file_name, pos_info const & pos,
                                 message_severity severity) :
        message_builder(std::make_shared<type_context_old>(env, ios.get_options()),
                        env, ios, file_name, pos, severity) {}

message message_builder::build() {
    auto text = m_text->str();
    if (!text.empty() && *text.rbegin() == '\n')
        text = text.substr(0, text.size() - 1);
    return message(m_file_name, m_pos, m_end_pos, m_severity, m_caption, text);
}

message_builder & message_builder::set_exception(std::exception const & ex, bool use_pos) {
    if (auto pos_ex = dynamic_cast<exception_with_pos const *>(&ex)) {
        if (use_pos && pos_ex->get_pos()) {
            m_pos = *pos_ex->get_pos();
        }
    }
    if (auto ext_ex = dynamic_cast<ext_exception const *>(&ex)) {
        *this << *ext_ex;
    } else if (auto f_ex = dynamic_cast<formatted_exception const *>(&ex)) {
        *this << f_ex->pp();
    } else {
        *this << ex.what();
    }
    return *this;
}

void message_builder::report() {
    report_message(build());
}

}




// ========== profiling.h ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <chrono>
#include <util/sexpr/options.h>

namespace lean {

using second_duration = std::chrono::duration<double>;

bool get_profiler(options const &);
second_duration get_profiling_threshold(options const &);

void initialize_profiling();
void finalize_profiling();

}




// ========== profiling.cpp ==========

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/profiling.h"
#include "util/sexpr/option_declarations.h"

#ifndef LEAN_DEFAULT_PROFILER
#define LEAN_DEFAULT_PROFILER false
#endif

#ifndef LEAN_DEFAULT_PROFILER_THRESHOLD
#define LEAN_DEFAULT_PROFILER_THRESHOLD 0
#endif

namespace lean {

static name * g_profiler           = nullptr;
static name * g_profiler_threshold = nullptr;

bool get_profiler(options const & opts) {
    return opts.get_bool(*g_profiler, LEAN_DEFAULT_PROFILER);
}

second_duration get_profiling_threshold(options const & opts) {
    return second_duration(opts.get_double(*g_profiler_threshold, LEAN_DEFAULT_PROFILER_THRESHOLD));
}

void initialize_profiling() {
    g_profiler           = new name{"profiler"};
    g_profiler_threshold = new name{"profiler", "threshold"};
    register_bool_option(*g_profiler, LEAN_DEFAULT_PROFILER, "(profiler) profile tactics and vm_eval command");
    register_double_option(*g_profiler_threshold, LEAN_DEFAULT_PROFILER_THRESHOLD,
                           "(profiler) threshold in seconds, profiling times under threshold will not be reported");
}

void finalize_profiling() {
    delete g_profiler;
    delete g_profiler_threshold;
}

}




// ========== expr_pair.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/hash.h"
#include "kernel/expr_pair.h"
#include "library/expr_lt.h"

namespace lean {
inline bool is_lt(expr_pair const & p1, expr_pair const & p2, bool use_hash) {
    return is_lt(p1.first, p2.first, use_hash) || (p1.first == p2.first && is_lt(p1.second, p2.second, use_hash));
}
struct expr_pair_quick_cmp {
    int operator()(expr_pair const & p1, expr_pair const & p2) const { return is_lt(p1, p2, true) ? -1 : (p1 == p2 ? 0 : 1);  }
};
}




// ========== register_module.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/script_state.h"
#include "library/kernel_bindings.h"
#include "library/resolve_macro.h"
#include "library/private.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/unifier.h"
#include "library/scoped_ext.h"
#include "library/match.h"
#include "library/reducible.h"

namespace lean {
inline void open_core_module(lua_State * L) {
    open_kernel_module(L);
    open_resolve_macro(L);
    open_private(L);
    open_placeholder(L);
    open_aliases(L);
    open_choice(L);
    open_scoped_ext(L);
    open_unifier(L);
    open_explicit(L);
    open_match(L);
    open_reducible(L);
}
inline void register_core_module() {
    script_state::register_module(open_core_module);
}
}




// ========== expr_pair_maps.h ==========

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include "kernel/expr.h"
#include "library/expr_pair.h"
namespace lean {
// Map based on structural equality
template<typename T>
using expr_pair_struct_map = std::unordered_map<expr_pair, T, expr_pair_hash, expr_pair_eq>;
}

