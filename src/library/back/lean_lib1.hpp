

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
