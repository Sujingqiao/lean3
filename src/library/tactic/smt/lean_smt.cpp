

// ========== hinst_lemmas.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_multi_map.h"
#include "kernel/environment.h"
#include "library/expr_lt.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"

namespace lean {
/** \brief Annotate \c e as a pattern hint */
expr mk_pattern_hint(expr const & e);
/** \brief Return true iff \c e is an annotated pattern */
bool is_pattern_hint(expr const & e);
/** \brief Return the actual pattern */
expr const & get_pattern_hint_arg(expr const & e);
/** \brief Return true iff \c e contains pattern hints */
bool has_pattern_hints(expr const & e);

/** \brief Hint for the pattern inference procedure.
    It should not consider/infer patterns containing the constant \c n. */
environment add_no_inst_pattern_attribute(environment const & env, name const & n);
/** \brief Return true if constant \c n is marked as [no_pattern] in the given environment. */
bool has_no_inst_pattern_attribute(environment const & env, name const & n);
/** \brief Return the set of constants marked as no-patterns */
name_set get_no_inst_patterns(environment const & env);

typedef list<expr> multi_pattern;

/** Heuristic instantiation lemma */
struct hinst_lemma {
    name                 m_id;
    unsigned             m_num_uvars{0};
    unsigned             m_num_mvars{0};
    list<multi_pattern>  m_multi_patterns;
    list<bool>           m_is_inst_implicit;
    list<expr>           m_mvars;
    expr                 m_prop;
    expr                 m_proof;
    /* term that was used to generate hinst_lemma, it is only used for tracing and profiling */
    expr                 m_expr;
};

inline int multi_pattern_cmp(multi_pattern const & m1, multi_pattern const & m2) {
    return cmp<expr>(m1, m2, expr_quick_cmp());
}

struct hinst_lemma_cmp {
    int operator()(hinst_lemma const & l1, hinst_lemma const & l2) const {
        int r = expr_quick_cmp()(l1.m_prop, l2.m_prop);
        if (r != 0) return r;
        return cmp(l1.m_multi_patterns, l2.m_multi_patterns, multi_pattern_cmp);
    }
};

typedef rb_tree<hinst_lemma, hinst_lemma_cmp> hinst_lemmas;

/** \brief Try to compute multipatterns for declaration \c c using the current environment configuration. */
list<multi_pattern> mk_multipatterns(environment const & env, io_state const & ios, name const & c);

/** \brief Create a (local) heuristic instantiation lemma for \c H.
    The maximum number of steps is extracted from the blast config object.

    \c md_norm is the transparency_mode used for normalizing the type of the lemma.
    The idea is to unfold the lemmas using the given transparency mode. */
hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, expr const & H, bool simp = false);
hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, name const & n, bool simp = false);

format pp_hinst_lemma(formatter const & fmt, hinst_lemma const & h);

inline io_state_stream const & operator<<(io_state_stream const & out, hinst_lemma const & e) {
    out << mk_pair(pp_hinst_lemma(out.get_formatter(), e), out.get_options());
    return out;
}

bool is_hinst_lemma(vm_obj const & o);
hinst_lemma const & to_hinst_lemma(vm_obj const & o);
vm_obj to_obj(hinst_lemma const & s);

bool is_hinst_lemmas(vm_obj const & o);
hinst_lemmas const & to_hinst_lemmas(vm_obj const & o);
vm_obj to_obj(hinst_lemmas const & s);

void initialize_hinst_lemmas();
void finalize_hinst_lemmas();
}




// ========== hinst_lemmas.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "library/expr_lt.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/normalize.h"
#include "library/idx_metavar.h"
#include "library/type_context.h"
#include "library/annotation.h"
#include "library/exception.h"
#include "library/replace_visitor.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/smt/hinst_lemmas.h"

#ifndef LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS
#define LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS 1024
#endif

namespace lean {
/*
Step 1: Selecting which variables we should track.
Given (H : Pi (a_1 : A_1) ... (a_n : A_n), B) where B is not a Pi,
we use the following procedure to decide which a_i's must be in
patterns used by heuristic instantiation.
- We say an a_i that must occur in a pattern is "trackable".
- The set of "trackable" a_i's is the least fix point of
  a) If there is j > i, a_j is trackable, type(a_j) depends on a_i,
     and type(a_i) is not higher-order, then
     a_i is NOT trackable.
     Reason: we can infer a_i from a_j using type inference.
  b) a_i is a proposition -> a_i is NOT trackable.
     Reason: we leave a_i as hypothesis whenever we instantiate H.
  c) a_i is instance implicit -> a_i is NOT trackable.
     We should use type class resolution to infer a_i.

Remark: we say a (multi-)pattern for H is valid iff it contains all
trackable a_i's.
We define the set of "residue" hypotheses a_i as the least fix point of
  a) a_i is a proposition
  b) a_i is not inst_implicit
  c) a_i is not trackable
  d) a_i is not a proposition and there is no j > i s.t. a_j is not residue
     and type(a_j) depends on a_i, and type(a_i) is not higher-order

That is, if a_i is a "residue" hypothesis, we cannot infer it
by using type inference or type class resolution.
Residue hypotheses are the hypotheses for any instance of H produced by
the heuristic instantiation module.

Step 2a: H contains user-provided pattern hints
The user may provide pattern hints by annotating subterms of H using
the notation (:t:).
Example: The term (g x y) is a pattern hint at (H : forall x y, f (:g x y:) = x).

Let S be the set of patterns hints contained in H.
Then, a multi-pattern P is any subset of S s.t.
    a) P contains all trackable a_i's in H
    b) There is no strict subset of P that contains all trackable a_i's in H

If S is not empty, Lean will generate an error if there is no multi-pattern P for S.
The option pattern.max_steps is a threshold on the number of steps performed
Lean will generate an error if more than pattern.max_steps are performed while processing the set S.

Step 2b: H does NOT contain user-provided pattern hints.
When pattern hints are not provided, Lean uses a heuristic for selecting patterns.

- Lean will only consider terms that do NOT contain constants marked with the hint attribute
  [no_pattern]. In the standard library, we use this attribute to mark constants such as
  'and', 'or', 'not', 'iff', 'eq', 'heq', etc.

- Lean will look for candidate patterns in B and residue hypotheses.
Actually, it uses the following approach (TODO(Leo): should we provide options to control it?)
   1) Lean tries to find multi-patterns in B (only). If it finds at least one, then it is done, otherwise
   2) Lean tries to find multi-patterns in residue hypotheses only.
      If it finds at leat one, then it is done, otherwise
   3) Lean tries to find multi-patterns using residue hypotheses and B.
      If it can't find at least one, it signs an error.

- So, from now on, we will assume T is the set of terms where we will look for patterns.
We use trackable(p) to denote the set of trackable variables in p.
Lean will try to find "minimal" patterns and rank candidates in the following way
     Given terms p and q where both do not contain [no_pattern] constants, we say
     term p is "better" than q
     IFF
       1) trackable(p) is a strict superset of trackable(q) OR
       2) trackable(p) == trackable(q), but p is as subterm of q.

Given T, we collect a set of candidates C s.t., for each c_1 in C, there is no c_2 in C s.t. c_2 is better than c_1.
If there is c in C s.t. c contains all trackable a_i's, then all such c in C is our set of patterns (done).
To mimize the number of multi-patterns to be considered, we delete from C
any candidate c_1 in C if there is a c_2 in C s.t.
trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).

We say a subset M of C is a multi-pattern if M contains all trackable variables.

We say a multi-pattern M is minimal if no strict subset of M is a multi-pattern.
If the set of minimal multi-patterns for C is bigger than `pattern.max`, then we generate an error.
That is, the user should provide pattern-hints.
*/

static name * g_no_inst_pattern_attr = nullptr;

static basic_attribute const & get_no_inst_pattern_attribute() {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_no_inst_pattern_attr));
}

bool has_no_inst_pattern_attribute(environment const & env, name const & d) {
    return has_attribute(env, *g_no_inst_pattern_attr, d);
}

environment add_no_inst_pattern_attribute(environment const & env, name const & n) {
    return get_no_inst_pattern_attribute().set(env, get_dummy_ios(), n, LEAN_DEFAULT_PRIORITY, true);
}

name_set get_no_inst_patterns(environment const & env) {
    buffer<name> ds;
    get_no_inst_pattern_attribute().get_instances(env, ds);
    return to_name_set(ds);
}

static name * g_pattern_hint = nullptr;

bool is_pattern_hint(expr const & e) { return is_annotation(e, *g_pattern_hint); }
expr const & get_pattern_hint_arg(expr const & e) { lean_assert(is_pattern_hint(e)); return get_annotation_arg(e); }
bool has_pattern_hints(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_pattern_hint(e); }));
}
expr mk_pattern_hint(expr const & e) {
    if (has_pattern_hints(e))
        throw exception("invalid pattern hint, nested patterns hints are not allowed");
    if (!is_app(e))
        throw generic_exception(e, "invalid pattern hint, pattern hints must be applications");
    return mk_annotation(*g_pattern_hint, e);
}

typedef rb_tree<unsigned, unsigned_cmp> idx_metavar_set;

static bool is_higher_order(type_context_old & ctx, expr const & e) {
    /* Remark: is it too expensive to use ctx.relaxed_whnf here? */
    return is_pi(ctx.whnf(ctx.infer(e)));
}

/** \brief Given type of the form (Pi (a_1 : A_1) ... (a_n : A_n), B) (or reducible to something of this form),
    create n idx_metavars (one for each a_i), store the meta-variables in mvars,
    and store in trackable and residue the subsets of these meta-variables as
    described in the beginning of this file. Then returns B (instantiated with the new meta-variables) */
expr extract_trackable(type_context_old & ctx, expr const & type,
                       buffer<expr> & mvars,
                       buffer<bool> & inst_implicit_flags,
                       idx_metavar_set & trackable, idx_metavar_set & residue) {
    // 1. Create mvars and initialize trackable and residue sets
    expr it = type;
    while (true) {
        if (!is_pi(it)) {
            expr new_it = ctx.relaxed_whnf(it);
            if (!is_pi(new_it))
                break; // consumed all arguments
            it = new_it;
        }
        lean_assert(is_pi(it));
        expr new_mvar = ctx.mk_tmp_mvar(binding_domain(it));
        lean_assert(is_idx_metavar(new_mvar));
        mvars.push_back(new_mvar);
        bool is_inst_implicit = binding_info(it).is_inst_implicit();
        inst_implicit_flags.push_back(is_inst_implicit);
        bool is_prop          = ctx.is_prop(binding_domain(it));
        if (!is_inst_implicit) {
            unsigned midx = to_meta_idx(new_mvar);
            if (is_prop)
                residue.insert(midx);
            else
                trackable.insert(midx);
        }
        it = instantiate(binding_body(it), new_mvar);
    }
    expr     B = it;
    unsigned n = mvars.size();
    // 2. Compute trackable fixpoint
    bool modified;
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!trackable.contains(midx))
                continue; // variable is not in the trackable set
            // There is no j > i, mvars[j] is trackable, type(mvars[j]) depends on mvars[i],
            // and type(mvars[i]) is not higher-order.
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (trackable.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            trackable.erase(midx);
            modified = true;
        }
    } while (modified);
    // 3. Compute residue fixpoint
    do {
        modified = false;
        for (unsigned i = 0; i < n; i++) {
            unsigned midx = to_meta_idx(mvars[i]);
            if (!residue.contains(midx))
                continue; // variable is not in the residue set
            // There is no j > i s.t. mvars[j] is not residue
            // and type(mvars[j]) depends on mvars[i], and type(mvars[i]) is not higher-order
            if (is_higher_order(ctx, mvars[i]))
                continue;
            unsigned j = i+1;
            for (; j < n; j++) {
                if (!residue.contains(to_meta_idx(mvars[j])) &&
                    occurs(mvars[i], ctx.infer(mvars[j]))) {
                    // we can infer mvars[i] using type inference
                    break;
                }
            }
            if (j == n)
                continue;
            residue.erase(midx);
            modified = true;
        }
    } while (modified);
    return B;
}

static expr dsimp(type_context_old & ctx, transparency_mode md, expr const & e) {
    /* We used to use ::lean::normalize here, but it was bad since it would unfold type class instances.
       First, this may be a performance problem.
       Second, it would expose a problem with the way we define some algebraic structures.
       See discussion at ring.lean.
    */
    defeq_can_state dcs;
    dsimp_config cfg;
    cfg.m_md                 = md;
    cfg.m_canonize_instances = false;
    cfg.m_max_steps          = 1000000; /* TODO(Leo): add parameter? */
    cfg.m_eta                = true;
    return dsimplify_fn(ctx, dcs, simp_lemmas_for(), list<name>(), cfg)(e);
}

struct mk_hinst_lemma_fn {
    type_context_old &     m_ctx;
    transparency_mode  m_md_norm;
    name_set           m_no_inst_patterns;
    expr               m_H;
    unsigned           m_num_uvars;
    unsigned           m_max_steps;
    /* If m_simp is true, the pattern inference procedure assumes the given lemma is a [simp] lemma.
       That is, the conclusion is of the form (t ~ s), and it will try to use t as a pattern. */
    bool               m_simp;

    buffer<expr>       m_mvars;
    idx_metavar_set    m_trackable;
    idx_metavar_set    m_residue;
    unsigned           m_num_steps;
    name               m_id;

    mk_hinst_lemma_fn(type_context_old & ctx, transparency_mode md_norm, expr const & H,
                      unsigned num_uvars, unsigned max_steps, bool simp,
                      name const & id):
        m_ctx(ctx), m_md_norm(md_norm),
        m_no_inst_patterns(get_no_inst_patterns(ctx.env())),
        m_H(H), m_num_uvars(num_uvars), m_max_steps(max_steps),
        m_simp(simp), m_id(id) {}

    struct candidate {
        expr            m_expr;
        idx_metavar_set m_mvars;
        candidate() {}
        candidate(expr const & e):
            m_expr(e) {
            for_each(e, [&](expr const & e, unsigned) {
                    if (is_idx_metavar(e))
                        m_mvars.insert(to_meta_idx(e));
                    return true;
                });
        }
        candidate(expr const & e, idx_metavar_set const & mvars):m_expr(e), m_mvars(mvars) {}
    };

    struct candidate_lt {
        int operator()(candidate const & c1, candidate const & c2) const { return expr_quick_cmp()(c1.m_expr, c2.m_expr); }
    };

    typedef rb_tree<candidate, candidate_lt> candidate_set;

    expr normalize(expr const & e) {
        return dsimp(m_ctx, m_md_norm, e);
    }

    void collect_pattern_hints(expr const & e, candidate_set & s) {
        for_each(e, [&](expr const & e, unsigned) {
                if (is_pattern_hint(e)) {
                    expr hint = get_pattern_hint_arg(e);
                    // TODO(Leo): if hint was unfolded and is not an application anymore, we should
                    // report to user this fact.
                    if (is_app(hint)) {
                        s.insert(candidate(normalize(hint)));
                    }
                    return false;
                }
                return true;
            });
    }

    candidate_set collect_pattern_hints(buffer<expr> const & mvars, buffer<expr> const & residue, expr const & B) {
        candidate_set s;
        for (expr const & mvar : mvars)
            collect_pattern_hints(m_ctx.infer(mvar), s);
        for (expr const & r : residue)
            collect_pattern_hints(m_ctx.infer(r), s);
        collect_pattern_hints(B, s);
        return s;
    }

    candidate_set m_candidates;

    void save_candidates(candidate_set const & s) {
        m_candidates.merge(s);
    }

    candidate_set collect_core(expr const & a) {
        switch (a.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:   case expr_kind::Constant:
        case expr_kind::Meta:   case expr_kind::Local:
        case expr_kind::Pi:
            return candidate_set();
        case expr_kind::Let:
            /* TODO(Leo): Decide whether we should support let-expressions or not.
               IF we don't, then we should report this occurrence users. */
            return candidate_set();
        case expr_kind::Lambda:
            if (has_idx_metavar(a))
                return candidate_set(candidate(a));
            else
                return candidate_set();
        case expr_kind::Macro:
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                candidate_set s = collect_core(macro_arg(a, i));
                save_candidates(s);
            }
            return candidate_set();
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(a, args);
            buffer<candidate_set> arg_candidates;
            bool forbidden = !is_local(fn) && (!is_constant(fn) || m_no_inst_patterns.contains(const_name(fn)));
            if (forbidden) {
                for (expr const & arg : args) {
                    candidate_set s = collect_core(arg);
                    save_candidates(s);
                }
                return candidate_set();
            } else {
                candidate_set ss;
                idx_metavar_set mvars;
                for (expr const & arg : args) {
                    if (is_idx_metavar(arg)) {
                        if (m_trackable.contains(to_meta_idx(arg))) {
                            mvars.insert(to_meta_idx(arg));
                        }
                    } else {
                        candidate_set s = collect_core(arg);
                        s.for_each([&](candidate const & c) {
                                ss.insert(c);
                                mvars.merge(c.m_mvars);
                            });
                    }
                }
                if (ss.find_if([&](candidate const & c) { return mvars == c.m_mvars; })) {
                    return ss;
                } else if (!mvars.empty()) {
                    // a subsumes all children candidates
                    return candidate_set(candidate(a, mvars));
                } else {
                    return candidate_set();
                }
            }
        }}
        lean_unreachable();
    }

    candidate_set collect(expr const & a) {
        m_candidates = candidate_set();
        if (m_simp) {
            expr lhs, rhs;
            if (is_eq(a, lhs, rhs) || is_heq(a, lhs, rhs) || is_iff(a, lhs, rhs)) {
                m_candidates.insert(candidate(normalize(lhs)));
            }
        } else {
            save_candidates(collect_core(normalize(a)));
        }
        return m_candidates;
    }

    void mk_multi_patterns_core(unsigned i, buffer<candidate> const & s, buffer<expr> & mp, idx_metavar_set const & mvars, buffer<multi_pattern> & mps) {
        m_num_steps++;
        if (m_num_steps > m_max_steps)
            throw exception(sstream() << "pattern inference failed for '" << m_id << "', the maximum number (" << m_max_steps << ") of steps has been reached "
                            "(possible solutions: provide pattern hints using the notation '(: t :)' for marking subterms; increase threshold using option pattern.max_steps)");
        if (i == s.size())
            return;
        candidate const & c = s[i];
        if (!mvars.is_strict_superset(c.m_mvars)) {
            // candidate s[i] contributes with new variables
            unsigned sz = mp.size();
            mp.push_back(c.m_expr);
            idx_metavar_set new_mvars = mvars;
            new_mvars.merge(c.m_mvars);
            if (new_mvars.is_superset(m_trackable)) {
                // found multi-pattern
                mps.push_back(to_list(mp));
            } else {
                // include s[i]
                mk_multi_patterns_core(i+1, s, mp, new_mvars, mps);
            }
            mp.shrink(sz);
        }
        // do not include s[i];
        mk_multi_patterns_core(i+1, s, mp, mvars, mps);
    }

    /* If heuristic is true, then
       1. Give preference to unary patterns
       2. If there are no unary patterns, then
          a) delete any candidate c_1 if there is a c_2 s.t.
             trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).
          b) delete any candidate c_1 if there is a c_2 s.t.
             c_1 is a subterm of c_2, and c_2.m_vars is a strict superset of c_1.m_vars */
    list<multi_pattern> mk_multi_patterns_using(candidate_set s, bool heuristic) {
        if (heuristic) {
            buffer<multi_pattern> unit_patterns;
            s.for_each([&](candidate const & c) {
                    if (c.m_mvars.is_superset(m_trackable))
                        unit_patterns.push_back(to_list(c.m_expr));
                });
            if (!unit_patterns.empty()) {
                return to_list(unit_patterns);
            }
            buffer<candidate> to_delete;
            s.for_each([&](candidate const & c_1) {
                    if (s.find_if([&](candidate const & c_2) {
                                return
                                    //      a) delete any candidate c_1 if there is a c_2 s.t.
                                    //         trackable(c_1) == trackable(c_2) and weight(c_1) > weight(c_2).
                                    (c_1.m_mvars == c_2.m_mvars && get_weight(c_1.m_expr) > get_weight(c_2.m_expr)) ||
                                    //      b) delete any candidate c_1 if there is a c_2 s.t.
                                    //         c_1 is a subterm of c_2, and c_2.m_vars is a strict superset of c_1.m_vars
                                    (occurs(c_1.m_expr, c_2.m_expr) && c_2.m_mvars.is_strict_superset(c_1.m_mvars));
                            })) {
                        to_delete.push_back(c_1);
                    }
                });
            for (candidate const & c : to_delete) {
                s.erase(c);
            }
        }
        buffer<candidate> s_buffer;
        s.to_buffer(s_buffer);
        buffer<multi_pattern> mps;
        buffer<expr> mp;
        m_num_steps = 0;
        mk_multi_patterns_core(0, s_buffer, mp, idx_metavar_set(), mps);
        return to_list(mps);
    }

    expr replace_mvars(expr const & e, buffer<expr> const & subst) {
        return replace(e,
                       [&](expr const & e) {
                           if (!has_expr_metavar(e))
                               return some_expr(e);
                           if (is_idx_metavar(e))
                               return some_expr(subst[to_meta_idx(e)]);
                           else
                               return none_expr();
                       });
    }

    /* Create proof by pushing all residue hypotheses to the "end".
       Residue hypotheses are converted into local constants.
       Remaining metavariables are "renamed" (i.e., renumbered to avoid gaps due to residue hypotheses moved to the end).
       Trackable set is updated.
       subst will contain the mvars renaming */
    expr mk_proof(type_context_old::tmp_locals & locals, buffer<expr> & new_residue, buffer<expr> & subst) {
        unsigned j = 0;
        bool found_residue     = false;
        bool only_tail_residue = true;
        for (unsigned i = 0; i < m_mvars.size(); i++) {
            expr new_type = m_ctx.infer(m_mvars[i]);
            if (i != j)
                new_type = replace_mvars(new_type, subst);
            if (m_residue.contains(to_meta_idx(m_mvars[i]))) {
                found_residue = true;
                expr res      = locals.push_local("_x", new_type);
                new_residue.push_back(res);
                subst.push_back(res);
            } else {
                if (found_residue)
                    only_tail_residue = false;
                expr new_mvar;
                if (j == i) {
                    new_mvar = m_mvars[i];
                } else {
                    new_mvar = mk_idx_metavar(j, new_type);
                    if (m_trackable.contains(i)) {
                        m_trackable.erase(i);
                        m_trackable.insert(j);
                    }
                    m_mvars[j] = new_mvar;
                }
                j++;
                subst.push_back(new_mvar);
            }
        }
        m_mvars.shrink(j);
        if (only_tail_residue) {
            return mk_app(m_H, m_mvars);
        } else {
            return locals.mk_lambda(mk_app(m_H, subst));
        }
    }

    struct try_again_without_hints {};

    struct erase_hints_fn : public replace_visitor {
        virtual expr visit_macro(expr const & e) override {
            if (is_pattern_hint(e)) {
                return visit(get_annotation_arg(e));
            } else {
                return replace_visitor::visit_macro(e);
            }
        }
    };

    hinst_lemma operator()(bool erase_hints) {
        expr H_type = m_ctx.infer(m_H);
        if (erase_hints) {
            H_type = erase_hints_fn()(H_type);
        }
        buffer<bool> inst_implicit_flags;
        expr B      = extract_trackable(m_ctx, H_type, m_mvars, inst_implicit_flags, m_trackable, m_residue);
        lean_assert(m_mvars.size() == inst_implicit_flags.size());
        buffer<expr> subst;
        buffer<expr> residue_locals;
        type_context_old::tmp_locals locals(m_ctx);
        expr proof  = mk_proof(locals, residue_locals, subst);
        B           = replace_mvars(B, subst);
        candidate_set hints = collect_pattern_hints(m_mvars, residue_locals, B);
        list<multi_pattern> mps;
        if (!hints.empty()) {
            mps = mk_multi_patterns_using(hints, false);
        } else {
            if (has_pattern_hints(H_type)) {
                throw try_again_without_hints();
            }
            buffer<expr> places;
            candidate_set B_candidates = collect(B);
            if (auto r1 = mk_multi_patterns_using(B_candidates, true)) {
                mps = r1;
            } else if (!m_simp) {
                candidate_set residue_candidates;
                for (expr const & r : residue_locals) {
                    residue_candidates.merge(collect(m_ctx.infer(r)));
                }
                if (auto r2 = mk_multi_patterns_using(residue_candidates, true)) {
                    mps = r2;
                } else if (!residue_candidates.empty() && !B_candidates.empty()) {
                    candidate_set all_candidates = B_candidates;
                    all_candidates.merge(residue_candidates);
                    mps = mk_multi_patterns_using(all_candidates, true);
                }
            }
        }
        if (!mps) {
            throw exception(sstream() << "pattern inference failed for '" << m_id << "', "
                            "(solution: provide pattern hints using the notation '(: t :)' )");
        }
        hinst_lemma r;
        r.m_id               = m_id;
        r.m_num_uvars        = m_num_uvars;
        r.m_num_mvars        = m_mvars.size();
        r.m_multi_patterns   = mps;
        r.m_mvars            = to_list(m_mvars);
        r.m_is_inst_implicit = to_list(inst_implicit_flags);
        r.m_prop             = m_ctx.infer(proof);
        r.m_proof            = proof;
        r.m_expr             = m_H;
        return r;
    }
};

hinst_lemma mk_hinst_lemma_core(type_context_old & ctx, transparency_mode md_norm, expr const & H, unsigned num_uvars,
                                unsigned max_steps, bool simp, name const & id) {
    if (num_uvars == 0 && !is_pi(ctx.relaxed_whnf(ctx.infer(H)))) {
        hinst_lemma h;
        h.m_id    = id;
        h.m_proof = H;
        h.m_prop  = dsimp(ctx, md_norm, ctx.infer(h.m_proof));
        h.m_expr  = h.m_proof;
        return h;
    } else {
        try {
            type_context_old::tmp_mode_scope tscope(ctx, num_uvars, 0);
            bool erase_hints = false;
            return mk_hinst_lemma_fn(ctx, md_norm, H, num_uvars, max_steps, simp, id)(erase_hints);
        } catch (mk_hinst_lemma_fn::try_again_without_hints &) {
            type_context_old::tmp_mode_scope tscope(ctx, num_uvars, 0);
            try {
                bool erase_hints = true;
                return mk_hinst_lemma_fn(ctx, md_norm, H, num_uvars, max_steps, simp, id)(erase_hints);
            } catch (mk_hinst_lemma_fn::try_again_without_hints &) {
                lean_unreachable();
            }
        }
    }
}

static name * g_hinst_lemma_max_steps = nullptr;

unsigned get_hinst_lemma_max_steps(options const & o) {
    return o.get_unsigned(*g_hinst_lemma_max_steps, LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS);
}

hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, expr const & H, bool simp) {
    unsigned max_steps = get_hinst_lemma_max_steps(ctx.get_options());
    name id;
    if (is_local(H))
        id = mlocal_pp_name(H);
    return mk_hinst_lemma_core(ctx, md_norm, H, 0, max_steps, simp, id);
}

hinst_lemma mk_hinst_lemma(type_context_old & ctx, transparency_mode md_norm, name const & c, bool simp) {
    unsigned max_steps = get_hinst_lemma_max_steps(ctx.get_options());
    declaration const & d = ctx.env().get(c);
    buffer<level> us;
    unsigned num_us = d.get_num_univ_params();
    for (unsigned i = 0; i < num_us; i++)
        us.push_back(mk_idx_metauniv(i));
    expr H          = mk_constant(c, to_list(us));
    name id         = c;
    return mk_hinst_lemma_core(ctx, md_norm, H, num_us, max_steps, simp, id);
}

format pp_hinst_lemma(formatter const & fmt, hinst_lemma const & h) {
    format r;
    r += format(h.m_id) + comma() + line();
    bool first1 = true;
    format pats;
    for (multi_pattern const & mp : h.m_multi_patterns) {
        if (first1) first1 = false; else pats += comma() + line();
        format pat;
        bool first2 = true;
        for (expr const & p : mp) {
            if (first2) first2 = false; else pat += comma() + line();
            pat += fmt(p);
        }
        pats += group(bracket("{", pat, "}"));
    }
    char const * n = "patterns:";
    r += nest(strlen(n), format(n) + line() + group(bracket("{", pats, "}")));
    return group(bracket("[", r, "]"));
}

struct vm_hinst_lemma : public vm_external {
    hinst_lemma m_val;
    vm_hinst_lemma(hinst_lemma const & v): m_val(v) {}
    virtual ~vm_hinst_lemma() {}
    virtual void dealloc() override { this->~vm_hinst_lemma(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemma), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_hinst_lemma(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_hinst_lemma))) vm_hinst_lemma(m_val); }
};

hinst_lemma const & to_hinst_lemma(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_hinst_lemma*>(to_external(o)));
    return static_cast<vm_hinst_lemma*>(to_external(o))->m_val;
}

vm_obj to_obj(hinst_lemma const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemma))) vm_hinst_lemma(s));
}

vm_obj hinst_lemma_mk_core(vm_obj const & m, vm_obj const & lemma, vm_obj const & simp, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context_old ctx        = mk_type_context_for(s);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_transparency_mode(m), to_expr(lemma), to_bool(simp));
    return tactic::mk_success(to_obj(h), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj hinst_lemma_mk_from_decl_core(vm_obj const & m, vm_obj const & lemma_name, vm_obj const & simp, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    type_context_old ctx        = mk_type_context_for(s);
    hinst_lemma h           = mk_hinst_lemma(ctx, to_transparency_mode(m), to_name(lemma_name), to_bool(simp));
    return tactic::mk_success(to_obj(h), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj hinst_lemma_pp(vm_obj const & h, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    type_context_old ctx = mk_type_context_for(s);
    formatter fmt = fmtf(s.env(), s.get_options(), ctx);
    format r = pp_hinst_lemma(fmt, to_hinst_lemma(h));
    return tactic::mk_success(to_obj(r), s);
    LEAN_TACTIC_CATCH(s);
}

struct vm_hinst_lemmas : public vm_external {
    hinst_lemmas m_val;
    vm_hinst_lemmas(hinst_lemmas const & v): m_val(v) {}
    virtual ~vm_hinst_lemmas() {}
    virtual void dealloc() override { this->~vm_hinst_lemmas(); get_vm_allocator().deallocate(sizeof(vm_hinst_lemmas), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_hinst_lemmas(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_hinst_lemmas))) vm_hinst_lemmas(m_val); }
};

hinst_lemmas const & to_hinst_lemmas(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_hinst_lemmas*>(to_external(o)));
    return static_cast<vm_hinst_lemmas*>(to_external(o))->m_val;
}

bool is_hinst_lemmas(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_hinst_lemmas*>(to_external(o));
}

vm_obj to_obj(hinst_lemmas const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_hinst_lemmas))) vm_hinst_lemmas(s));
}

vm_obj hinst_lemmas_mk() {
    return to_obj(hinst_lemmas());
}

vm_obj hinst_lemmas_add(vm_obj const & hls, vm_obj const & h) {
    hinst_lemmas new_lemmas = to_hinst_lemmas(hls);
    new_lemmas.insert(to_hinst_lemma(h));
    return to_obj(new_lemmas);
}

vm_obj hinst_lemmas_fold(vm_obj const &, vm_obj const & hls, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    to_hinst_lemmas(hls).for_each([&](hinst_lemma const & h) {
            r = invoke(fn, to_obj(h), r);
        });
    return r;
}

vm_obj hinst_lemmas_merge(vm_obj const & s1, vm_obj const & s2) {
    hinst_lemmas r = to_hinst_lemmas(s1);
    r.merge(to_hinst_lemmas(s2));
    return to_obj(r);
}

void initialize_hinst_lemmas() {
    g_pattern_hint      = new name("pattern_hint");
    register_annotation(*g_pattern_hint);
    g_no_inst_pattern_attr = new name({"no_inst_pattern"});
    /* Add validation */
    register_system_attribute(basic_attribute(*g_no_inst_pattern_attr, "do not consider terms containing this declaration in the pattern inference procedure"));

    g_hinst_lemma_max_steps = new name{"hinst_lemma", "pattern", "max_steps"};

    register_unsigned_option(*g_hinst_lemma_max_steps, LEAN_DEFAULT_HINST_LEMMA_PATTERN_MAX_STEPS,
                             "(hinst_lemma) max number of steps performed by pattern inference procedure for heuristic instantiation lemmas, "
                             "we have this threshold because in the worst case this procedure may take "
                             "an exponetial number of steps");

    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_core"}),           hinst_lemma_mk_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "mk_from_decl_core"}), hinst_lemma_mk_from_decl_core);
    DECLARE_VM_BUILTIN(name({"hinst_lemma", "pp"}),                hinst_lemma_pp);

    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "mk"}),               hinst_lemmas_mk);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "add"}),              hinst_lemmas_add);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "fold"}),             hinst_lemmas_fold);
    DECLARE_VM_BUILTIN(name({"hinst_lemmas", "merge"}),            hinst_lemmas_merge);
}

void finalize_hinst_lemmas() {
    delete g_pattern_hint;
    delete g_no_inst_pattern_attr;
    delete g_hinst_lemma_max_steps;
}
}




// ========== util.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_delayed_cc_eq_proof(expr const & e1, expr const & e2);
expr mark_cc_theory_proof(expr const & pr);
expr get_cc_theory_proof_arg(expr const & pr);
bool is_cc_theory_proof(expr const & e);

class congruence_closure;
expr expand_delayed_cc_proofs(congruence_closure const & cc, expr const & e);

void initialize_smt_util();
void finalize_smt_util();
}




// ========== util.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/vm/vm.h"
#include "library/tactic/smt/congruence_closure.h"

namespace lean {
static name * g_cc_proof_name = nullptr;
static macro_definition * g_cc_proof_macro = nullptr;

class cc_proof_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_cc_proof_name; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return mk_eq(ctx, macro_arg(e, 0), macro_arg(e, 1));
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        /* This is a temporary/delayed proof step. */
        lean_unreachable();
    }

    virtual void write(serializer &) const {
        /* This is a temporary/delayed proof step. */
        lean_unreachable();
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        cc_proof_macro_cell const * other_ptr = dynamic_cast<cc_proof_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 23; }
};

/* Delayed (congruence closure procedure) proof.
   This proof is a placeholder for the real one that is computed only if needed. */
expr mk_delayed_cc_eq_proof(expr const & e1, expr const & e2) {
    expr args[2] = {e1, e2};
    return mk_macro(*g_cc_proof_macro, 2, args);
}

bool is_delayed_cc_eq_proof(expr const & e) {
    return is_macro(e) && dynamic_cast<cc_proof_macro_cell const *>(macro_def(e).raw());
}

static name * g_theory_proof = nullptr;

expr mark_cc_theory_proof(expr const & pr) {
    return mk_annotation(*g_theory_proof, pr);
}

bool is_cc_theory_proof(expr const & e) {
    return is_annotation(e, *g_theory_proof);
}

expr get_cc_theory_proof_arg(expr const & pr) {
    lean_assert(is_cc_theory_proof(pr));
    return get_annotation_arg(pr);
}

class expand_delayed_cc_proofs_fn : public replace_visitor {
    congruence_closure const & m_cc;

    expr visit_macro(expr const & e) {
        if (is_delayed_cc_eq_proof(e)) {
            expr const & lhs = macro_arg(e, 0);
            expr const & rhs = macro_arg(e, 1);
            return *m_cc.get_eq_proof(lhs, rhs);
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

public:
    expand_delayed_cc_proofs_fn(congruence_closure const & cc):m_cc(cc) {}
};

expr expand_delayed_cc_proofs(congruence_closure const & cc, expr const & e) {
    return expand_delayed_cc_proofs_fn(cc)(e);
}

void initialize_smt_util() {
    g_cc_proof_name   = new name("cc_proof");
    g_cc_proof_macro  = new macro_definition(new cc_proof_macro_cell());
    g_theory_proof    = new name("th_proof");
    register_annotation(*g_theory_proof);
}

void finalize_smt_util() {
    delete g_cc_proof_macro;
    delete g_cc_proof_name;
    delete g_theory_proof;
}
}




// ========== theory_ac.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/ac_tactics.h"

namespace lean {
class congruence_closure;
/* Associativity and commutativity by completion */
class theory_ac {
public:
    class occurrences {
        rb_expr_tree m_occs;
        unsigned     m_size{0};
    public:
        void insert(expr const & e) {
            if (m_occs.contains(e)) return;
            m_occs.insert(e);
            m_size++;
        }

        void erase(expr const & e) {
            if (m_occs.contains(e)) {
                m_occs.erase(e);
                m_size--;
            }
        }

        unsigned size() const { return m_size; }

        template<typename F>
        optional<expr> find_if(F && f) const {
            return m_occs.find_if(f);
        }

        template<typename F>
        void for_each(F && f) const {
            m_occs.for_each(f);
        }
    };

    struct entry {
        /* m_expr is the term in the congruence closure
           module being represented by this entry */
        unsigned    m_idx;
        occurrences m_R_occs[2];
        entry() {}
        entry(unsigned idx):m_idx(idx) {}
        occurrences const & get_R_occs(bool lhs) const { return m_R_occs[lhs]; }
        occurrences const & get_R_lhs_occs() const { return get_R_occs(true); }
        occurrences const & get_R_rhs_occs() const { return get_R_occs(false); }
        void set_R_occs(occurrences const & occs, bool lhs) { m_R_occs[lhs] = occs; }
    };

    typedef std::tuple<expr, expr, expr> expr_triple;

    struct state {
        /* Mapping from operators occurring in terms and their canonical
           representation in this module */
        rb_expr_map<expr>        m_can_ops;

        /* Mapping from canonical AC operators to AC proof terms. */
        rb_expr_map<expr_pair>   m_op_info;

        unsigned                 m_next_idx{0};

        rb_expr_map<entry>       m_entries;

        /* Confluent rewriting system */
        rb_expr_map<expr_pair>   m_R;

        format pp_term(formatter const & fmt, expr const & e) const;
        format pp_decl(formatter const & fmt, expr const & e) const;
        format pp_decls(formatter const & fmt) const;
        format pp_R(formatter const & fmt) const;
        format pp(formatter const & fmt) const;
        unsigned get_num_R_occs(expr const & e, bool in_lhs) const;
        expr get_var_with_least_occs(expr const & e, bool in_lhs) const;
        expr get_var_with_least_rhs_occs(expr const & e) const {
            return get_var_with_least_occs(e, false);
        }
        expr get_var_with_least_lhs_occs(expr const & e) const {
            return get_var_with_least_occs(e, true);
        }
    };

private:
    type_context_old &       m_ctx;
    congruence_closure & m_cc;
    state &              m_state;
    ac_manager_old       m_ac_manager;
    buffer<expr_triple>  m_todo;

    expr convert(expr const & op, expr const & e, buffer<expr> & args);
    bool internalize_var(expr const & e);
    void insert_erase_R_occ(expr const & arg, expr const & lhs, bool in_lhs, bool is_insert);
    void insert_erase_R_occs(expr const & e, expr const & lhs, bool in_lhs, bool is_insert);
    void insert_R_occs(expr const & e, expr const & lhs, bool in_lhs);
    void erase_R_occs(expr const & e, expr const & lhs, bool in_lhs);
    void insert_R_rhs_occs(expr const & e, expr const & lhs) { insert_R_occs(e, lhs, false); }
    void erase_R_rhs_occs(expr const & e, expr const & lhs) { erase_R_occs(e, lhs, false); }
    void insert_R_occs(expr const & lhs, expr const & rhs);
    void erase_R_occs(expr const & lhs, expr const & rhs);
    void compose_expr(expr const & lhs, expr const & rhs, expr const & H);
    void collapse(expr const & lhs, expr const & rhs, expr const & H);
    void superpose(expr const & lhs, expr const & rhs, expr const & H);
    expr_pair simplify_core(expr const & e, expr const & lhs, expr const & rhs, expr const & H);
    optional<expr_pair> simplify_step(expr const & e);
    optional<expr_pair> simplify(expr const & e);
    void process();
    void dbg_trace_state() const;
    void dbg_trace_eq(char const * header, expr const & lhs, expr const & rhs) const;

public:
    theory_ac(congruence_closure & cc, state & s);
    ~theory_ac();

    void internalize(expr const & e, optional<expr> const & parent);
    void add_eq(expr const & e1, expr const & e2);
    optional<expr> is_ac(expr const & e);

    format pp_term(formatter const & fmt, expr const & e) const {
        return m_state.pp_term(fmt, e);
    }
};

void initialize_theory_ac();
void finalize_theory_ac();
}




// ========== theory_ac.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/smt/util.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/theory_ac.h"

namespace lean {
/* Given e and ac_term that is provably equal to e using AC, return a proof for e = ac_term */
static expr mk_ac_refl_proof(type_context_old & ctx, expr const & e, expr const & ac_term, expr const & assoc, expr const & comm) {
    return mk_perm_ac_macro(ctx, assoc, comm, e, ac_term);
}

/* Given (tr := t*r) (sr := s*r) (t_eq_s : t = s), return a proof for
   tr = sr

   We use a*b to denote an AC application. That is, (a*b)*(c*a) is the term (a*a*b*c). */
static expr mk_ac_simp_proof(type_context_old & ctx, expr const & tr, expr const & t, expr const & s, expr const & r, expr const & sr,
                             expr const & t_eq_s, expr const & assoc, expr const & comm) {
    if (tr == t) {
        return t_eq_s;
    } else if (tr == sr) {
        return mk_eq_refl(ctx, tr);
    } else {
        lean_assert(is_ac_app(tr));
        expr const & op = get_ac_app_op(tr);
        expr op_r       = mk_app(op, r);
        expr rt         = mk_app(op_r, t);
        expr rs         = mk_app(op, r, s);
        expr rt_eq_rs   = mk_congr_arg(ctx, op_r, t_eq_s);
        expr tr_eq_rt   = mk_perm_ac_macro(ctx, assoc, comm, tr, rt);
        expr rs_eq_sr   = mk_perm_ac_macro(ctx, assoc, comm, rs, sr);
        return mk_eq_trans(ctx, mk_eq_trans(ctx, tr_eq_rt, rt_eq_rs), rs_eq_sr);
    }
}

/* Given (ra := a*r) (sb := b*s) (ts := t*s) (tr := t*r) (ts_eq_a : t*s = a) (tr_eq_b : t*r = b),
   return a proof for ra = sb.

   We use a*b to denote an AC application. That is, (a*b)*(c*a) is the term (a*a*b*c).

   The proof is constructed using congruence and the perm_ac macro. */
static expr mk_ac_superpose_proof(type_context_old & ctx,
                                  expr const & ra, expr const & sb,
                                  expr const & a, expr const & b,
                                  expr const & r, expr const & s,
                                  expr const & ts, expr const & tr,
                                  expr const & ts_eq_a, expr const & tr_eq_b,
                                  expr const & assoc, expr const & comm) {
    lean_assert(is_ac_app(tr));
    lean_assert(is_ac_app(ts));
    expr const & op = get_ac_app_op(ts);
    expr tsr_eq_ar  = mk_congr_fun(ctx, mk_congr_arg(ctx, op, ts_eq_a), r);
    expr trs_eq_bs  = mk_congr_fun(ctx, mk_congr_arg(ctx, op, tr_eq_b), s);
    expr tsr        = mk_app(op, ts, r);
    expr trs        = mk_app(op, tr, s);
    expr tsr_eq_trs = mk_perm_ac_macro(ctx, assoc, comm, tsr, trs);
    expr ar         = mk_app(op, a, r);
    expr bs         = mk_app(op, b, s);
    expr ra_eq_ar   = mk_perm_ac_macro(ctx, assoc, comm, ra, ar);
    expr bs_eq_sb   = mk_perm_ac_macro(ctx, assoc, comm, bs, sb);
    return mk_eq_trans(ctx, ra_eq_ar,
           mk_eq_trans(ctx, mk_eq_symm(ctx, tsr_eq_ar),
           mk_eq_trans(ctx, tsr_eq_trs,
           mk_eq_trans(ctx, trs_eq_bs, bs_eq_sb))));
}

static char const * ac_var_prefix = "x_";

format theory_ac::state::pp_term(formatter const & fmt, expr const & e) const {
    if (auto it = m_entries.find(e)) {
        return format(ac_var_prefix) + format(it->m_idx);
    } else if (is_ac_app(e)) {
        format r          = fmt(get_ac_app_op(e));
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        for (unsigned i = 0; i < nargs; i++) {
            r += line() + pp_term(fmt, args[i]);
        }
        return group(bracket("[", r, "]"));
    } else {
        tout() << "pp_term: " << e << "\n";
        lean_unreachable();
    }
}

format theory_ac::state::pp_decl(formatter const & fmt, expr const & e) const {
    lean_assert(m_entries.contains(e));
    auto it = m_entries.find(e);
    return group(format(ac_var_prefix) + format(it->m_idx) + line() + format(":=") + line() + fmt(e));
}

format theory_ac::state::pp_decls(formatter const & fmt) const {
    format r;
    bool first = true;
    m_entries.for_each([&](expr const & k, entry const &) {
            if (first) first = false; else r += comma() + line();
            r += pp_decl(fmt, k);
        });
    return group(bracket("{", r, "}"));
}

format theory_ac::state::pp_R(formatter const & fmt) const {
    format r;
    unsigned indent = get_pp_indent(fmt.get_options());
    bool first = true;
    m_R.for_each([&](expr const & k, expr_pair const & p) {
            format curr = pp_term(fmt, k) + line() + format("-->") + nest(indent, line() + pp_term(fmt, p.first));
            if (first) first = false; else r += comma() + line();
            r += group(curr);
        });
    return group(bracket("{", r, "}"));
}

format theory_ac::state::pp(formatter const & fmt) const {
    return group(bracket("[", pp_decls(fmt) + comma() + line() + pp_R(fmt), "]"));
}

theory_ac::theory_ac(congruence_closure & cc, state & s):
    m_ctx(cc.ctx()),
    m_cc(cc),
    m_state(s),
    m_ac_manager(cc.ctx()) {
}

theory_ac::~theory_ac() {
}

optional<expr> theory_ac::is_ac(expr const & e) {
    optional<expr> assoc_pr = m_ac_manager.is_assoc(e);
    if (!assoc_pr) return none_expr();
    optional<expr> comm_pr  = m_ac_manager.is_comm(e);
    if (!comm_pr) return none_expr();
    expr op = app_fn(app_fn(e));
    op = m_cc.get_defeq_canonizer().canonize(op);
    if (auto it = m_state.m_can_ops.find(op))
        return some_expr(*it);
    optional<expr> found_op;
    m_state.m_op_info.for_each([&](expr const & c_op, expr_pair const &) {
            if (!found_op && m_ctx.pure_relaxed_is_def_eq(op, c_op))
                found_op = c_op;
        });
    if (found_op) {
        m_state.m_can_ops.insert(op, *found_op);
        return found_op;
    } else {
        m_state.m_can_ops.insert(op, op);
        m_state.m_op_info.insert(op, mk_pair(*assoc_pr, *comm_pr));
        return some_expr(op);
    }
}

expr theory_ac::convert(expr const & op, expr const & e, buffer<expr> & args) {
    if (optional<expr> curr_op = is_ac(e)) {
        if (op == *curr_op) {
            expr arg1 = convert(op, app_arg(app_fn(e)), args);
            expr arg2 = convert(op, app_arg(e), args);
            return mk_app(op, arg1, arg2);
        }
    }

    internalize_var(e);
    args.push_back(e);
    return e;
}

bool theory_ac::internalize_var(expr const & e) {
    if (m_state.m_entries.contains(e)) return false;
    m_state.m_entries.insert(e, entry(m_state.m_next_idx));
    m_state.m_next_idx++;
    m_cc.set_ac_var(e);
    return true;
}

void theory_ac::dbg_trace_state() const {
    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << group(format("state:") + nest(get_pp_indent(fmt.get_options()), line() + m_state.pp(fmt))) << "\n";);
}

void theory_ac::dbg_trace_eq(char const * header, expr const & lhs, expr const & rhs) const {
    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << group(format(header) + line() + pp_term(fmt, lhs) + line() + format("=") + line() + pp_term(fmt, rhs)) << "\n";);
}

void theory_ac::internalize(expr const & e, optional<expr> const & parent) {
    auto op = is_ac(e);
    if (!op) return;
    optional<expr> parent_op;
    if (parent) parent_op = is_ac(*parent);
    if (parent_op && *op == *parent_op) return;

    if (!internalize_var(e)) return;

    buffer<expr> args;
    expr norm_e = convert(*op, e, args);
    expr rep    = mk_ac_app(*op, args);
    auto ac_prs = m_state.m_op_info.find(*op);
    lean_assert(ac_prs);
    expr pr     = mk_ac_refl_proof(m_ctx, norm_e, rep, ac_prs->first, ac_prs->second);

    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               format d = group(paren(pp_term(fmt, e) + space() + format(":=") + line() + fmt(e)));
               format r = format("new term:") + line() + d + line() + format("===>") + line() + pp_term(fmt, rep);
               out << group(r) << "\n";);

    m_todo.emplace_back(e, rep, pr);
    process();
    dbg_trace_state();
}

void theory_ac::insert_erase_R_occ(expr const & arg, expr const & lhs, bool in_lhs, bool is_insert) {
    entry new_entry  = *m_state.m_entries.find(arg);
    occurrences occs = new_entry.get_R_occs(in_lhs);
    if (is_insert)
        occs.insert(lhs);
    else
        occs.erase(lhs);
    new_entry.set_R_occs(occs, in_lhs);
    m_state.m_entries.insert(arg, new_entry);
}

void theory_ac::insert_erase_R_occs(expr const & e, expr const & lhs, bool in_lhs, bool is_insert) {
    if (is_ac_app(e)) {
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        insert_erase_R_occ(args[0], lhs, in_lhs, is_insert);
        for (unsigned i = 1; i < nargs; i++) {
            if (args[i] != args[i-1])
                insert_erase_R_occ(args[i], lhs, in_lhs, is_insert);
        }
    } else {
        insert_erase_R_occ(e, lhs, in_lhs, is_insert);
    }
}

void theory_ac::insert_R_occs(expr const & e, expr const & lhs, bool in_lhs) {
    insert_erase_R_occs(e, lhs, in_lhs, true);
}

void theory_ac::erase_R_occs(expr const & e, expr const & lhs, bool in_lhs) {
    insert_erase_R_occs(e, lhs, in_lhs, false);
}

void theory_ac::insert_R_occs(expr const & lhs, expr const & rhs) {
    insert_R_occs(lhs, lhs, true);
    insert_R_occs(rhs, lhs, false);
}

void theory_ac::erase_R_occs(expr const & lhs, expr const & rhs) {
    erase_R_occs(lhs, lhs, true);
    erase_R_occs(rhs, lhs, false);
}

/*
  Given, e is of the form lhs*r, (H : lhs = rhs),
  return (rhs*r) and proof ac_simp_pr(e, lhs, rhs, r, rhs*r, H) : e = rhs*r
*/
expr_pair theory_ac::simplify_core(expr const & e, expr const & lhs, expr const & rhs, expr const & H) {
    lean_assert(is_ac_subset(lhs, e));
    if (e == lhs) {
        return mk_pair(rhs, H);
    } else {
        lean_assert(is_ac_app(e));
        expr dummy = mk_Prop();
        expr op    = get_ac_app_op(e);
        buffer<expr> new_args;
        ac_diff(e, lhs, new_args);
        expr r      = new_args.empty() ? dummy : mk_ac_app(op, new_args);
        ac_append(op, rhs, new_args);
        expr new_e  = mk_ac_app(op, new_args);
        auto ac_prs = m_state.m_op_info.find(op);
        lean_assert(ac_prs);
        expr new_pr = mk_ac_simp_proof(m_ctx, e, lhs, rhs, r, new_e, H, ac_prs->first, ac_prs->second);
        return mk_pair(new_e, new_pr);
    }
}

optional<expr_pair> theory_ac::simplify_step(expr const & e) {
    if (is_ac_app(e)) {
        unsigned nargs = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        for (unsigned i = 0; i < nargs; i++) {
            if (i == 0 || args[i] != args[i-1]) {
                occurrences const & occs = m_state.m_entries.find(args[i])->get_R_lhs_occs();
                optional<expr> R_lhs = occs.find_if([&](expr const & R_lhs) {
                        return is_ac_subset(R_lhs, e);
                    });
                if (R_lhs) {
                    expr_pair const * p = m_state.m_R.find(*R_lhs);
                    lean_assert(p);
                    expr R_rhs = p->first;
                    expr H     = p->second;
                    return optional<expr_pair>(simplify_core(e, *R_lhs, R_rhs, H));
                }
            }
        }
    } else if (expr_pair const * p = m_state.m_R.find(e)) {
        return optional<expr_pair>(*p);
    }
    return optional<expr_pair>();
}

optional<expr_pair> theory_ac::simplify(expr const & e) {
    optional<expr_pair> p = simplify_step(e);
    if (!p) return p;
    expr curr = p->first;
    expr pr   = p->second;
    while (optional<expr_pair> p = simplify_step(curr)) {
        expr new_curr = p->first;
        pr   = mk_eq_trans(m_ctx, e, curr, new_curr, pr, p->second);
        curr = new_curr;
    }
    return optional<expr_pair>(mk_pair(curr, pr));
}

unsigned theory_ac::state::get_num_R_occs(expr const & e, bool in_lhs) const {
    return m_entries.find(e)->m_R_occs[in_lhs].size();
}

expr theory_ac::state::get_var_with_least_occs(expr const & e, bool in_lhs) const {
    if (is_ac_app(e)) {
        unsigned nargs    = get_ac_app_num_args(e);
        expr const * args = get_ac_app_args(e);
        expr r            = args[0];
        unsigned num_occs = get_num_R_occs(r, in_lhs);
        for (unsigned i = 1; i < nargs; i++) {
            if (args[i] != args[i-1]) {
                unsigned curr_occs = get_num_R_occs(args[i], in_lhs);
                if (curr_occs < num_occs) {
                    r        = args[i];
                    num_occs = curr_occs;
                }
            }
        }
        return r;
    } else {
        return e;
    }
}

void theory_ac::compose_expr(expr const & lhs, expr const & rhs, expr const & H) {
    expr x           = m_state.get_var_with_least_rhs_occs(lhs);
    occurrences occs = m_state.m_entries.find(x)->get_R_rhs_occs();
    occs.for_each([&](expr const & R_lhs) {
            auto p = m_state.m_R.find(R_lhs);
            expr R_rhs = p->first;
            expr R_H  = p->second;
            if (is_ac_subset(lhs, R_rhs)) {
                expr new_R_rhs, R_rhs_eq_new_R_rhs;
                std::tie(new_R_rhs, R_rhs_eq_new_R_rhs) = simplify_core(R_rhs, lhs, rhs, H);
                expr new_R_H = mk_eq_trans(m_ctx, R_lhs, R_rhs, new_R_rhs, R_H, R_rhs_eq_new_R_rhs);
                m_state.m_R.insert(R_lhs, mk_pair(new_R_rhs, new_R_H));
                erase_R_rhs_occs(R_rhs, R_lhs);
                insert_R_rhs_occs(new_R_rhs, R_lhs);
                lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                           auto out      = tout();
                           auto fmt      = out.get_formatter();
                           format old_rw = group(paren(pp_term(fmt, R_lhs) + line() + format("-->") + line() + pp_term(fmt, R_rhs)));
                           format new_rw = group(paren(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs)));
                           format r      = format("compose:");
                           r += nest(get_pp_indent(fmt.get_options()), line() + group(old_rw + line() + format("with") + line() + new_rw) +
                                     line() + format(":=") + line() + pp_term(fmt, new_R_rhs));
                           out << group(r) << "\n";);
            }
        });
}

void theory_ac::collapse(expr const & lhs, expr const & rhs, expr const & H) {
    expr x           = m_state.get_var_with_least_lhs_occs(lhs);
    occurrences occs = m_state.m_entries.find(x)->get_R_lhs_occs();
    occs.for_each([&](expr const & R_lhs) {
            if (is_ac_subset(lhs, R_lhs)) {
                expr R_rhs, R_H;
                std::tie(R_rhs, R_H) = *m_state.m_R.find(R_lhs);
                erase_R_occs(R_lhs, R_rhs);
                m_state.m_R.erase(R_lhs);
                expr new_R_lhs, R_lhs_eq_new_R_lhs;
                std::tie(new_R_lhs, R_lhs_eq_new_R_lhs) = simplify_core(R_lhs, lhs, rhs, H);
                expr new_R_lhs_eq_R_lhs = mk_eq_symm(m_ctx, R_lhs, new_R_lhs, R_lhs_eq_new_R_lhs);
                expr new_R_H            = mk_eq_trans(m_ctx, new_R_lhs, R_lhs, R_rhs, new_R_lhs_eq_R_lhs, R_H);
                m_todo.emplace_back(new_R_lhs, R_rhs, new_R_H);
                lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                           auto out      = tout();
                           auto fmt      = out.get_formatter();
                           format new_rw = group(paren(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs)));
                           format old_rw = group(paren(pp_term(fmt, R_rhs) + line() + format("<--") + line() + pp_term(fmt, R_lhs)));
                           format r      = format("collapse:");
                           r += nest(get_pp_indent(fmt.get_options()), line() + group(new_rw + line() + format("at") + line() + old_rw) +
                                     line() + format(":=") + line() + pp_term(fmt, new_R_lhs));
                           out << group(r) << "\n";);
            }
        });
}

void theory_ac::superpose(expr const & ts, expr const & a, expr const & ts_eq_a) {
    if (!is_ac_app(ts)) return;
    expr const & op = get_ac_app_op(ts);
    unsigned nargs  = get_ac_app_num_args(ts);
    expr const * args = get_ac_app_args(ts);
    for (unsigned i = 0; i < nargs; i++) {
        if (i == 0 || args[i] != args[i-1]) {
            occurrences const & occs = m_state.m_entries.find(args[i])->get_R_lhs_occs();
            occs.for_each([&](expr const & tr) {
                    if (get_ac_app_op(tr) != op) return;
                    expr b, tr_eq_b;
                    std::tie(b, tr_eq_b) = *m_state.m_R.find(tr);
                    buffer<expr> t_args, s_args, r_args;
                    ac_intersection(ts, tr, t_args); lean_assert(!t_args.empty());
                    expr t = mk_ac_app(op, t_args);
                    ac_diff(ts, t, s_args); lean_assert(!s_args.empty());
                    ac_diff(tr, t, r_args); lean_assert(!r_args.empty());
                    expr s  = mk_ac_app(op, s_args);
                    expr r  = mk_ac_app(op, r_args);
                    expr ra = mk_ac_flat_app(op, r, a);
                    expr sb = mk_ac_flat_app(op, s, b);
                    auto ac_prs = m_state.m_op_info.find(op);
                    lean_assert(ac_prs);
                    expr ra_eq_sb = mk_ac_superpose_proof(m_ctx, ra, sb, a, b, r, s, ts, tr, ts_eq_a, tr_eq_b,
                                                          ac_prs->first, ac_prs->second);
                    m_todo.emplace_back(ra, sb, ra_eq_sb);
                    lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                               auto out      = tout();
                               auto fmt      = out.get_formatter();
                               format rw1    = group(paren(pp_term(fmt, ts) + line() + format("-->") + line() + pp_term(fmt, a)));
                               format rw2    = group(paren(pp_term(fmt, tr) + line() + format("-->") + line() + pp_term(fmt, b)));
                               format eq     = group(paren(pp_term(fmt, ra) + line() + format("=") + line() + pp_term(fmt, sb)));
                               format r      = format("superpose:");
                               r += nest(get_pp_indent(fmt.get_options()), line() + group(rw1 + line() + format("with") + line() + rw2) +
                                         line() + format(":=") + line() + eq);
                               out << group(r) << "\n";);
                });
        }
    }
}

void theory_ac::process() {
    while (!m_todo.empty()) {
        expr lhs, rhs, H;
        std::tie(lhs, rhs, H) = m_todo.back();
        m_todo.pop_back();
        dbg_trace_eq("process eq:", lhs, rhs);
        expr lhs0 = lhs;
        expr rhs0 = rhs;

        /* Forward simplification lhs/rhs */
        if (optional<expr_pair> p = simplify(lhs)) {
            H  = mk_eq_trans(m_ctx, p->first, lhs, rhs, mk_eq_symm(m_ctx, lhs, p->first, p->second), H);
            lhs = p->first;
        }
        if (optional<expr_pair> p = simplify(rhs)) {
            H  = mk_eq_trans(m_ctx, lhs, rhs, p->first, H, p->second);
            rhs = p->first;
        }

        if (lhs != lhs0 || rhs != rhs0) {
            dbg_trace_eq("after simp:", lhs, rhs);
        }

        /* Check trivial */
        if (lhs == rhs) {
            lean_trace(name({"debug", "cc", "ac"}), tout() << "trivial\n";);
            continue;
        }

        /* Propagate new equality to congruence closure module */
        if (!is_ac_app(lhs) && !is_ac_app(rhs) && m_cc.get_root(lhs) != m_cc.get_root(rhs)) {
            m_cc.push_eq(lhs, rhs, mark_cc_theory_proof(H));
        }

        /* Orient */
        if (ac_lt(lhs, rhs)) {
            H = mk_eq_symm(m_ctx, lhs, rhs, H);
            std::swap(lhs, rhs);
        }

        /* Backward simplification */
        compose_expr(lhs, rhs, H);
        collapse(lhs, rhs, H);

        /* Superposition */
        superpose(lhs, rhs, H);

        /* Update R */
        m_state.m_R.insert(lhs, mk_pair(rhs, H));
        insert_R_occs(lhs, rhs);

        lean_trace(name({"debug", "cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
                   auto out      = tout();
                   auto fmt      = out.get_formatter();
                   format new_rw = group(pp_term(fmt, lhs) + line() + format("-->") + line() + pp_term(fmt, rhs));
                   out << group(format("new rw:") + line() + new_rw) << "\n";);
    }
}

void theory_ac::add_eq(expr const & e1, expr const & e2) {
    dbg_trace_eq("cc eq:", e1, e2);
    m_todo.emplace_back(e1, e2, mk_delayed_cc_eq_proof(e1, e2));
    process();
    dbg_trace_state();
}

void initialize_theory_ac() {
    register_trace_class(name({"cc", "ac"}));
    register_trace_class(name({"debug", "cc", "ac"}));
}

void finalize_theory_ac() {
}
}




// ========== ematch.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/head_map.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/hinst_lemmas.h"

namespace lean {
typedef rb_expr_tree rb_expr_set;
typedef rb_map<head_index, rb_expr_set, head_index::cmp> app_map;

struct ematch_config {
    unsigned  m_max_instances{1000};
    unsigned  m_max_generation{10};
};

class ematch_fn;

class ematch_state {
    friend class ematch_fn;
    app_map               m_app_map;
    rb_expr_set           m_instances;
    unsigned              m_num_instances{0};
    bool                  m_max_instances_exceeded{false};
    ematch_config         m_config;
    hinst_lemmas          m_lemmas;
    hinst_lemmas          m_new_lemmas;
public:
    ematch_state(ematch_config const & cfg, hinst_lemmas const & lemmas = hinst_lemmas()):
        m_config(cfg), m_new_lemmas(lemmas) {}

    void internalize(type_context_old & ctx, expr const & e);
    bool max_instances_exceeded() const { return m_max_instances_exceeded; }
    bool save_instance(expr const & e);
    /* Record the fact that the given lemma was instantiated with the given arguments. */
    bool save_instance(expr const & lemma, buffer<expr> const & args);
    app_map const & get_app_map() const { return m_app_map; }
    hinst_lemmas const & get_lemmas() const { return m_lemmas; }
    hinst_lemmas const & get_new_lemmas() const { return m_new_lemmas; }
    void add_lemma(hinst_lemma const & lemma) { m_new_lemmas.insert(lemma); }
    void set_lemmas(hinst_lemmas const & lemmas) { m_lemmas.clear(); m_new_lemmas = lemmas; }
    ematch_config const & get_config() const { return m_config; }
    vm_obj mk_vm_ematch_config() const;
};

struct new_instance {
    expr     m_instance;
    expr     m_proof;
    unsigned m_generation;
};

/* Ematch patterns in lemma with t, and add instances of lemma at result */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t,
            buffer<new_instance> & result);

/* Ematch patterns in lemma with terms internalized in the ematch_state, and add instances of lemma at result */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter,
            buffer<new_instance> & result);

/* Ematch patterns of lemmas in s.m_lemmas and s.m_new_lemmas with terms internalized in the ematch_state.
   Add instances to result.
   Move s.m_new_lemmas to s.m_lemmas, and increment gmt from cc.
   For s.m_lemmas, only terms with mt >= gmt are considered. */
void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, buffer<new_instance> & result);

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
*/
pair<name_set, congruence_closure::config> to_ho_fns_cc_config(vm_obj const & cfg);
ematch_config to_ematch_config(vm_obj const & cfg);

ematch_state const & to_ematch_state(vm_obj const & o);
vm_obj to_obj(ematch_state const & s);

void initialize_ematch();
void finalize_ematch();
}




// ========== ematch.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/interrupt.h"
#include "util/small_object_allocator.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/fun_info.h"
#include "library/idx_metavar.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/hinst_lemmas.h"

namespace lean {
void ematch_state::internalize(type_context_old & ctx, expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:      case expr_kind::Sort:
    case expr_kind::Constant: case expr_kind::Meta:
    case expr_kind::Local:    case expr_kind::Lambda:
    case expr_kind::Let:
        break;
    case expr_kind::Pi:
        if (is_arrow(e) && ctx.is_prop(e)) {
            internalize(ctx, binding_domain(e));
            internalize(ctx, binding_body(e));
        }
        break;
    case expr_kind::Macro:
        for (unsigned i = 0; i < macro_num_args(e); i++)
            internalize(ctx, macro_arg(e, i));
        break;
    case expr_kind::App: {
        buffer<expr> args;
        expr const & f = get_app_args(e, args);
        if ((is_constant(f) && !has_no_inst_pattern_attribute(ctx.env(), const_name(f))) ||
            (is_local(f))) {
            rb_expr_set s;
            if (auto old_s = m_app_map.find(head_index(f)))
                s = *old_s;
            s.insert(e);
            m_app_map.insert(head_index(f), s);
        }
        for (expr const & arg : args) {
            internalize(ctx, arg);
        }
        break;
    }}
}

bool ematch_state::save_instance(expr const & i) {
    if (m_num_instances >= m_config.m_max_instances) {
        if (!m_max_instances_exceeded) {
            lean_trace(name({"smt", "ematch"}),
                       tout() << "maximum number of ematching instances (" << m_config.m_max_instances << ") has been reached\n";);
        }
        m_max_instances_exceeded = true;
        return false;
    }
    if (m_instances.contains(i)) {
        return false;
    } else {
        m_num_instances++;
        m_instances.insert(i);
        return true;
    }
}

bool ematch_state::save_instance(expr const & lemma, buffer<expr> const & args) {
    expr key = mk_app(lemma, args);
    return save_instance(key);
}

/*
structure ematch_config :=
(max_instances  : nat)
(max_generation : nat)
*/
vm_obj ematch_state::mk_vm_ematch_config() const {
    return mk_vm_constructor(0, mk_vm_nat(get_config().m_max_instances), mk_vm_nat(get_config().m_max_generation));
}

/* CACHE_RESET: NO */
/* Allocator for ematching constraints. */
MK_THREAD_LOCAL_GET(small_object_allocator, get_emc_allocator, "ematch constraint");

enum class ematch_cnstr_kind { DefEqOnly, EqvOnly, Match, MatchAC, MatchSS /* match subsingleton */, Continue };
class ematch_cnstr;
/** \brief Base class for Ematching constraints.

    Remark: these objects are thread local. So, we don't need synchronization. */
struct ematch_cnstr_cell {
    unsigned          m_rc;
    ematch_cnstr_kind m_kind;

    void inc_ref() { m_rc++; }
    bool dec_ref_core() { lean_assert(m_rc > 0); m_rc--; return m_rc == 0; }
    void dec_ref() { if (dec_ref_core()) { dealloc(); } }
    void dealloc();
    ematch_cnstr_cell(ematch_cnstr_kind k):m_rc(0), m_kind(k) {}
    ematch_cnstr_kind kind() const { return m_kind; }
    unsigned get_rc() const { return m_rc; }
};

/* Ematching constraint smart pointer */
class ematch_cnstr {
    friend struct ematch_cnstr_cell;
    ematch_cnstr_cell * m_data;
public:
    ematch_cnstr():m_data(nullptr) {}
    explicit ematch_cnstr(ematch_cnstr_cell * c):m_data(c) { m_data->inc_ref(); }
    ematch_cnstr(ematch_cnstr const & o):m_data(o.m_data) { m_data->inc_ref(); }
    ematch_cnstr(ematch_cnstr && o):m_data(o.m_data) { o.m_data = nullptr; }
    ~ematch_cnstr() { if (m_data) m_data->dec_ref(); }
    operator ematch_cnstr_cell*() const { return m_data; }

    ematch_cnstr & operator=(ematch_cnstr const & s) {
        if (s.m_data) s.m_data->inc_ref();
        ematch_cnstr_cell * new_data = s.m_data;
        if (m_data) m_data->dec_ref();
        m_data = new_data;
        return *this;
    }

    ematch_cnstr & operator=(ematch_cnstr && s) {
        if (m_data) m_data->dec_ref();
        m_data   = s.m_data;
        s.m_data = nullptr;
        return *this;
    }

    ematch_cnstr_kind kind() const { return m_data->kind(); }
    ematch_cnstr_cell * raw() const { return m_data; }
};

struct ematch_eq_cnstr : public ematch_cnstr_cell {
    expr m_p;
    expr m_t;
    ematch_eq_cnstr(ematch_cnstr_kind k, expr const & p, expr const & t):
        ematch_cnstr_cell(k), m_p(p), m_t(t) {}
};

struct ematch_ac_cnstr : public ematch_cnstr_cell {
    expr       m_op;
    list<expr> m_p;
    list<expr> m_t;
    ematch_ac_cnstr(expr const & op, list<expr> const & p, list<expr> const & t):
        ematch_cnstr_cell(ematch_cnstr_kind::MatchAC), m_op(op), m_p(p), m_t(t) {}
};

struct ematch_continue : public ematch_cnstr_cell {
    expr m_p;
    ematch_continue(expr const & p):
        ematch_cnstr_cell(ematch_cnstr_kind::Continue), m_p(p) {}
};

inline bool is_eq_cnstr(ematch_cnstr_cell const * c) {
    return
        c->kind() == ematch_cnstr_kind::Match || c->kind() == ematch_cnstr_kind::MatchSS ||
        c->kind() == ematch_cnstr_kind::DefEqOnly || c->kind() == ematch_cnstr_kind::EqvOnly;
}
static bool is_ac_cnstr(ematch_cnstr_cell const * c) { return c->kind() == ematch_cnstr_kind::MatchAC; }
static bool is_continue(ematch_cnstr_cell const * c) { return c->kind() == ematch_cnstr_kind::Continue; }

static ematch_eq_cnstr * to_eq_cnstr(ematch_cnstr_cell * c) { lean_assert(is_eq_cnstr(c)); return static_cast<ematch_eq_cnstr*>(c); }
static ematch_ac_cnstr * to_ac_cnstr(ematch_cnstr_cell * c) { lean_assert(is_ac_cnstr(c)); return static_cast<ematch_ac_cnstr*>(c); }
static ematch_continue * to_continue(ematch_cnstr_cell * c) { lean_assert(is_continue(c)); return static_cast<ematch_continue*>(c); }

void ematch_cnstr_cell::dealloc() {
    lean_assert(get_rc() == 0);
    if (is_ac_cnstr(this)) {
        to_ac_cnstr(this)->~ematch_ac_cnstr();
        get_emc_allocator().deallocate(sizeof(ematch_ac_cnstr), this);
    } else if (is_continue(this)) {
        to_continue(this)->~ematch_continue();
        get_emc_allocator().deallocate(sizeof(ematch_continue), this);
    } else {
        to_eq_cnstr(this)->~ematch_eq_cnstr();
        get_emc_allocator().deallocate(sizeof(ematch_eq_cnstr), this);
    }
}

static ematch_cnstr mk_eq_cnstr(ematch_cnstr_kind k, expr const & p, expr const & t) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_eq_cnstr))) ematch_eq_cnstr(k, p, t));
}

static ematch_cnstr mk_match_ac_cnstr(expr const & op, list<expr> const & p, list<expr> const & t) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_ac_cnstr))) ematch_ac_cnstr(op, p, t));
}

static ematch_cnstr mk_continue(expr const & p) {
    return ematch_cnstr(new (get_emc_allocator().allocate(sizeof(ematch_continue))) ematch_continue(p));
}

static ematch_cnstr mk_match_eq_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::Match, p, t); }
static ematch_cnstr mk_match_ss_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::MatchSS, p, t); }
static ematch_cnstr mk_eqv_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::EqvOnly, p, t); }
static ematch_cnstr mk_defeq_cnstr(expr const & p, expr const & t) { return mk_eq_cnstr(ematch_cnstr_kind::DefEqOnly, p, t); }

static expr const & cnstr_p(ematch_cnstr const & c) { return to_eq_cnstr(c)->m_p; }
static expr const & cnstr_t(ematch_cnstr const & c) { return to_eq_cnstr(c)->m_t; }
static expr const & cont_p(ematch_cnstr const & c) { return to_continue(c)->m_p; }
static expr const & ac_op(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_op; }
static list<expr> const & ac_p(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_p; }
static list<expr> const & ac_t(ematch_cnstr const & c) { return to_ac_cnstr(c)->m_t; }

/*
  Matching modulo equalities.

  This module also supports matching modulo AC.

  The procedure is (supposed to be) complete for E-matching and AC-matching.
  However, it is currently incomplete for AC-E-matching.

  Here are matching problems that are not supported.
  Assuming + is an AC operation.

  1) Given { a + b = f c }, solve (?x + f ?x) =?= (a + c + b)
  It misses the solution ?x := c

  2) Given { a = a + a }, solve (?x + ?x + ?x + ?y) =?= (a + b)
  It misses the solution ?x := a, ?y := b

  The following implementation is based on standard algorithms for E-matching and
  AC-matching. The following extensions are supported.

  - E-matching modulo heterogeneous equalities.
    Casts are automatically introduced.
    Moreover, in standard E-matching, a sub-problem such as
          ?x =?= t
    where ?x is unassigned, is solved by assigning ?x := t.
    We add the following extension when t is in a heterogeneous equivalence class.
    We peek a term t_i in eqc(t) for each different type, and then create
    the subproblems:
          ?x := t_1 \/ ... \/ ?x := t_k

  - Uses higher-order pattern matching whenever higher-order sub-patterns
    are found. Example: (?f a) =?= (g a a)

  - Subsingleton support. For example, suppose (a b : A), and A is a subsingleton.
    Then, the following pattern is solved.
        (f a ?x) =?= (f b c)
    This is useful when we have proofs embedded in terms.

  - Equality expansion preprocessing step for AC-matching subproblems.
    Given an AC-matching subproblem  p =?= ...+t+...
    For each term t' headed by + in eqc(t), we generate a new case:
          p =?= ...+t'+...

    Limitations:
    1- A term t will be expanded at most once per AC subproblem.
       Example: given {a = a + a}, and constraint (?x + ?x + ?x + ?y) =?= (a + b).
       We produce two cases:
                ?x + ?x + ?x + ?y =?= a + b
                \/
                ?x + ?x + ?x + ?y =?= a + a + b

    2- We do not consider subterms of the form (t+s).
       Example: give {a + b = f c}, and constraint {?x + f ?x =?= a + c + b},
       this procedure will not generate the new case {?x + f ?x =?= f c + c}
       by replacing (a + b) with (f c).
*/
class ematch_fn {
    typedef list<ematch_cnstr> state;
    type_context_old &                m_ctx;
    ematch_state &                m_em_state;
    congruence_closure &          m_cc;
    buffer<new_instance> &        m_new_instances;
    unsigned                      m_gen;

    state                         m_state;
    buffer<pair<state, unsigned>> m_choice_stack;

    expr instantiate_mvars(expr const & e) {
        return m_ctx.instantiate_mvars(e);
    }

    /* Similar to instantiate_mvars, but it makes sure the assignment at m_ctx is not modified by composition.
       That is, suppose we have the assignment { ?x := f ?y, ?y := a }, and we instantiate (g ?x).
       The result is (g (f a)), but this method prevents the assignment to be modified to
              { ?x := f a, ?y := a }

       We need this feature for AC matching, where we want to be able to quickly detect "partially solved"
       variables of the form (?x := ?y + s) where s does not contain metavariables. */
    expr safe_instantiate_mvars(expr const & e) {
        m_ctx.push_scope();
        expr r = instantiate_mvars(e);
        m_ctx.pop_scope();
        return r;
    }

    bool is_metavar(expr const & e) { return m_ctx.is_tmp_mvar(e); }
    bool is_meta(expr const & e) { return is_metavar(get_app_fn(e)); }
    bool has_expr_metavar(expr const & e) { return has_idx_expr_metavar(e); }
    optional<expr> is_ac(expr const & /* e */) {
        // TODO(Leo): enable AC matching when it is done
        return none_expr();
        // return m_cc.is_ac(e);
    }
    optional<expr> get_binary_op(expr const & e) {
        if (is_app(e) && is_app(app_fn(e)))
            return some_expr(app_fn(app_fn(e)));
        else
            return none_expr();
    }

    expr tmp_internalize(expr const & e) {
        expr new_e = m_cc.normalize(e);
        m_cc.internalize(new_e, 0);
        return new_e;
    }

    bool is_ground_eq(expr const & p, expr const & t) {
        lean_assert(!has_expr_metavar(p));
        lean_assert(!has_expr_metavar(t));
        return m_cc.is_eqv(p, t) || m_ctx.is_def_eq(p, t);
    }

    /* Return true iff e is a metavariable, and we have an assignment of the
       form e := ?m + s, where + is an AC operator, and ?m is another metavariable. */
    bool is_partially_solved(expr const & e) {
        lean_assert(is_metavar(e));
        if (auto v = m_ctx.get_assignment(e)) {
            return is_ac(*v) && m_ctx.is_tmp_mvar(app_arg(app_fn(*v)));
        } else {
            return false;
        }
    }

    void flat_ac(expr const & op, expr const & e, buffer<expr> & args) {
        if (optional<expr> curr_op = get_binary_op(e)) {
            if (m_ctx.is_def_eq(op, *curr_op)) {
                flat_ac(op, app_arg(app_fn(e)), args);
                flat_ac(op, app_arg(e), args);
                return;
            }
        }
        args.push_back(e);
    }

    /* Cancel ground terms that occur in p_args and t_args.
       Example:
       Given
          [?x, 0, ?y] [a, b, 0, c],
       the result is:
            [?x, ?y] [a, b, c]
    */
    void ac_cancel_terms(buffer<expr> & p_args, buffer<expr> & t_args) {
        unsigned j = 0;
        for (unsigned i = 0; i < p_args.size(); i++) {
            if (has_expr_metavar(p_args[i])) {
                p_args[j] = p_args[i];
                j++;
            } else {
                expr p = tmp_internalize(p_args[i]);
                unsigned k = 0;
                for (; k < t_args.size(); k++) {
                    if (is_ground_eq(p, t_args[k])) {
                        break;
                    }
                }
                if (k == t_args.size()) {
                    p_args[j] = p;
                    j++;
                } else {
                    // cancelled
                    t_args.erase(k);
                }
            }
        }
        p_args.shrink(j);
    }

    expr mk_ac_term(expr const & op, buffer<expr> const & args) {
        lean_assert(!args.empty());
        expr r = args.back();
        unsigned i = args.size() - 1;
        while (i > 0) {
            --i;
            r = mk_app(op, args[i], r);
        }
        return r;
    }

    expr mk_ac_term(expr const & op, list<expr> const & args) {
        buffer<expr> b;
        to_buffer(args, b);
        return mk_ac_term(op, b);
    }

    void display_ac_cnstr(io_state_stream const & out, ematch_cnstr const & c) {
        expr p = mk_ac_term(ac_op(c), ac_p(c));
        expr t = mk_ac_term(ac_op(c), ac_t(c));
        auto fmt = out.get_formatter();
        format r = group(fmt(p) + line() + format("=?=") + line() + fmt(t));
        out << r;
    }

    void process_new_ac_cnstr(state const & s, expr const & p, expr const & t, buffer<pair<state, unsigned>> & new_states) {
        optional<expr> op = is_ac(t);
        lean_assert(op);
        buffer<expr> p_args, t_args;
        flat_ac(*op, p, p_args);
        flat_ac(*op, t, t_args);
        lean_assert(t_args.size() >= 2);
        if (p_args.empty()) {
            /* This can happen if we fail to unify the operator in p with the one in t. */
            return;
        }
        lean_assert(p_args.size() >= 2);
        ac_cancel_terms(p_args, t_args);
        if (p_args.size() == 1 && t_args.size() == 1) {
            new_states.emplace_back(cons(mk_match_eq_cnstr(p_args[0], t_args[0]), s), m_gen);
            return;
        }
        list<expr> ps  = to_list(p_args);
        buffer<expr> new_t_args;
        /* Create a family of AC-matching constraints by replacing t-arguments
           with op-applications that are in the same equivalence class.

           Example: given (a = b + c) (d = e + f) and t is of the form (a + d).
           expand, will add the following AC constraints

               p =?= a + d
               p =?= a + e + f
               p =?= b + c + d
               p =?= b + c + e + f

           To avoid non termination, we unfold a t_arg at most once.
           Here is an example that would produce non-termination if
           we did not use unfolded.

           Given (a = a + a) and t is of the form (a + d).
           We would be able to produce

              p =?= a + d
              p =?= a + a + d
              ...
              p =?= a + ... + a + d
              ...
        */
        std::function<void(unsigned, rb_expr_tree const &)>
        expand = [&](unsigned i, rb_expr_tree const & unfolded) {
            check_system("ematching");
            if (i == t_args.size()) {
                ematch_cnstr c = mk_match_ac_cnstr(*op, ps, to_list(new_t_args));
                lean_trace(name({"debug", "smt", "ematch"}), tout() << "new ac constraint: "; display_ac_cnstr(tout(), c); tout() << "\n";);
                new_states.emplace_back(cons(c, s), m_gen);
            } else {
                expr const & t_arg = t_args[i];
                new_t_args.push_back(t_arg);
                expand(i+1, unfolded);
                new_t_args.pop_back();
                /* search for op-applications in eqc(t_arg) */
                rb_expr_tree new_unfolded = unfolded;
                bool first = true;
                expr it    = t_arg;
                do {
                    if (auto op2 = is_ac(it)) {
                        if (*op == *op2) {
                            unsigned sz = t_args.size();
                            flat_ac(*op, it, t_args);
                            if (first) {
                                new_unfolded.insert(t_arg);
                                first = false;
                            }
                            expand(i+1, new_unfolded);
                            t_args.shrink(sz);
                        }
                    }
                    it = m_cc.get_next(it);
                } while (it != t_arg);
            }
        };
        expand(0, rb_expr_tree());
    }

    void push_states(buffer<pair<state, unsigned>> & new_states) {
        if (new_states.size() == 1) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(only one match)\n";);
            m_state = new_states[0].first;
            m_gen   = new_states[0].second;
        } else {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "# matches: " << new_states.size() << "\n";);
            m_state = new_states.back().first;
            m_gen   = new_states.back().second;
            new_states.pop_back();
            m_choice_stack.append(new_states);
            for (unsigned i = 0; i < new_states.size(); i++)
                m_ctx.push_scope();
        }
    }

    bool ac_merge_clash_p(expr const & p, expr const & t) {
        lean_assert(is_metavar(p) && is_partially_solved(p));
        tout() << "ac_merge_clash_p: " << p << " =?= " << t << "\n";
        // TODO(Leo):
        lean_unreachable();
    }

    bool is_ac_eqv(expr const & p, expr const & t) {
        lean_assert(is_ac(t));
        if (is_metavar(p) && is_partially_solved(p)) {
            return ac_merge_clash_p(p, t);
        } else {
            /* When AC support is enabled, metavariables may be assigned to terms
               that have not been internalized. */
            expr new_p = safe_instantiate_mvars(p);
            if (!has_expr_metavar(new_p)) {
                new_p = tmp_internalize(new_p);
                return is_ground_eq(new_p, t);
            } else {
                return m_ctx.is_def_eq(new_p, t);
            }
        }
    }

    bool is_eqv(expr const & p, expr const & t) {
        if (is_ac(t)) {
            return is_ac_eqv(p, t);
        } else if (!has_expr_metavar(p)) {
            return is_ground_eq(p, t);
        } else if (is_meta(p)) {
            expr const & m = get_app_fn(p);
            if (!m_ctx.is_assigned(m)) {
                expr p_type = safe_instantiate_mvars(m_ctx.infer(p));
                expr t_type = m_ctx.infer(t);
                if (m_ctx.is_def_eq(p_type, t_type)) {
                    /* Types are definitionally equal. So, we just assign */
                    return m_ctx.is_def_eq(p, t);
                } else if (!has_expr_metavar(p_type) && !has_expr_metavar(t_type)) {
                    /* Check if types are provably equal and apply cast
                       Here is some background on this case. p is a metavariable ?m.
                       So, it should be the argument of some function application (f a_1 ... a_k ?m ...).
                       Reason: p is a subterm of a valid pattern.
                       Then, t should also be the argument of a function application (f b_1 ... b_k t ...).
                       Reason: how the ematching procedure works.
                       Moreover, the types of ?m and t should be of the form
                             ?m : A_{k+1}[a_1 ... a_k]
                             t  : A_{k+1}[b_1 ... b_k]
                       The function applications are type correct, and the type of f should be of the form:
                          f : Pi (x_1 : A_1) (x_2 : A_2[x_1]) ... (x_k : A_k[x_1, ... x_{k-1}]) (x_{k+1} : A_{k+1}[x_1, ..., x_k]) ..., B
                       The subproblems a_i == b_i have already been processed. So,
                       A[a_1 ... a_k] is probably congruent to A[b_1 ... b_k].
                       We say "probably" because we may miss some cases depending on how the equalities
                       have been processed. For example, A_{k+1}[...] may contain binders,
                       and we may not have visited them.
                       Important: we must process arguments from left to right. Otherwise, the "trick"
                       above will not work.
                    */
                    p_type = tmp_internalize(p_type);
                    t_type = tmp_internalize(t_type);
                    if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                        expr cast_H_t = mk_cast(m_ctx, *H, t);
                        return m_ctx.is_def_eq(p, cast_H_t);
                    } else {
                        /* Types are not definitionally equal nor provably equal */
                        return false;
                    }
                } else {
                    /* Types are not definitionally equal, and we cannot check whether they are provably equal
                       using cc since they contain metavariables */
                    return false;
                }
            } else if (is_metavar(p) && is_partially_solved(p)) {
                return ac_merge_clash_p(p, t);
            } else {
                expr new_p = safe_instantiate_mvars(p);
                if (!has_expr_metavar(new_p)) {
                    return is_ground_eq(new_p, t);
                } else {
                    return m_ctx.is_def_eq(new_p, t);
                }
            }
        } else {
            return m_ctx.is_def_eq(p, t);
        }
    }

    /* If the eq equivalence class of `t` is heterogeneous, then even though
       `t` may fail to match because of its type, another element that is
       heterogeneously equal to `t`, but that has a different type, may match
       successfully. */
    bool match_leaf(expr const & p, expr const & t) {
        if (m_cc.in_heterogeneous_eqc(t)) {
            buffer<pair<state, unsigned>> new_states;
            rb_expr_set types_seen;
            expr it = t;
            do {
                expr it_type = m_ctx.infer(it);
                if (!types_seen.find(it_type)) {
                    types_seen.insert(it_type);
                    new_states.emplace_back(cons(mk_eqv_cnstr(p, it), m_state), m_gen);
                }
                it = m_cc.get_next(it);
            } while (it != t);
            push_states(new_states);
            return true;
        } else {
            return is_eqv(p, t);
        }
    }

    bool match_args(state & s, buffer<expr> const & p_args, expr const & t) {
        optional<ext_congr_lemma> cg_lemma = m_cc.mk_ext_congr_lemma(t);
        if (!cg_lemma) return false;
        buffer<expr> t_args;
        expr const & fn = get_app_args(t, t_args);
        if (p_args.size() != t_args.size())
            return false;
        if (cg_lemma->m_hcongr_lemma) {
            /* Lemma was created using mk_hcongr_lemma */
            fun_info finfo                 = get_fun_info(m_ctx, fn, t_args.size());
            list<ss_param_info> sinfo      = get_subsingleton_info(m_ctx, fn, t_args.size());
            list<param_info> const * it1   = &finfo.get_params_info();
            list<ss_param_info> const *it2 = &sinfo;
            buffer<ematch_cnstr> new_cnstrs;
            for (unsigned i = 0; i < t_args.size(); i++) {
                if (*it1 && head(*it1).is_inst_implicit()) {
                    new_cnstrs.push_back(mk_defeq_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::DefEqOnly);
                } else if (*it2 && head(*it2).is_subsingleton()) {
                    new_cnstrs.push_back(mk_match_ss_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::MatchSS);
                } else {
                    new_cnstrs.push_back(mk_match_eq_cnstr(p_args[i], t_args[i]));
                    lean_assert(new_cnstrs.back().kind() == ematch_cnstr_kind::Match);
                }
                if (*it1) it1 = &tail(*it1);
                if (*it2) it2 = &tail(*it2);
            }
            s = to_list(new_cnstrs.begin(), new_cnstrs.end(), s);
            return true;
        } else {
            return false;
        }
    }

    bool process_match(expr const & p, expr const & t) {
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "try process_match: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);
        if (!is_app(p)) {
            return match_leaf(p, t);
        }
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        if (m_ctx.is_tmp_mvar(fn)) {
            return match_leaf(p, t);
        }
        buffer<pair<expr, unsigned>> candidates;
        expr t_fn;
        expr it = t;
        do {
            if (check_generation(it)) {
                expr const & it_fn = get_app_fn(it);
                bool ok = false;
                if ((m_cc.is_congr_root(it) || m_cc.in_heterogeneous_eqc(it)) &&
                    m_ctx.is_def_eq(it_fn, fn) &&
                    get_app_num_args(it) == p_args.size()) {
                    t_fn = it_fn;
                    ok = true;
                    candidates.emplace_back(it, m_cc.get_generation_of(it));
                }
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "candidate: " << it << "..." << (ok ? "ok" : "skip") << "\n";);
            }
            it = m_cc.get_next(it);
        } while (it != t);

        if (candidates.empty()) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(no candidates)\n";);
            return false;
        }
        buffer<pair<state, unsigned>> new_states;
        for (pair<expr, unsigned> const & c_gen : candidates) {
            expr const & c = c_gen.first;
            unsigned gen   = c_gen.second;
            state new_state = m_state;
            if (is_ac(c)) {
                process_new_ac_cnstr(new_state, p, t, new_states);
            } else if (match_args(new_state, p_args, c)) {
                lean_trace(name({"debug", "smt", "ematch"}), tout() << "match: " << c << "\n";);
                new_states.emplace_back(new_state, std::max(m_gen, gen));
            }
        }
        if (new_states.empty()) {
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(no new states)\n";);
            return false;
        }
        push_states(new_states);
        return true;
    }

    bool match_args_prefix(state & s, buffer<expr> const & p_args, expr const & t) {
        unsigned t_nargs = get_app_num_args(t);
        expr it = t;
        while (t_nargs > p_args.size()) {
            t_nargs--;
            it = app_fn(it);
        }
        return match_args(s, p_args, it);
    }

    bool check_generation(expr const & t) {
        unsigned gen = m_cc.get_generation_of(t);
        if (gen >= m_em_state.m_config.m_max_generation) {
            lean_trace(name({"smt", "ematch"}), tout() << "skipping term generation: " << gen
                       << ", instances based on exceeds the limit\n" << t << "\n";);
            return false;
        } else {
            return true;
        }
    }

    bool process_continue(expr const & p) {
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "process_continue: " << p << "\n";);
        buffer<expr> p_args;
        expr const & f = get_app_args(p, p_args);
        buffer<pair<state, unsigned>> new_states;
        if (auto s = m_em_state.get_app_map().find(head_index(f))) {
            s->for_each([&](expr const & t) {
                    if (check_generation(t) && (m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t))) {
                        state new_state = m_state;
                        if (match_args_prefix(new_state, p_args, t))
                            new_states.emplace_back(new_state, m_cc.get_generation_of(t));
                    }
                });
            if (new_states.empty()) {
                return false;
            } else {
                push_states(new_states);
                return true;
            }
        } else {
            return false;
        }
    }

    /* (Basic) subsingleton matching support: solve p =?= t when
       typeof(p) and typeof(t) are subsingletons */
    bool process_matchss(expr const & p, expr const & t) {
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "process_matchss: " << p << " ::= " << new_p << " : " << new_p_type << " <=?=> "
                   << t << " : " << t_type << "\n";);
        if (!is_metavar(p)) {
            /* If p is not a metavariable we simply ignore it.
               We should improve this case in the future. */
            lean_trace(name({"debug", "smt", "ematch"}), tout() << "(p not a metavar)\n";);
            return true;
        }
        expr p_type = safe_instantiate_mvars(m_ctx.infer(p));
        expr t_type = m_ctx.infer(t);
        if (m_ctx.is_def_eq(p_type, t_type)) {
            bool success = m_ctx.is_def_eq(p, t);
            lean_trace(name({"debug", "smt", "ematch"}),
                       tout() << "types are def_eq and assignment..." << (success ? "succeeded" : "failed") << "\n";);
            return success;
        } else {
            /* Check if the types are provably equal, and cast t */
            p_type = tmp_internalize(p_type);
            if (auto H = m_cc.get_eq_proof(t_type, p_type)) {
                expr cast_H_t = mk_cast(m_ctx, *H, t);
                bool success = m_ctx.is_def_eq(p, cast_H_t);
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "types can be proved equal and assignment..." << (success ? "succeeded" : "failed") << "\n";);
                return success;
            }
        }
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "types cannot be proved equal\n";);
        return false;
    }

    bool process_defeq_only(ematch_cnstr const & c) {
        expr const & p = cnstr_p(c);
        expr const & t = cnstr_t(c);
        bool success = m_ctx.is_def_eq(p, t);
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "must be def-eq: " << new_p << " : " << new_p_type
                   << "  =?= " << t << " : " << t_type
                   << " ... " << (success ? "succeeded" : "failed") << "\n";);
        return success;
    }

    bool process_eqv_only(ematch_cnstr const & c) {
        expr const & p = cnstr_p(c);
        expr const & t = cnstr_t(c);
        bool success = is_eqv(p, t);
        lean_trace(name({"debug", "smt", "ematch"}),
                   expr new_p      = safe_instantiate_mvars(p);
                   expr new_p_type = safe_instantiate_mvars(m_ctx.infer(p));
                   expr t_type     = m_ctx.infer(t);
                   tout() << "must be eqv: " << new_p << " : " << new_p_type << " =?= "
                   << t << " : " << t_type << " ... " << (success ? "succeeded" : "failed") << "\n";);
        return success;
    }

    bool process_match_ac(ematch_cnstr const & /* c */) {
        // TODO(Leo)
        lean_unreachable();
    }

    bool is_done() const {
        return is_nil(m_state);
    }

    bool process_next() {
        lean_assert(!is_done());
        /* TODO(Leo): select easy constraint first */
        ematch_cnstr c = head(m_state);
        m_state        = tail(m_state);

        switch (c.kind()) {
        case ematch_cnstr_kind::DefEqOnly:
            return process_defeq_only(c);
        case ematch_cnstr_kind::Match:
            return process_match(cnstr_p(c), cnstr_t(c));
        case ematch_cnstr_kind::EqvOnly:
            return process_eqv_only(c);
        case ematch_cnstr_kind::MatchSS:
            return process_matchss(cnstr_p(c), cnstr_t(c));
        case ematch_cnstr_kind::Continue:
            return process_continue(cont_p(c));
        case ematch_cnstr_kind::MatchAC:
            return process_match_ac(c);
        }
        lean_unreachable();
    }

    bool backtrack() {
        lean_trace(name({"debug", "smt", "ematch"}), tout() << "backtrack\n";);
        if (m_choice_stack.empty())
            return false;
        m_ctx.pop_scope();
        m_state = m_choice_stack.back().first;
        m_gen   = m_choice_stack.back().second;
        m_choice_stack.pop_back();
        return true;
    }

    void instantiate(hinst_lemma const & lemma) {
        list<bool> const * it = &lemma.m_is_inst_implicit;
        buffer<expr> lemma_args;
        for (expr const & mvar : lemma.m_mvars) {
            if (!m_ctx.is_assigned(mvar)) {
                if (!head(*it)) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unassigned argument not inst-implicit: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, argument is not instance implicit
                }
                auto new_val = m_ctx.mk_class_instance(m_ctx.infer(mvar));
                if (!new_val) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "cannot synthesize unassigned inst-implicit argument: " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, instance could not be generated
                }
                if (!m_ctx.is_def_eq(mvar, *new_val)) {
                    lean_trace(name({"debug", "smt", "ematch"}),
                               tout() << "instantiation failure [" << lemma.m_id << "], " <<
                               "unable to assign inst-implicit argument: " << *new_val << " : " << m_ctx.infer(mvar) << "\n";);
                    return; // fail, type error
                }
            }
            lemma_args.push_back(mvar);
            it = &tail(*it);
        }

        for (expr & lemma_arg : lemma_args) {
            lemma_arg = instantiate_mvars(lemma_arg);
            if (has_idx_metavar(lemma_arg)) {
                lean_trace(name({"debug", "smt", "ematch"}),
                           tout() << "instantiation failure [" << lemma.m_id << "], " <<
                           "there are unassigned metavariables\n";);
                return; // result contains temporary metavariables
            }
        }

        if (!m_em_state.save_instance(lemma.m_prop, lemma_args)) {
            return; // already added this instance
        }

        expr new_inst  = instantiate_mvars(lemma.m_prop);
        if (has_idx_metavar(new_inst)) {
            lean_trace(name({"debug", "smt", "ematch"}),
                       tout() << "new instance contains unassigned metavariables\n"
                       << new_inst << "\n";);
            return; // result contains temporary metavariables
        }

        lean_trace(name({"smt", "ematch"}),
                   tout() << "instance [" << lemma.m_id << "], generation: " << m_gen+1
                   << "\n" << new_inst << "\n";);
        expr new_proof = instantiate_mvars(lemma.m_proof);
        m_new_instances.push_back({new_inst, new_proof, m_gen+1});
    }

    void search(hinst_lemma const & lemma) {
        while (true) {
            check_system("ematching");
            if (is_done()) {
                instantiate(lemma);
                if (!backtrack())
                    return;
            }
            if (!process_next()) {
                if (!backtrack())
                    return;
            }
        }
    }

    void clear_choice_stack() {
        for (unsigned i = 0; i < m_choice_stack.size(); i++) {
            m_ctx.pop_scope();
        }
        m_choice_stack.clear();
    }

    state mk_inital_state(buffer<expr> const & ps) {
        state s;
        unsigned i = ps.size();
        while (i > 1) {
            --i;
            s = cons(mk_continue(ps[i]), s);
        }
        return s;
    }

    /* Ematch p =?= t with initial state init. p is the pattern, and t is a term.
       The inital state init is used for multipatterns.
       The given lemma is instantiated for each solution found.
       The new instances are stored at m_new_instances. */
    void main(hinst_lemma const & lemma, state const & init, expr const & p, expr const & t) {
        type_context_old::tmp_mode_scope scope(m_ctx, lemma.m_num_uvars, lemma.m_num_mvars);
        lean_assert(!has_idx_metavar(t));
        clear_choice_stack();
        m_state = init;
        buffer<expr> p_args;
        expr const & fn = get_app_args(p, p_args);
        m_gen = m_cc.get_generation_of(t);
        if (!m_ctx.is_def_eq(fn, get_app_fn(t)))
            return;
        if (check_generation(t) && !match_args_prefix(m_state, p_args, t))
            return;
        search(lemma);
    }

    void ematch_term(hinst_lemma const & lemma, multi_pattern const & mp, expr const & t) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        /* TODO(Leo): use heuristic to select the pattern we will match first */
        state init_state = mk_inital_state(ps);
        main(lemma, init_state, ps[0], t);
    }

    void ematch_terms_core(hinst_lemma const & lemma, buffer<expr> const & ps, bool filter) {
        expr const & fn  = get_app_fn(ps[0]);
        unsigned gmt     = m_cc.get_gmt();
        state init_state = mk_inital_state(ps);
        if (rb_expr_set const * s = m_em_state.get_app_map().find(head_index(fn))) {
            s->for_each([&](expr const & t) {
                    if ((m_cc.is_congr_root(t) || m_cc.in_heterogeneous_eqc(t)) &&
                        (!filter || m_cc.get_mt(t) == gmt)) {
                        main(lemma, init_state, ps[0], t);
                    }
                });
        }
    }

    /* Match internalized terms in m_em_state with the given multipatterns.
       If filter is true, then we use the term modification time information
       stored in the congruence closure module. Only terms with
       modification time (mt) >= the global modification time (gmt) are considered. */
    void ematch_terms(hinst_lemma const & lemma, multi_pattern const & mp, bool filter) {
        buffer<expr> ps;
        to_buffer(mp, ps);
        if (filter) {
            for (unsigned i = 0; i < ps.size(); i++) {
                std::swap(ps[0], ps[i]);
                ematch_terms_core(lemma, ps, filter);
                std::swap(ps[0], ps[i]);
            }
        } else {
            ematch_terms_core(lemma, ps, filter);
        }
    }


    /* Match internalized terms in m_em_state with the given lemmas. */
    void ematch_using_lemmas(hinst_lemmas const & lemmas, bool filter) {
        lemmas.for_each([&](hinst_lemma const & lemma) {
                if (!m_em_state.max_instances_exceeded()) {
                    ematch_terms(lemma, filter);
                }
            });
    }

public:
    ematch_fn(type_context_old & ctx, ematch_state & ems, congruence_closure & cc, buffer<new_instance> & new_insts):
        m_ctx(ctx), m_em_state(ems), m_cc(cc), m_new_instances(new_insts) {}

    void ematch_term(hinst_lemma const & lemma, expr const & t) {
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch_term(lemma, mp, t);
        }
    }

    /* Match internalized terms in m_em_state with the given lemma. */
    void ematch_terms(hinst_lemma const & lemma, bool filter) {
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        for (multi_pattern const & mp : lemma.m_multi_patterns) {
            ematch_terms(lemma, mp, filter);
        }
    }

    void operator()() {
        if (m_em_state.max_instances_exceeded())
            return;
        /* The following scope is a temporary workaround, we need to refactor this module
           and adapt all improvements added to type_context_old::is_def_eq. */
        ematch_using_lemmas(m_em_state.get_new_lemmas(), false);
        ematch_using_lemmas(m_em_state.get_lemmas(), true);
        m_em_state.m_lemmas.merge(m_em_state.m_new_lemmas);
        m_em_state.m_new_lemmas = hinst_lemmas();
        m_cc.inc_gmt();
    }
};

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, expr const & t, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result).ematch_term(lemma, t);
}

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, hinst_lemma const & lemma, bool filter, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result).ematch_terms(lemma, filter);
}

void ematch(type_context_old & ctx, ematch_state & s, congruence_closure & cc, buffer<new_instance> & result) {
    congruence_closure::state_scope scope(cc);
    ematch_fn(ctx, s, cc, result)();
}

struct vm_ematch_state : public vm_external {
    ematch_state m_val;
    vm_ematch_state(ematch_state const & v): m_val(v) {}
    virtual ~vm_ematch_state() {}
    virtual void dealloc() override { this->~vm_ematch_state(); get_vm_allocator().deallocate(sizeof(vm_ematch_state), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_ematch_state(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_ematch_state))) vm_ematch_state(m_val); }
};

ematch_state const & to_ematch_state(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_ematch_state*>(to_external(o)));
    return static_cast<vm_ematch_state*>(to_external(o))->m_val;
}

vm_obj to_obj(ematch_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_ematch_state))) vm_ematch_state(s));
}

/*
structure ematch_config :=
(max_instances  : nat := 10000)
(max_generation : nat := 10)
*/
ematch_config to_ematch_config(vm_obj const & cfg) {
    ematch_config r;
    r.m_max_instances  = force_to_unsigned(cfield(cfg, 0));
    r.m_max_generation = force_to_unsigned(cfield(cfg, 1));
    return r;
}

vm_obj ematch_state_mk(vm_obj const & cfg) {
    return to_obj(ematch_state(to_ematch_config(cfg)));
}

vm_obj ematch_state_internalize(vm_obj const & ems, vm_obj const & e, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    ematch_state S   = to_ematch_state(ems);
    type_context_old ctx = mk_type_context_for(s);
    S.internalize(ctx, to_expr(e));
    return tactic::mk_success(to_obj(S), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj mk_ematch_result(buffer<new_instance> const & new_inst_buffer, congruence_closure::state const & ccs,
                        ematch_state const & ems) {
    vm_obj new_insts = mk_vm_nil();
    unsigned i = new_inst_buffer.size();
    while (i > 0) {
        --i;
        new_insts = mk_vm_cons(mk_vm_pair(to_obj(new_inst_buffer[i].m_instance), to_obj(new_inst_buffer[i].m_proof)), new_insts);
    }
    return mk_vm_pair(new_insts, mk_vm_pair(to_obj(ccs), to_obj(ems)));
}

vm_obj ematch_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & t, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(_s, md);
    ematch_state ems    = to_ematch_state(_ems);
    defeq_can_state dcs = s.dcs();
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs, dcs);
    buffer<new_instance> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_expr(t), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = set_dcs(s, dcs);
    return tactic::mk_success(r, new_s);
    LEAN_TACTIC_CATCH(s);
}

vm_obj ematch_all_core(vm_obj const & md, vm_obj const & _ccs, vm_obj const & _ems, vm_obj const & hlemma, vm_obj const & filter, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(_s, md);
    ematch_state ems    = to_ematch_state(_ems);
    defeq_can_state dcs = s.dcs();
    congruence_closure::state ccs = to_cc_state(_ccs);
    congruence_closure cc(ctx, ccs, dcs);
    buffer<new_instance> new_inst_buffer;
    ematch(ctx, ems, cc, to_hinst_lemma(hlemma), to_bool(filter), new_inst_buffer);
    vm_obj r = mk_ematch_result(new_inst_buffer, ccs, ems);
    tactic_state new_s = set_dcs(s, dcs);
    return tactic::mk_success(r, new_s);
    LEAN_TACTIC_CATCH(s);
}

void initialize_ematch() {
    register_trace_class(name{"smt", "ematch"});
    register_trace_class(name({"debug", "smt", "ematch"}));

    DECLARE_VM_BUILTIN(name({"ematch_state", "mk"}),               ematch_state_mk);
    DECLARE_VM_BUILTIN(name({"ematch_state", "internalize"}),      ematch_state_internalize);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_core"}),            ematch_core);
    DECLARE_VM_BUILTIN(name({"tactic", "ematch_all_core"}),        ematch_all_core);
}
void finalize_ematch() {
}
}




// ========== smt_state.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
#include "library/tactic/simp_lemmas.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
class smt;

struct smt_pre_config {
    name        m_simp_attr;
    simp_lemmas m_simp_lemmas;
    unsigned    m_max_steps;
    bool        m_zeta;
};

struct smt_config {
    name_set       m_ho_fns;
    cc_config      m_cc_config;
    ematch_config  m_em_config;
    smt_pre_config m_pre_config;
    name           m_em_attr;
    hinst_lemmas   m_em_lemmas;
};

typedef std::shared_ptr<smt_config> smt_config_ref;

class smt_goal {
    friend class smt;
    cc_state       m_cc_state;
    ematch_state   m_em_state;
    smt_config_ref m_cfg;
public:
    smt_goal(smt_config_ref const & cfg);
    smt_goal(smt_config const & cfg);
    cc_state const & get_cc_state() const { return m_cc_state; }
    ematch_state const & get_em_state() const { return m_em_state; }
    smt_pre_config const & get_pre_config() const { return m_cfg->m_pre_config; }
    smt_config const & get_config() const { return *m_cfg; }

    void add_lemma(hinst_lemma const & lemma) { m_em_state.add_lemma(lemma); }
    void set_lemmas(hinst_lemmas const & lemmas) { m_em_state.set_lemmas(lemmas); }
};

class smt : public cc_propagation_handler, public cc_normalizer {
private:
    type_context_old &     m_ctx;
    defeq_can_state &  m_dcs;
    smt_goal &         m_goal;
    congruence_closure m_cc;

    lbool get_value_core(expr const & e);
    lbool get_value(expr const & e);
    virtual void propagated(unsigned n, expr const * p) override;
    virtual void new_aux_cc_term(expr const & e) override;
    virtual expr normalize(expr const & e) override;
public:
    smt(type_context_old & ctx, defeq_can_state & dcs, smt_goal & g);
    virtual ~smt();

    void internalize(expr const & e);
    void add(expr const & type, expr const & proof, unsigned gen = 0);
    void ematch(buffer<new_instance> & result);
    void ematch_using(hinst_lemma const & lemma, buffer<new_instance> & result);

    defeq_can_state & dcs() { return m_dcs; }
    smt_pre_config const & get_pre_config() { return m_goal.get_pre_config(); }

    optional<expr> get_proof(expr const & e);
    bool inconsistent() const { return m_cc.inconsistent(); }
    optional<expr> get_inconsistency_proof() const { return m_cc.get_inconsistency_proof(); }
    optional<expr> get_eq_proof(expr const & lhs, expr const & rhs) const {
        return m_cc.get_eq_proof(lhs, rhs);
    }
};

bool is_smt_goal(vm_obj const & o);
smt_goal const & to_smt_goal(vm_obj const & o);
vm_obj to_obj(smt_goal const & s);

format smt_state_pp(vm_obj const & ss, tactic_state const & ts);

void initialize_smt_state();
void finalize_smt_state();
}




// ========== smt_state.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/delayed_abstraction.h"
#include "library/type_context.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/tactic/user_attribute.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/dsimplify.h"
#include "library/tactic/simplify.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/change_tactic.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/smt_state.h"

namespace lean {
smt_goal::smt_goal(smt_config_ref const & cfg):
    m_cc_state(cfg->m_ho_fns, cfg->m_cc_config),
    m_em_state(cfg->m_em_config, cfg->m_em_lemmas),
    m_cfg(cfg) {
}

smt_goal::smt_goal(smt_config const & cfg):
    smt_goal(std::make_shared<smt_config>(cfg)) {
}

smt::smt(type_context_old & ctx, defeq_can_state & dcs, smt_goal & g):
    m_ctx(ctx),
    m_dcs(dcs),
    m_goal(g),
    m_cc(ctx, m_goal.m_cc_state, dcs, this, this) {
}

smt::~smt() {
}

void smt::propagated(unsigned n, expr const * p) {
    lean_trace(name({"smt", "fact"}), scope_trace_env _(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               format r;
               for (unsigned i = 0; i < n; i++) { if (i > 0) r += comma() + line(); r += fmt(p[i]); }
               tout() << group(format("new facts:") + line() + bracket("{", r, "}")) << "\n";);
}

lbool smt::get_value_core(expr const & e) {
    if (m_cc.is_eqv(e, mk_true())) return l_true;
    if (m_cc.is_eqv(e, mk_false())) return l_false;
    return l_undef;
}

lbool smt::get_value(expr const & e) {
    lbool r = get_value_core(e);
    if (r != l_undef) return r;
    expr arg;
    if (is_not(e, arg)) {
        return ~get_value_core(arg);
    }
    return l_undef;
}

optional<expr> smt::get_proof(expr const & e) {
    if (m_cc.is_eqv(e, mk_true()))
        if (auto pr = m_cc.get_eq_proof(e, mk_true()))
            return some_expr(mk_of_eq_true(m_ctx, *pr));
    expr arg;
    if (is_not(e, arg) && m_cc.is_eqv(arg, mk_false()))
        if (auto pr = m_cc.get_eq_proof(arg, mk_false()))
            return some_expr(mk_not_of_eq_false(m_ctx, *pr));
    return none_expr();
}

void smt::internalize(expr const & e) {
    m_cc.internalize(e, 0);
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::new_aux_cc_term(expr const & e) {
    m_goal.m_em_state.internalize(m_ctx, e);
}

void smt::add(expr const & type, expr const & proof, unsigned gen) {
    m_goal.m_em_state.internalize(m_ctx, type);
    m_cc.add(type, proof, gen);
}

void smt::ematch(buffer<new_instance> & result) {
    ::lean::ematch(m_ctx, m_goal.m_em_state, m_cc, result);
}

void smt::ematch_using(hinst_lemma const & lemma, buffer<new_instance> & result) {
    ::lean::ematch(m_ctx, m_goal.m_em_state, m_cc, lemma, false, result);
}

static dsimplify_fn mk_dsimp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg);

expr smt::normalize(expr const & e) {
    type_context_old::zeta_scope _1(m_ctx, m_goal.get_pre_config().m_zeta);
    dsimplify_fn dsimp       = mk_dsimp(m_ctx, m_dcs, m_goal.get_pre_config());
    return dsimp(e);
}

struct vm_smt_goal : public vm_external {
    smt_goal m_val;
    vm_smt_goal(smt_goal const & v):m_val(v) {}
    virtual ~vm_smt_goal() {}
    virtual void dealloc() override {
        this->~vm_smt_goal(); get_vm_allocator().deallocate(sizeof(vm_smt_goal), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_smt_goal(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_smt_goal))) vm_smt_goal(m_val); }
};

bool is_smt_goal(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_smt_goal*>(to_external(o));
}

smt_goal const & to_smt_goal(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_smt_goal*>(to_external(o)));
    return static_cast<vm_smt_goal*>(to_external(o))->m_val;
}

vm_obj to_obj(smt_goal const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_smt_goal))) vm_smt_goal(s));
}

vm_obj mk_smt_tactic_success(vm_obj const & a, vm_obj const & ss, vm_obj const & ts) {
    return tactic::mk_success(mk_vm_pair(a, ss), ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, vm_obj const & ts) {
    return mk_smt_tactic_success(mk_vm_unit(), ss, ts);
}

vm_obj mk_smt_tactic_success(vm_obj const & ss, tactic_state const & ts) {
    return mk_smt_tactic_success(ss, to_obj(ts));
}

vm_obj tactic_success_to_smt_tactic_success(vm_obj const & r, vm_obj const & ss) {
    return mk_smt_tactic_success(tactic::get_success_value(r), ss, tactic::get_success_state(r));
}

/* Remove auxiliary definitions introduced by the equation compiler.
   Reason: ematching will close the goal by instantiating them.
   Then later, the equation compiler will fail to eliminate this application
   using structural or well founded induction. */
static tactic_state clear_recs(tactic_state const & s) {
    lean_assert(s.goals());
    expr mvar                = head(s.goals());
    metavar_context mctx     = s.mctx();
    expr new_mvar            = clear_recs(mctx, mvar);
    if (new_mvar == mvar)
        return s;
    else
        return set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals())));
}

static optional<local_instance> get_last_local_instance(local_context const & lctx) {
    if (optional<local_instances> const & lis = lctx.get_frozen_local_instances()) {
        if (*lis)
            return optional<local_instance>(head(*lis));
    }
    return optional<local_instance>();
}

static pair<tactic_state, unsigned> revert_all(tactic_state const & s) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    local_context lctx       = g->get_context();
    buffer<expr> hs;
    if (optional<local_instance> const & last_local_inst = get_last_local_instance(lctx)) {
        /* We should not revert local instances. */
        local_decl const & last_local_inst_decl = lctx.get_local_decl(mlocal_name(last_local_inst->get_local()));
        lctx.for_each_after(last_local_inst_decl, [&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    } else {
        lctx.for_each([&](local_decl const & d) { hs.push_back(d.mk_ref()); });
    }
    bool preserve_to_revert_order = false;
    tactic_state new_s = revert(hs, s, preserve_to_revert_order);
    return mk_pair(new_s, hs.size());
}

static dsimplify_fn mk_dsimp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg) {
    dsimp_config dcfg;
    dcfg.m_max_steps          = cfg.m_max_steps;
    dcfg.m_canonize_instances = false;
    /* We use eta reduction to make sure terms such as (fun x, list x) are reduced to list.

       Given (a : nat) (l : list nat) (a ∈ a::l), the elaborator produces

              @mem nat list (@list.has_mem nat) a (a::l)

       On the other hand, it elaborates (λ (α : Type u) (l : list α) (a : α), a ∈ l) as

             (λ (α : Type u) (l : list α) (a : α), @mem α (λ (α : Type u), list α) (@list.has_mem α) a l)

       Another option is to use eta expansion. When we have metavariables, eta expansion is a better option.
       Example:  (fun x, ?m)  =?= f
       To solve this unification problem, we need to eta expand.

       This is not an issue in this module since it assumes goals do not contain metavariables.
    */
    dcfg.m_eta               = true;
    simp_lemmas_for eq_lemmas;
    if (auto r = cfg.m_simp_lemmas.find(get_eq_name()))
        eq_lemmas = *r;
    return dsimplify_fn(ctx, dcs, eq_lemmas, list<name>(), dcfg);
}

static simplify_fn mk_simp(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg) {
    simp_config scfg;
    scfg.m_max_steps          = cfg.m_max_steps;
    scfg.m_contextual         = false;
    scfg.m_lift_eq            = true;
    scfg.m_canonize_instances = true;
    scfg.m_canonize_proofs    = false;
    scfg.m_use_axioms         = true;
    scfg.m_zeta               = cfg.m_zeta;
    return simplify_fn(ctx, dcs, cfg.m_simp_lemmas, list<name>(), scfg);
}

static simp_result preprocess(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg, expr const & e) {
    type_context_old::zeta_scope         scope1(ctx, cfg.m_zeta);
    type_context_old::transparency_scope scope2(ctx, transparency_mode::Reducible);
    dsimplify_fn dsimp       = mk_dsimp(ctx, dcs, cfg);
    expr new_e               = dsimp(e);
    simplify_fn simp         = mk_simp(ctx, dcs, cfg);
    simp_result r            = simp(get_eq_name(), new_e);
    return r;
}

static vm_obj preprocess(tactic_state s, smt_pre_config const & cfg) {
    lean_assert(s.goals());
    optional<metavar_decl> g = s.get_main_goal_decl();
    type_context_old ctx         = mk_type_context_for(s, transparency_mode::Reducible);
    expr target              = g->get_type();
    defeq_can_state dcs      = s.dcs();
    simp_result r            = preprocess(ctx, dcs, cfg, target);
    if (!r.has_proof()) {
        tactic_state new_s = set_dcs(s, dcs);
        return change(r.get_new(), new_s);
    } else {
        expr new_M           = ctx.mk_metavar_decl(ctx.lctx(), r.get_new());
        expr h               = mk_eq_mpr(ctx, r.get_proof(), new_M);
        metavar_context mctx = ctx.mctx();
        mctx.assign(head(s.goals()), h);
        tactic_state new_s   = set_mctx_goals_dcs(s, mctx, cons(new_M, tail(s.goals())), dcs);
        return tactic::mk_success(new_s);
    }
}

static expr_pair preprocess_forward(type_context_old & ctx, defeq_can_state & dcs, smt_pre_config const & cfg, expr const & type, expr const & h) {
    simp_result r = preprocess(ctx, dcs, cfg, type);
    if (r.has_proof()) {
        expr new_h = mk_eq_mp(ctx, r.get_proof(), h);
        return mk_pair(r.get_new(), new_h);
    } else if (r.get_new() == type) {
        return mk_pair(type, h);
    } else {
        return mk_pair(r.get_new(), mk_id(ctx, r.get_new(), h));
    }
}

static expr_pair preprocess_forward(type_context_old & ctx, defeq_can_state & dcs, smt_goal const & g, expr const & type, expr const & h) {
    return preprocess_forward(ctx, dcs, g.get_pre_config(), type, h);
}

static name mk_intro_name(type_context_old & ctx, name const & bname, bool use_unused_names, list<name> & user_ids) {
    if (user_ids) {
        name r   = head(user_ids);
        user_ids = tail(user_ids);
        return r;
    } else if (use_unused_names) {
        return ctx.get_unused_name(bname);
    } else {
        return bname;
    }
}

/* This try_to_pi version only unfolds the head symbol if it is a not-application or a reducible constant. */
static expr convervative_try_to_pi(type_context_old & ctx, expr const & e) {
    expr new_e = ctx.whnf_head_pred(e, [&](expr const & t) {
            if (is_not(t)) return true;
            expr const & fn = get_app_fn(e);
            return is_constant(fn) && is_reducible(ctx.env(), const_name(fn));
        });
    return is_pi(new_e) ? new_e : e;
}

static expr intros(environment const & env, options const & opts, metavar_context & mctx, expr const & mvar,
                   defeq_can_state & dcs, smt_goal & s_goal, bool use_unused_names,
                   optional<unsigned> const & num, list<name> ids) {
    optional<metavar_decl> decl = mctx.find_metavar_decl(mvar);
    lean_assert(decl);
    type_context_old ctx(env, opts, mctx, decl->get_context(), transparency_mode::Semireducible);
    smt S(ctx, dcs, s_goal);
    /* We need to use dsimp to canonize instances as we introduce hypotheses.
       Example: suppose we are introducing
         forall {α : Type u} [field α] (x y : α), f (x + y) (y + x) (x + y) = 0

       The nested instances of has_add and has_zero must be canonized and registered at dcs.
    */
    dsimplify_fn dsimp = mk_dsimp(ctx, dcs, s_goal.get_pre_config());
    type_context_old::zeta_scope _1(ctx, s_goal.get_pre_config().m_zeta);
    expr target = decl->get_type();
    type_context_old::tmp_locals locals(ctx);
    buffer<expr> new_Hs;
    buffer<expr> to_inst;
    for (unsigned i = 0; !num || i < *num; i++) {
        if (!is_pi(target) && !is_let(target)) {
            target = instantiate_rev(target, to_inst.size(), to_inst.data());
            to_inst.clear();
            if (!num) {
                target = convervative_try_to_pi(ctx, target);
            } else {
                target = ctx.relaxed_try_to_pi(target);
            }
        }
        if (is_pi(target)) {
            expr type = dsimp(instantiate_rev(binding_domain(target), to_inst.size(), to_inst.data()));
            name n    = mk_intro_name(ctx, binding_name(target), use_unused_names, ids);
            expr h    = locals.push_local(n, type);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(h);
            S.add(type, h);
            lean_trace(name({"smt", "intro"}), scope_trace_env _(env, ctx);
                       tout() << n << " : " << type << "\n";);
            target = binding_body(target);
        } else if (is_let(target)) {
            expr type  = dsimp(instantiate_rev(let_type(target), to_inst.size(), to_inst.data()));
            expr value = dsimp(instantiate_rev(let_value(target), to_inst.size(), to_inst.data()));
            name n     = mk_intro_name(ctx, let_name(target), use_unused_names, ids);
            expr h     = locals.push_let(n, type, value);
            to_inst.push_back(h);
            new_Hs.push_back(h);
            S.internalize(type);
            S.internalize(value);
            S.add(type, h);
            lean_trace(name({"smt", "intro"}), scope_trace_env _(env, ctx);
                       tout() << n << " : " << type << "\n";);
            target = let_body(target);
        } else {
            break;
        }
    }
    target = dsimp(instantiate_rev(target, to_inst.size(), to_inst.data()));

    expr new_M   = ctx.mk_metavar_decl(ctx.lctx(), target);
    expr new_val = abstract_locals(mk_delayed_abstraction_with_locals(new_M, new_Hs), new_Hs.size(), new_Hs.data());
    unsigned i   = new_Hs.size();
    while (i > 0) {
        --i;
        local_decl d = ctx.lctx().get_local_decl(new_Hs[i]);
        expr type = d.get_type();
        type      = abstract_locals(type, i, new_Hs.data());
        if (auto letval = d.get_value()) {
            letval    = abstract_locals(*letval, i, new_Hs.data());
            new_val   = mk_let(d.get_pp_name(), type, *letval, new_val);
        } else {
            new_val   = mk_lambda(d.get_pp_name(), type, new_val, d.get_info());
        }
    }
    lean_assert(!ctx.mctx().is_assigned(new_M));
    mctx = ctx.mctx();
    mctx.assign(mvar, new_val);
    return new_M;
}

/* Assert lemma in the current state if does not have universal metavariables, and return true.
   Return false otherwise. */
static bool add_em_fact(smt & S, type_context_old & ctx, hinst_lemma const & lemma) {
    if (lemma.m_num_mvars == 0 && lemma.m_num_uvars == 0) {
        expr type  = lemma.m_prop;
        expr h     = lemma.m_proof;
        std::tie(type, h) = preprocess_forward(ctx, S.dcs(), S.get_pre_config(), type, h);
        lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                   tout() << "new ground fact: " << type << "\n";);
        S.add(type, h);
        return true;
    } else {
        return false;
    }
}

tactic_state add_em_facts(tactic_state const & ts, smt_goal & g) {
    type_context_old ctx      = mk_type_context_for(ts);
    defeq_can_state dcs   = ts.dcs();
    smt S(ctx, dcs, g);
    hinst_lemmas lemmas   = g.get_em_state().get_new_lemmas();
    lemmas.for_each([&](hinst_lemma const & lemma) {
            add_em_fact(S, ctx, lemma);
        });
    return set_dcs(ts, dcs);
}

vm_obj mk_smt_state(tactic_state s, smt_config const & cfg) {
    if (!s.goals()) return mk_no_goals_exception(s);
    unsigned num_reverted;
    /* Remark: revert_all only reverts declarations after the last local instance.

       It is not reliable to implement "revert/do something/intro" idiom using `num_reverted`.
       The problem is that the `do something` step may eliminate `let`-decls.
       We have to figure out a way to do it more reliably.
    */
    std::tie(s, num_reverted) = revert_all(clear_recs(s));
    smt_goal new_goal(cfg);

    vm_obj r = preprocess(s, cfg.m_pre_config);
    if (tactic::is_result_exception(r)) return r;
    s = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = s.mctx();
    bool use_unused_names = true;
    defeq_can_state dcs = s.dcs();
    list<name> ids;
    expr new_M = intros(s.env(), s.get_options(), mctx, head(s.goals()), dcs, new_goal, use_unused_names,
                        optional<unsigned>(num_reverted), ids);

    s = set_mctx_goals_dcs(s, mctx, cons(new_M, tail(s.goals())), dcs);
    s = add_em_facts(s, new_goal);

    return tactic::mk_success(mk_vm_cons(to_obj(new_goal), mk_vm_nil()), s);
}

/* TODO(Leo): for hinst_lemma sets, the attribute name and declaration name should be the same. */

static hinst_lemmas get_hinst_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj r      = user_attribute_get_cache(S, s, attr_name);
    if (tactic::is_result_exception(r))
        throw exception(sstream() << "failed to initialize smt_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = tactic::get_success_value(r);
    if (!is_hinst_lemmas(lemmas))
        throw exception(sstream() << "failed to initialize smt_state, attribute '" << attr_name << "' is not a hinst_lemmas");
    return to_hinst_lemmas(lemmas);
}

static simp_lemmas get_simp_lemmas(name const & attr_name, tactic_state const & s) {
    auto & S      = get_vm_state();
    vm_obj r      = user_attribute_get_cache(S, s, mk_simp_attr_decl_name(attr_name));
    if (tactic::is_result_exception(r))
        throw exception(sstream() << "failed to initialize smt_state, failed to retrieve attribute '" << attr_name << "'");
    vm_obj lemmas = tactic::get_success_value(r);
    if (!is_simp_lemmas(lemmas))
        throw exception(sstream() << "failed to initialize smt_state, attribute '" << attr_name << "' is not a simp_lemmas");
    return to_simp_lemmas(lemmas);
}

/*
structure smt_pre_config :=
(simp_attr : name)
(max_steps : nat)
(zeta      : bool)
*/
static smt_pre_config to_smt_pre_config(vm_obj const & cfg, tactic_state const & s) {
    smt_pre_config r;
    r.m_simp_attr     = to_name(cfield(cfg, 0));
    r.m_simp_lemmas   = get_simp_lemmas(r.m_simp_attr, s);
    r.m_max_steps     = force_to_unsigned(cfield(cfg, 1));
    r.m_zeta          = to_bool(cfield(cfg, 2));
    return r;
}

/*
structure smt_config :=
(cc_cfg        : cc_config)
(em_cfg        : ematch_config)
(pre_cfg       : smt_pre_config)
(em_attr       : name)
*/
static smt_config to_smt_config(vm_obj const & cfg, tactic_state const & s) {
    smt_config r;
    std::tie(r.m_ho_fns, r.m_cc_config) = to_ho_fns_cc_config(cfield(cfg, 0));
    r.m_em_config                       = to_ematch_config(cfield(cfg, 1));
    r.m_pre_config                      = to_smt_pre_config(cfield(cfg, 2), s);
    r.m_em_attr                         = to_name(cfield(cfg, 3));
    r.m_em_lemmas                       = get_hinst_lemmas(r.m_em_attr, s);
    return r;
}

vm_obj smt_state_mk(vm_obj const & cfg, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return mk_smt_state(tactic::to_state(s), to_smt_config(cfg, tactic::to_state(s)));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

bool same_hyps(metavar_context const & mctx, expr const & mvar1, expr const & mvar2) {
    lean_assert(is_metavar(mvar1));
    lean_assert(is_metavar(mvar2));
    optional<metavar_decl> d1 = mctx.find_metavar_decl(mvar1);
    optional<metavar_decl> d2 = mctx.find_metavar_decl(mvar2);
    return d1 && d2 && equal_locals(d1->get_context(), d2->get_context());
}

vm_obj tactic_to_smt_tactic(vm_obj const &, vm_obj const & tac, vm_obj const & ss, vm_obj const & ts) {
    vm_obj r1 = invoke(tac, ts);
    if (tactic::is_result_exception(r1)) {
        /* Tactic failed */
        return r1;
    }
    if (is_nil(ss)) {
        /* There is no SMT state associated with any goal. */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    /* We only handle the common cases:
       1) goals is of the form (a_1, a_2, ..., a_m)
       2) new_goals is of the form (new_1, ... new_n, a_2, ..., a_m)
       3) the sets of hypotheses in new_1 ... new_n are equal to the
          set of hypotheses of a_1

       In this case, given a ss of the form

          (s_1, ..., s_k)

       where k <= m, we obtain a new valid ss

          (s_1, ..., s_1, s_2, ..., s_k)
           n copies of s_1
    */
    vm_obj new_ts = tactic::get_success_state(r1);
    if (is_eqp(tactic::to_state(ts), tactic::to_state(new_ts))) {
        /* The tactic_state was not modified */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    list<expr> goals          = tactic::to_state(ts).goals();
    list<expr> new_goals      = tactic::to_state(new_ts).goals();
    if (goals == new_goals) {
        /* Set of goals did not change. */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    if (!new_goals) {
        /* There are no new goals */
        return tactic_success_to_smt_tactic_success(r1, mk_vm_nil());
    }
    if (!goals) {
        return tactic::mk_exception("failed to lift tactic to smt_tactic, there were no goals to be solved", tactic::to_state(ts));
    }
    if (new_goals == tail(goals)) {
        /* Main goal was solved */
        /* remove one SMT goal */
        vm_obj new_ss = tail(ss);
        return tactic_success_to_smt_tactic_success(r1, new_ss);
    }
    metavar_context const & mctx = tactic::to_state(new_ts).mctx();
    if (tail(new_goals) == tail(goals) && same_hyps(mctx, head(new_goals), head(goals))) {
        /* The set of hypotheses in the main goal did not change */
        return tactic_success_to_smt_tactic_success(r1, ss);
    }
    vm_obj new_ss = ss;
    while (true) {
        if (!same_hyps(mctx, head(new_goals), head(goals))) {
            return tactic::mk_exception("failed to lift tactic to smt_tactic, set of hypotheses has been modified, at least one of the used tactics has to be lifted manually",
                                       tactic::to_state(ts));
        }
        if (tail(new_goals) == tail(goals)) {
            return tactic_success_to_smt_tactic_success(r1, new_ss);
        }
        /* copy smt state */
        new_ss = mk_vm_cons(head(new_ss), new_ss);

        /* Move to next */
        new_goals = tail(new_goals);
        if (!new_goals) {
            return tactic::mk_exception("failed to lift tactic to smt_tactic, only tactics that modify a prefix of the list of goals can be automatically lifted",
                                       tactic::to_state(ts));
        }
    }
}

static bool ignore_pp_fact(expr const & e) {
    return
        is_arrow(e) ||
        is_true(e) ||
        is_false(e) ||
        is_or(e) ||
        is_and(e) ||
        is_not(e) ||
        is_iff(e) ||
        is_ite(e);
}

static optional<format> pp_facts(cc_state const & ccs, expr const & root, formatter const & fmt) {
    optional<format> r;
    expr it = root;
    do {
        if (!ignore_pp_fact(it)) {
            format fmt_it = fmt(it);
            if (is_pi(it) || is_lambda(it) || is_let(it))
                fmt_it = paren(fmt_it);
            if (r)
                r = *r + comma() + line() + fmt_it;
            else
                r = fmt_it;
        }
        it = ccs.get_next(it);
    } while (it != root);
    return r;
}

static format pp_positive_facts(cc_state const & ccs, formatter const & fmt) {
    if (auto r = pp_facts(ccs, mk_true(), fmt))
        return group(format("facts:") + line() + bracket("{", *r, "}")) + line();
    else
        return format();
}

static format pp_negative_facts(cc_state const & ccs, formatter const & fmt) {
    if (auto r = pp_facts(ccs, mk_false(), fmt))
        return group(format("refuted facts:") + line() + bracket("{", *r, "}")) + line();
    else
        return format();
}

static format pp_equivalences(type_context_old & ctx, cc_state const & ccs, formatter const & fmt) {
    format r;
    bool first = true;
    buffer<expr> roots;
    ccs.get_roots(roots);
    for (expr const & root : roots) {
        if (root == mk_true() || root == mk_false()) continue;
        if (ctx.is_proof(root)) continue;
        if (first) first = false; else r += comma() + line();
        r += ccs.pp_eqc(fmt, root);
    }
    if (!first) {
        return group(format("equalities:") + line() + bracket("{", r, "}")) + line();
    } else {
        return format();
    }
}

format smt_goal_to_format(smt_goal sg, tactic_state const & ts) {
    lean_assert(ts.goals());
    options opts               = ts.get_options().update_if_undef(get_pp_purify_locals_name(), false);
    bool inst_mvars            = get_pp_instantiate_mvars(opts);
    bool unicode               = get_pp_unicode(opts);
    unsigned indent            = get_pp_indent(opts);
    metavar_decl decl          = *ts.get_main_goal_decl();
    local_context lctx         = decl.get_context();
    metavar_context mctx_tmp   = ts.mctx();
    expr target                = decl.get_type();
    if (inst_mvars)
        target                 = mctx_tmp.instantiate_mvars(target);
    format turnstile(unicode ? "⊢" : "|-");
    type_context_old ctx(ts.env(), opts, mctx_tmp, lctx, transparency_mode::All);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt              = fmtf(ts.env(), opts, ctx);
    defeq_can_state dcs        = ts.dcs();
    smt S(ctx, dcs, sg);
    format r;
    if (S.inconsistent()) {
        r  = format("contradictory goal, use 'smt_tactic.close' to close this goal");
        r += line();
    } else {
        if (inst_mvars)
            lctx                   = lctx.instantiate_mvars(mctx_tmp);
        /* TODO(Leo): add support for hidding hypotheses */
        r                          = lctx.pp(fmt, [&](local_decl const &) { return true; });
        if (!lctx.empty())
            r += line();
        cc_state ccs               = sg.get_cc_state();
        r += pp_positive_facts(ccs, fmt);
        r += pp_negative_facts(ccs, fmt);
        r += pp_equivalences(ctx, ccs, fmt);
    }
    r += turnstile + space() + nest(indent, fmt(target));
    return r;
}

format smt_state_to_format_core(vm_obj const & ss, tactic_state const & ts) {
    if (!ts.goals()) return format("no goals");
    if (is_nil(ss))  return ts.pp(); /* fallback */
    format r;
    r = smt_goal_to_format(to_smt_goal(head(ss)), ts);

    /* Pretty print type of remaining goals
       TODO(Leo): move this code to a different place */
    metavar_context mctx = ts.mctx();
    bool unicode         = get_pp_unicode(ts.get_options());
    format turnstile(unicode ? "⊢" : "|-");
    for (expr const & g : tail(ts.goals())) {
        metavar_decl d = mctx.get_metavar_decl(g);
        type_context_old ctx(ts.env(), ts.get_options(), mctx, d.get_context(), transparency_mode::Semireducible);
        formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
        formatter fmt                  = fmtf(ts.env(), ts.get_options(), ctx);
        r += line() + line() + turnstile + space() + nest(3, fmt(d.get_type()));
    }
    return r;
}

format smt_state_pp(vm_obj const & ss, tactic_state const & ts) {
    return smt_state_to_format_core(ss, ts);
}

vm_obj smt_state_to_format(vm_obj const & ss, vm_obj const & ts) {
    LEAN_TACTIC_TRY;
    return to_obj(smt_state_to_format_core(ss, tactic::to_state(ts)));
    LEAN_TACTIC_CATCH(tactic::to_state(ts));
}

vm_obj mk_smt_state_empty_exception(tactic_state const & ts) {
    return tactic::mk_exception("tactic failed, smt_state is empty", ts);
}

vm_obj mk_smt_state_empty_exception(vm_obj const & ts) {
    lean_assert(tactic::is_state(ts));
    return mk_smt_state_empty_exception(tactic::to_state(ts));
}

vm_obj exact_core(expr const & e, vm_obj const & ss, tactic_state const & ts) {
    lean_assert(!is_nil(ss));
    lean_assert(ts.goals());
    vm_obj new_ss = tail(ss);
    auto mctx = ts.mctx();
    mctx.assign(head(ts.goals()), e);
    tactic_state new_ts = set_mctx_goals(ts, mctx, tail(ts.goals()));
    return mk_smt_tactic_success(new_ss, to_obj(new_ts));
}

vm_obj smt_tactic_close(vm_obj const & ss, vm_obj const & _ts) {
    tactic_state const & ts = tactic::to_state(_ts);
    LEAN_TACTIC_TRY;
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    smt_goal g          = to_smt_goal(head(ss));
    defeq_can_state dcs = ts.dcs();
    smt S(ctx, dcs, g);
    if (S.inconsistent()) {
        if (auto pr = S.get_inconsistency_proof()) {
            expr H      = mk_false_rec(ctx, target, *pr);
            return exact_core(H, ss, ts);
        }
    }

    S.internalize(target);
    expr lhs, rhs;
    if (is_eq(target, lhs, rhs)) {
        if (auto pr = S.get_eq_proof(lhs, rhs)) {
            return exact_core(*pr, ss, ts);
        }
    }

    if (auto pr = S.get_proof(target)) {
        return exact_core(*pr, ss, ts);
    }
    LEAN_TACTIC_CATCH(ts);
    return tactic::mk_exception("smt_tactic.close failed", ts);
}

vm_obj smt_tactic_intros_core(list<name> const & ids, optional<unsigned> const & num, vm_obj const & ss, tactic_state ts) {
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    LEAN_TACTIC_TRY;

    smt_goal new_sgoal   = to_smt_goal(head(ss));

    vm_obj r = preprocess(ts, new_sgoal.get_pre_config());
    if (tactic::is_result_exception(r)) return r;
    ts = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = ts.mctx();
    defeq_can_state dcs  = ts.dcs();
    expr new_mvar = intros(ts.env(), ts.get_options(), mctx, head(ts.goals()),
                           dcs, new_sgoal, true, num, ids);

    tactic_state new_ts = set_mctx_goals_dcs(ts, mctx, cons(new_mvar, tail(ts.goals())), dcs);
    vm_obj new_ss       = mk_vm_cons(to_obj(new_sgoal), tail(ss));
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_intros(vm_obj const & ss, vm_obj const & ts) {
    return smt_tactic_intros_core(list<name>(), optional<unsigned>(), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intron(vm_obj const & n, vm_obj const & ss, vm_obj const & ts) {
    return smt_tactic_intros_core(list<name>(), optional<unsigned>(force_to_unsigned(n)), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intro_lst(vm_obj const & _ids, vm_obj const & ss, vm_obj const & ts) {
    list<name> const & ids = to_list_name(_ids);
    return smt_tactic_intros_core(list<name>(ids), optional<unsigned>(length(ids)), ss, tactic::to_state(ts));
}

vm_obj smt_tactic_intros_core(vm_obj const & _ids, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss))
        return mk_smt_state_empty_exception(ts);
    LEAN_TACTIC_TRY;

    smt_goal new_sgoal   = to_smt_goal(head(ss));

    vm_obj r = preprocess(ts, new_sgoal.get_pre_config());
    if (tactic::is_result_exception(r)) return r;
    ts = tactic::to_state(tactic::get_success_state(r));

    metavar_context mctx = ts.mctx();
    defeq_can_state dcs  = ts.dcs();
    list<name> ids       = to_list_name(_ids);
    optional<unsigned> n;
    if (ids) n = length(ids);
    expr new_mvar = intros(ts.env(), ts.get_options(), mctx, head(ts.goals()),
                           dcs, new_sgoal, true, n, ids);

    tactic_state new_ts = set_mctx_goals_dcs(ts, mctx, cons(new_mvar, tail(ts.goals())), dcs);
    vm_obj new_ss       = mk_vm_cons(to_obj(new_sgoal), tail(ss));
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_state_classical(vm_obj const & ss) {
    bool r = false;
    if (!is_nil(ss)) {
        smt_goal const & g = to_smt_goal(head(ss));
        r = g.get_cc_state().get_config().m_em;
    }
    return mk_vm_bool(r);
}

vm_obj smt_tactic_ematch_core(vm_obj const & pred, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    S.internalize(target);
    buffer<new_instance> new_instances;
    S.ematch(new_instances);
    if (new_instances.empty())
        return tactic::mk_exception("ematch failed, no new instance was produced", ts);
    for (new_instance const & p : new_instances) {
        expr type   = p.m_instance;
        expr proof  = p.m_proof;
        vm_obj keep = invoke(pred, to_obj(type));
        if (to_bool(keep)) {
            std::tie(type, proof) = preprocess_forward(ctx, dcs, g, type, proof);
            lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                       tout() << "instance, generation: " << p.m_generation << ", after preprocessing\n"
                       << type << "\n";);
            S.add(type, proof, p.m_generation);
        }
    }
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_mk_ematch_eqn_lemmas_for_core(vm_obj const & md, vm_obj const & decl_name, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(ts);
    buffer<name> eqns;
    get_ext_eqn_lemmas_for(ts.env(), to_name(decl_name), eqns);
    if (eqns.empty())
        return tactic::mk_exception(sstream() << "tactic failed, '" << to_name(decl_name) << "' does not have equation lemmas", ts);
    hinst_lemmas hs;
    for (name const & eqn : eqns) {
        declaration eqn_decl = ctx.env().get(eqn);
        hinst_lemma h = mk_hinst_lemma(ctx, to_transparency_mode(md), eqn, true);
        hs.insert(h);
    }
    tactic_state new_ts = set_env_mctx(ts, ctx.env(), ctx.mctx());
    return mk_smt_tactic_success(to_obj(hs), ss, to_obj(new_ts));
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_to_cc_state(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    return mk_smt_tactic_success(to_obj(to_smt_goal(head(ss)).get_cc_state()), ss, ts);
}

vm_obj smt_tactic_to_em_state(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    return mk_smt_tactic_success(to_obj(to_smt_goal(head(ss)).get_em_state()), ss, ts);
}

vm_obj smt_tactic_preprocess(vm_obj const & e, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    type_context_old ctx    = mk_type_context_for(ts);
    smt_goal g          = to_smt_goal(head(ss));
    defeq_can_state dcs = ts.dcs();
    simp_result r       = preprocess(ctx, dcs, g.get_pre_config(), to_expr(e));
    r                   = finalize(ctx, get_eq_name(), r);
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(mk_vm_pair(to_obj(r.get_new()), to_obj(r.get_proof())), ss, to_obj(new_ts));
    LEAN_TACTIC_CATCH(ts);
}

vm_obj smt_tactic_get_lemmas(vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g      = to_smt_goal(head(ss));
    hinst_lemmas s  = g.get_em_state().get_lemmas();
    s.merge(g.get_em_state().get_new_lemmas());
    vm_obj r        = to_obj(s);
    return mk_smt_tactic_success(r, ss, _ts);
}

vm_obj smt_tactic_set_lemmas(vm_obj const & lemmas, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts     = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g          = to_smt_goal(head(ss));
    g.set_lemmas(to_hinst_lemmas(lemmas));
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    return mk_smt_tactic_success(new_ss, _ts);
}

vm_obj smt_tactic_add_lemmas(vm_obj const & lemmas, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts     = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    to_hinst_lemmas(lemmas).for_each([&](hinst_lemma const & lemma) {
            bool is_fact = add_em_fact(S, ctx, lemma);
            if (!is_fact) {
                lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                           tout() << "new equation lemma " << lemma << "\n" << lemma.m_prop << "\n";);
                g.add_lemma(lemma);
            }
        });
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
}

vm_obj smt_tactic_ematch_using(vm_obj const & hs, vm_obj const & ss, vm_obj const & _ts) {
    tactic_state ts = tactic::to_state(_ts);
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    lean_assert(ts.goals());
    LEAN_TACTIC_TRY;
    expr target         = ts.get_main_goal_decl()->get_type();
    type_context_old ctx    = mk_type_context_for(ts);
    defeq_can_state dcs = ts.dcs();
    smt_goal g          = to_smt_goal(head(ss));
    smt S(ctx, dcs, g);
    S.internalize(target);
    bool added_facts = false;
    buffer<new_instance> new_instances;
    to_hinst_lemmas(hs).for_each([&](hinst_lemma const & lemma) {
            if (add_em_fact(S, ctx, lemma)) {
                added_facts = true;
            } else {
                S.ematch_using(lemma, new_instances);
            }
        });
    if (!added_facts && new_instances.empty())
        return tactic::mk_exception("ematch_using failed, no instance was produced", ts);
    for (new_instance const & p : new_instances) {
        expr type   = p.m_instance;
        expr proof  = p.m_proof;
        std::tie(type, proof) = preprocess_forward(ctx, dcs, g, type, proof);
        lean_trace(name({"smt", "ematch"}), scope_trace_env _(ctx.env(), ctx);
                   tout() << "instance, generation: " << p.m_generation
                   << ", after preprocessing\n" << type << "\n";);
        S.add(type, proof, p.m_generation);
    }
    vm_obj new_ss       = mk_vm_cons(to_obj(g), tail(ss));
    tactic_state new_ts = set_mctx_dcs(ts, ctx.mctx(), dcs);
    return mk_smt_tactic_success(new_ss, new_ts);
    LEAN_TACTIC_CATCH(ts);
}

/*
structure smt_pre_config :=
(simp_attr : name := `pre_smt)
(max_steps : nat  := 1000000)
(zeta      : bool := ff)

structure smt_config :=
(cc_cfg        : cc_config      := {})
(em_cfg        : ematch_config  := {})
(pre_cfg       : smt_pre_config := {})
(em_attr       : name           := `ematch)
*/
vm_obj smt_tactic_get_config(vm_obj const & ss, vm_obj const & ts) {
    if (is_nil(ss)) return mk_smt_state_empty_exception(ts);
    smt_goal g = to_smt_goal(head(ss));
    smt_config const & cfg = g.get_config();
    smt_pre_config const & pre = g.get_pre_config();

    vm_obj cc_cfg  = g.get_cc_state().mk_vm_cc_config();
    vm_obj em_cfg  = g.get_em_state().mk_vm_ematch_config();
    vm_obj pre_cfg = mk_vm_constructor(0, to_obj(pre.m_simp_attr), mk_vm_nat(pre.m_max_steps), mk_vm_bool(pre.m_zeta));
    vm_obj em_attr = to_obj(cfg.m_em_attr);

    vm_obj r = mk_vm_constructor(0, cc_cfg, em_cfg, pre_cfg, em_attr);

    return mk_smt_tactic_success(r, ss, ts);
}

void initialize_smt_state() {
    register_trace_class("smt");
    register_trace_class(name({"smt", "fact"}));
    register_trace_class(name({"smt", "intro"}));
    register_trace_class(name({"smt", "ematch"}));

    DECLARE_VM_BUILTIN(name({"smt_state", "mk"}),                                smt_state_mk);
    DECLARE_VM_BUILTIN(name({"smt_state", "to_format"}),                         smt_state_to_format);
    DECLARE_VM_BUILTIN(name({"smt_state", "classical"}),                         smt_state_classical);
    DECLARE_VM_BUILTIN("tactic_to_smt_tactic",                                   tactic_to_smt_tactic);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "close"}),                            smt_tactic_close);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intros"}),                           smt_tactic_intros);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intron"}),                           smt_tactic_intron);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "intro_lst"}),                        smt_tactic_intro_lst);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "ematch_core"}),                      smt_tactic_ematch_core);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "ematch_using"}),                     smt_tactic_ematch_using);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "to_cc_state"}),                      smt_tactic_to_cc_state);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "to_em_state"}),                      smt_tactic_to_em_state);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "get_config"}),                       smt_tactic_get_config);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "preprocess"}),                       smt_tactic_preprocess);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "get_lemmas"}),                       smt_tactic_get_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "set_lemmas"}),                       smt_tactic_set_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "add_lemmas"}),                       smt_tactic_add_lemmas);
    DECLARE_VM_BUILTIN(name({"smt_tactic", "mk_ematch_eqn_lemmas_for_core"}),    smt_tactic_mk_ematch_eqn_lemmas_for_core);
}

void finalize_smt_state() {
}
}




// ========== congruence_closure.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/type_context.h"
#include "library/congr_lemma.h"
#include "library/relation_manager.h"
#include "library/defeq_canonizer.h"
#include "library/vm/vm.h"
#include "library/tactic/simp_result.h"
#include "library/tactic/smt/theory_ac.h"

namespace lean {
struct ext_congr_lemma;

struct ext_congr_lemma_cache;
typedef std::shared_ptr<ext_congr_lemma_cache> ext_congr_lemma_cache_ptr;

class cc_propagation_handler {
public:
    virtual ~cc_propagation_handler() {}
    virtual void propagated(unsigned n, expr const * data) = 0;
    void propagated(buffer<expr> const & p) { propagated(p.size(), p.data()); }
    /* Congruence closure module invokes the following method when
       a new auxiliary term is created during propagation. */
    virtual void new_aux_cc_term(expr const & e) = 0;
};

/* The congruence_closure module (optionally) uses a normalizer.
   The idea is to use it (if available) to normalize auxiliary expressions
   produced by internal propagation rules (e.g., subsingleton propagator). */
class cc_normalizer {
public:
    virtual ~cc_normalizer() {}
    virtual expr normalize(expr const & e) = 0;
};

class congruence_closure {
    /* Equivalence class data associated with an expression 'e' */
    struct entry {
        expr           m_next;       // next element in the equivalence class.
        expr           m_root;       // root (aka canonical) representative of the equivalence class.
        expr           m_cg_root;    // root of the congruence class, it is meaningless if 'e' is not an application.
        /* When 'e' was added to this equivalence class because of an equality (H : e = target), then we
           store 'target' at 'm_target', and 'H' at 'm_proof'. Both fields are none if 'e' == m_root */
        optional<expr> m_target;
        optional<expr> m_proof;
        /* Variable in the AC theory. */
        optional<expr> m_ac_var;
        unsigned       m_flipped:1;      // proof has been flipped
        unsigned       m_interpreted:1;  // true if the node should be viewed as an abstract value
        unsigned       m_constructor:1;  // true if head symbol is a constructor
        unsigned       m_has_lambdas:1;  // true if equivalence class contains lambda expressions
        /* m_heq_proofs == true iff some proofs in the equivalence class are based on heterogeneous equality.
           We represent equality and heterogeneous equality in a single equivalence class. */
        unsigned       m_heq_proofs:1;
        /* If m_fo == true, then the expression associated with this entry is an application, and
           we are using first-order approximation to encode it. That is, we ignore its partial applications. */
        unsigned       m_fo:1;
        unsigned       m_size;           // number of elements in the equivalence class, it is meaningless if 'e' != m_root
        /* The field m_mt is used to implement the mod-time optimization introduce by the Simplify theorem prover.
           The basic idea is to introduce a counter gmt that records the number of heuristic instantiation that have
           occurred in the current branch. It is incremented after each round of heuristic instantiation.
           The field m_mt records the last time any proper descendant of of thie entry was involved in a merge. */
        unsigned       m_mt;
        unsigned       m_generation;
    };

    struct parent_occ {
        expr m_expr;
        /* If m_symm_table is true, then we should use the m_symm_congruences, otherwise m_congruences.
           Remark: this information is redundant, it can be inferred from m_expr. We use store it for
           performance reasons. */
        bool m_symm_table;
        parent_occ() {}
        parent_occ(expr const & e, bool symm_table):m_expr(e), m_symm_table(symm_table) {}
    };

    struct parent_occ_cmp {
        int operator()(parent_occ const & k1, parent_occ const & k2) const {
            return expr_quick_cmp()(k1.m_expr, k2.m_expr);
        }
    };

    typedef rb_expr_map<entry>                           entries;
    typedef rb_tree<parent_occ, parent_occ_cmp>          parent_occ_set;
    typedef rb_expr_map<parent_occ_set>                  parents;
    typedef unsigned_map<list<expr>>                     congruences;
    typedef unsigned_map<list<pair<expr, name>>>         symm_congruences;
    typedef rb_expr_map<expr>                            subsingleton_reprs;
    typedef std::tuple<expr, expr, expr, bool>           todo_entry;

public:
    struct config {
        unsigned m_ignore_instances:1;
        unsigned m_values:1;
        unsigned m_all_ho:1;
        unsigned m_ac:1;
        unsigned m_em:1;
        config() { m_ignore_instances = true; m_values = true; m_all_ho = false; m_ac = true; m_em = true; }
    };

    class state {
        entries            m_entries;
        parents            m_parents;
        congruences        m_congruences;
        symm_congruences   m_symm_congruences;
        /** The following mapping store a representative for each subsingleton type */
        subsingleton_reprs m_subsingleton_reprs;
        /** The congruence closure module has a mode where the root of
            each equivalence class is marked as an interpreted/abstract
            value. Moreover, in this mode proof production is disabled.
            This capability is useful for heuristic instantiation. */
        short              m_froze_partitions{false};
        short              m_inconsistent{false};
        unsigned           m_gmt{0};
        /** Only for constant functions in m_ho_fns, we add the extra occurrences discussed in
            the paper "Congruence Closure in Intensional Type Theory". The idea is to avoid
            the quadratic number of entries in the parent occurrences data-structures,
            and avoid the creation of entries for partial applications. For example, given
            (@add nat nat_has_add a b), it seems wasteful to create entries for
            (@add nat), (@add nat nat_has_add) and (@nat nat_has_add a).
            This set is ignore if m_config.m_all_ho is true. */
        name_set           m_ho_fns;
        /* We are planning to have very few theories in this module. So, we don't
           use any abstract theory state object. */
        theory_ac::state   m_ac_state;
        config             m_config;
        friend class congruence_closure;
        bool check_eqc(expr const & e) const;
        void mk_entry_core(expr const & e, bool interpreted, bool constructor, unsigned gen);
    public:
        state(name_set const & ho_fns = name_set(), config const & cfg = config());
        void get_roots(buffer<expr> & roots, bool nonsingleton_only = true) const;
        expr get_root(expr const & e) const;
        expr get_next(expr const & e) const;
        unsigned get_mt(expr const & e) const;
        bool is_congr_root(expr const & e) const;
        bool check_invariant() const;
        bool inconsistent() const { return m_inconsistent; }
        bool in_singleton_eqc(expr const & e) const;
        bool in_heterogeneous_eqc(expr const & e) const;
        format pp_eqc(formatter const & fmt, expr const & e) const;
        format pp_eqcs(formatter const & fmt, bool nonsingleton_only = true) const;
        format pp_parent_occs(formatter const & fmt, expr const & e) const;
        format pp_parent_occs(formatter const & fmt) const;
        unsigned get_gmt() const { return m_gmt; }
        void inc_gmt() { m_gmt++; }
        config const & get_config() const { return m_config; }
        vm_obj mk_vm_cc_config() const;
    };

private:
    type_context_old &            m_ctx;
    defeq_canonizer           m_defeq_canonizer;
    state &                   m_state;
    buffer<todo_entry>        m_todo;
    ext_congr_lemma_cache_ptr m_cache_ptr;
    transparency_mode         m_mode;
    relation_info_getter      m_rel_info_getter;
    symm_info_getter          m_symm_info_getter;
    refl_info_getter          m_refl_info_getter;
    theory_ac                 m_ac;
    cc_propagation_handler *  m_phandler;
    cc_normalizer *           m_normalizer;
    friend class theory_ac;

    bool compare_symm(expr lhs1, expr rhs1, expr lhs2, expr rhs2) const;
    bool compare_symm(pair<expr, name> const & k1, pair<expr, name> const & k2) const;
    unsigned mk_symm_hash(expr const & lhs, expr const & rhs) const;
    optional<name> is_binary_relation(expr const & e, expr & lhs, expr & rhs) const;
    optional<name> is_symm_relation(expr const & e, expr & lhs, expr & rhs) const;
    optional<name> is_refl_relation(expr const & e, expr & lhs, expr & rhs) const;
    bool is_symm_relation(expr const & e);
    unsigned mk_congr_hash(expr const & e) const;
    bool is_congruent(expr const & e1, expr const & e2) const;
    void set_fo(expr const & e);
    bool is_value(expr const & e);
    bool is_interpreted_value(expr const & e);
    void process_subsingleton_elem(expr const & e);
    void apply_simple_eqvs(expr const & e);
    void add_occurrence(expr const & parent, expr const & child, bool symm_table);
    void add_congruence_table(expr const & e);
    void check_eq_true(expr const & e);
    void add_symm_congruence_table(expr const & e);
    void mk_entry(expr const & e, bool interpreted, unsigned gen);
    void set_ac_var(expr const & e);
    void internalize_app(expr const & e, unsigned gen);
    void internalize_core(expr const & e, optional<expr> const & parent, unsigned gen);
    void push_todo(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof);
    void push_heq(expr const & lhs, expr const & rhs, expr const & H);
    void push_eq(expr const & lhs, expr const & rhs, expr const & H);
    void push_refl_eq(expr const & lhs, expr const & rhs);
    void invert_trans(expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof);
    void invert_trans(expr const & e);
    void remove_parents(expr const & e, buffer<expr> & parents_to_propagate);
    void reinsert_parents(expr const & e);
    void update_mt(expr const & e);
    bool has_heq_proofs(expr const & root) const;
    expr flip_proof_core(expr const & H, bool flipped, bool heq_proofs) const;
    expr flip_proof(expr const & H, bool flipped, bool heq_proofs) const;
    optional<ext_congr_lemma> mk_ext_hcongr_lemma(expr const & fn, unsigned nargs) const;
    expr mk_trans(expr const & H1, expr const & H2, bool heq_proofs) const;
    expr mk_trans(optional<expr> const & H1, expr const & H2, bool heq_proofs) const;
    expr mk_congr_proof_core(expr const & e1, expr const & e2, bool heq_proofs) const;
    optional<expr> mk_symm_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const;
    expr mk_congr_proof(expr const & lhs, expr const & rhs, bool heq_proofs) const;
    expr mk_proof(expr const & lhs, expr const & rhs, expr const & H, bool heq_proofs) const;
    optional<expr> get_eq_proof_core(expr const & e1, expr const & e2, bool as_heq) const;
    void push_subsingleton_eq(expr const & a, expr const & b);
    void check_new_subsingleton_eq(expr const & old_root, expr const & new_root);
    bool is_eq_true(expr const & e) const;
    bool is_eq_false(expr const & e) const;
    expr get_eq_true_proof(expr const & e) const;
    expr get_eq_false_proof(expr const & e) const;
    expr get_prop_eq_proof(expr const & a, expr const & b) const;
    static bool may_propagate(expr const & e);
    void propagate_iff_up(expr const & e);
    void propagate_and_up(expr const & e);
    void propagate_or_up(expr const & e);
    void propagate_not_up(expr const & e);
    void propagate_imp_up(expr const & e);
    void propagate_ite_up(expr const & e);
    optional<expr> mk_ne_of_eq_of_ne(expr const & a, expr const & a1, expr const & a1_ne_b);
    optional<expr> mk_ne_of_ne_of_eq(expr const & a_ne_b1, expr const & b1, expr const & b);
    void propagate_eq_up(expr const & e);
    void propagate_up(expr const & e);
    void propagate_and_down(expr const & e);
    void propagate_or_down(expr const & e);
    void propagate_not_down(expr const & e);
    void propagate_eq_down(expr const & e);
    expr_pair to_forall_not(expr const & ex, expr const & h_not_ex);
    void propagate_exists_down(expr const & e);
    void propagate_down(expr const & e);
    void propagate_inst_implicit(expr const & e);
    void propagate_constructor_eq(expr const & e1, expr const & e2);
    void propagate_projection_constructor(expr const & p, expr const & c);
    void propagate_value_inconsistency(expr const & e1, expr const & e2);
    void get_eqc_lambdas(expr const & e, buffer<expr> & r);
    void propagate_beta(expr const & fn, buffer<expr> const & rev_args, buffer<expr> const & lambdas, buffer<expr> & r);
    void propagate_beta_to_eqc(buffer<expr> const & fn_roots, buffer<expr> const & lambdas, buffer<expr> & new_lambda_apps);
    void collect_fn_roots(expr const & root, buffer<expr> & fn_roots);
    void add_eqv_step(expr e1, expr e2, expr const & H, bool heq_proof);
    void process_todo();
    void add_eqv_core(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof);
    bool check_eqc(expr const & e) const;
    bool check_congr_keys() const;

    friend ext_congr_lemma_cache_ptr const & get_cache_ptr(congruence_closure const & cc);
public:
    congruence_closure(type_context_old & ctx, state & s, defeq_canonizer::state & dcs,
                       cc_propagation_handler * phandler = nullptr,
                       cc_normalizer * normalizer = nullptr);
    ~congruence_closure();

    environment const & env() const { return m_ctx.env(); }
    type_context_old & ctx() { return m_ctx; }
    transparency_mode mode() const { return m_mode; }
    defeq_canonizer & get_defeq_canonizer() { return m_defeq_canonizer; }

    /** \brief Register expression \c e in this data-structure.
       It creates entries for each sub-expression in \c e.
       It also updates the m_parents mapping.

       We ignore the following subterms of \c e.
       1- and, or and not-applications are not inserted into the data-structures, but
          their arguments are visited.
       2- (Pi (x : A), B), the subterms A and B are not visited if B depends on x.
       3- (A -> B) is not inserted into the data-structures, but their arguments are visited
          if they are propositions.
       4- Terms containing meta-variables.
       5- The subterms of lambda-expressions.
       6- Sorts (Type and Prop). */
    void internalize(expr const & e, unsigned gen);

    void add(expr const & type, expr const & proof, unsigned gen);

    bool is_eqv(expr const & e1, expr const & e2) const;
    bool is_not_eqv(expr const & e1, expr const & e2) const;
    bool proved(expr const & e) const;

    bool is_def_eq(expr const & e1, expr const & e2) const {
        return m_ctx.pure_is_def_eq(e1, e2);
    }

    bool relaxed_is_def_eq(expr const & e1, expr const & e2) const {
        return m_ctx.pure_relaxed_is_def_eq(e1, e2);
    }

    expr get_root(expr const & e) const { return m_state.get_root(e); }
    expr get_next(expr const & e) const { return m_state.get_next(e); }
    bool is_congr_root(expr const & e) const { return m_state.is_congr_root(e); }
    bool in_heterogeneous_eqc(expr const & e) const { return m_state.in_heterogeneous_eqc(e); }

    optional<expr> get_heq_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_eq_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_proof(expr const & e1, expr const & e2) const;
    optional<expr> get_inconsistency_proof() const;
    bool inconsistent() const { return m_state.inconsistent(); }

    unsigned get_gmt() const { return m_state.get_gmt(); }
    unsigned get_mt(expr const & t) const { return m_state.get_mt(t); }
    void inc_gmt() { m_state.inc_gmt(); }

    optional<ext_congr_lemma> mk_ext_congr_lemma(expr const & e) const;

    optional<expr> is_ac(expr const & e) {
        if (m_state.m_config.m_ac) return m_ac.is_ac(e);
        else return none_expr();
    }

    entry const * get_entry(expr const & e) const { return m_state.m_entries.find(e); }
    bool check_invariant() const { return m_state.check_invariant(); }

    expr normalize(expr const & e);

    unsigned get_generation_of(expr const & e) const {
        if (auto it = get_entry(e))
            return it->m_generation;
        else
            return 0;
    }

    class state_scope {
        congruence_closure & m_cc;
        state                m_saved_state;
    public:
        state_scope(congruence_closure & cc):m_cc(cc), m_saved_state(cc.m_state) {}
        ~state_scope() { m_cc.m_state = m_saved_state; }
    };
};

typedef congruence_closure::state  cc_state;
typedef congruence_closure::config cc_config;

struct ext_congr_lemma {
    /* The basic congr_lemma object defined at congr_lemma_manager */
    congr_lemma          m_congr_lemma;
    /* If m_heq_result is true, then lemma is based on heterogeneous equality
       and the conclusion is a heterogeneous equality. */
    unsigned             m_heq_result:1;
    /* If m_heq_lemma is true, then lemma was created using mk_hcongr_lemma. */
    unsigned             m_hcongr_lemma:1;
    ext_congr_lemma(congr_lemma const & H):
        m_congr_lemma(H), m_heq_result(false), m_hcongr_lemma(false) {}
};

void initialize_congruence_closure();
void finalize_congruence_closure();
}




// ========== congruence_closure.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <algorithm>
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/string.h"
#include "library/trace.h"
#include "library/fun_info.h"
#include "library/annotation.h"
#include "library/comp_val.h"
#include "library/app_builder.h"
#include "library/projection.h"
#include "library/constructions/constructor.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_list.h"
#include "library/tactic/smt/util.h"
#include "library/tactic/smt/congruence_closure.h"

namespace lean {
struct ext_congr_lemma_key {
    expr     m_fn;
    unsigned m_nargs;
    unsigned m_hash;
    ext_congr_lemma_key():m_nargs(0), m_hash(0) {}
    ext_congr_lemma_key(expr const & fn, unsigned nargs):
        m_fn(fn), m_nargs(nargs),
        m_hash(hash(fn.hash(), nargs)) {}
};

struct ext_congr_lemma_key_hash_fn {
    unsigned operator()(ext_congr_lemma_key const & k) const { return k.m_hash; }
};

struct ext_congr_lemma_key_eq_fn {
    bool operator()(ext_congr_lemma_key const & k1, ext_congr_lemma_key const & k2) const {
        return k1.m_fn == k2.m_fn && k1.m_nargs == k2.m_nargs;
    }
};

typedef std::unordered_map<ext_congr_lemma_key,
                           optional<ext_congr_lemma>,
                           ext_congr_lemma_key_hash_fn,
                           ext_congr_lemma_key_eq_fn> ext_congr_lemma_cache_data;

struct ext_congr_lemma_cache {
    environment                m_env;
    ext_congr_lemma_cache_data m_cache[LEAN_NUM_TRANSPARENCY_MODES];

    ext_congr_lemma_cache(environment const & env):m_env(env) {
    }
};

typedef std::shared_ptr<ext_congr_lemma_cache> ext_congr_lemma_cache_ptr;

congruence_closure::congruence_closure(type_context_old & ctx, state & s, defeq_canonizer::state & dcs,
                                       cc_propagation_handler * phandler,
                                       cc_normalizer * normalizer):
    m_ctx(ctx), m_defeq_canonizer(ctx, dcs), m_state(s), m_cache_ptr(std::make_shared<ext_congr_lemma_cache>(ctx.env())), m_mode(ctx.mode()),
    m_rel_info_getter(mk_relation_info_getter(ctx.env())),
    m_symm_info_getter(mk_symm_info_getter(ctx.env())),
    m_refl_info_getter(mk_refl_info_getter(ctx.env())),
    m_ac(*this, m_state.m_ac_state),
    m_phandler(phandler),
    m_normalizer(normalizer) {
}

congruence_closure::~congruence_closure() {
}

inline ext_congr_lemma_cache_ptr const & get_cache_ptr(congruence_closure const & cc) {
    return cc.m_cache_ptr;
}

inline ext_congr_lemma_cache_data & get_cache(congruence_closure const & cc) {
    return get_cache_ptr(cc)->m_cache[static_cast<unsigned>(cc.mode())];
}

/* Automatically generated congruence lemma based on heterogeneous equality. */
static optional<ext_congr_lemma> mk_hcongr_lemma_core(type_context_old & ctx, expr const & fn, unsigned nargs) {
    optional<congr_lemma> eq_congr = mk_hcongr(ctx, fn, nargs);
    if (!eq_congr) return optional<ext_congr_lemma>();
    ext_congr_lemma res1(*eq_congr);
    expr type = eq_congr->get_type();
    while (is_pi(type)) type = binding_body(type);
    lean_assert(is_eq(type) || is_heq(type));
    res1.m_hcongr_lemma = true;
    if (is_heq(type))
        res1.m_heq_result = true;
    return optional<ext_congr_lemma>(res1);
}

optional<ext_congr_lemma> congruence_closure::mk_ext_hcongr_lemma(expr const & fn, unsigned nargs) const {
    auto & cache = get_cache(*this);
    ext_congr_lemma_key key1(fn, nargs);
    auto it1 = cache.find(key1);
    if (it1 != cache.end())
        return it1->second;

    if (auto lemma = mk_hcongr_lemma_core(m_ctx, fn, nargs)) {
        /* succeeded */
        cache.insert(mk_pair(key1, lemma));
        return lemma;
    }

    /* cache failure */
    cache.insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

optional<ext_congr_lemma> congruence_closure::mk_ext_congr_lemma(expr const & e) const {
    expr const & fn     = get_app_fn(e);
    unsigned nargs      = get_app_num_args(e);
    auto & cache        = get_cache(*this);

    /* Check if (fn, nargs) is in the cache */
    ext_congr_lemma_key key1(fn, nargs);
    auto it1 = cache.find(key1);
    if (it1 != cache.end())
        return it1->second;

    /* Try automatically generated congruence lemma with support for heterogeneous equality. */
    auto lemma = mk_hcongr_lemma_core(m_ctx, fn, nargs);

    if (lemma) {
        /* succeeded */
        cache.insert(mk_pair(key1, lemma));
        return lemma;
    }

    /* cache failure */
    cache.insert(mk_pair(key1, optional<ext_congr_lemma>()));
    return optional<ext_congr_lemma>();
}

expr congruence_closure::state::get_root(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_root;
    } else {
        return e;
    }
}

void congruence_closure::state::get_roots(buffer<expr> & roots, bool nonsingleton_only) const {
    m_entries.for_each([&](expr const & k, entry const & n) {
            if (k == n.m_root && (!nonsingleton_only || !in_singleton_eqc(k)))
                roots.push_back(k);
        });
}

expr congruence_closure::state::get_next(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_next;
    } else {
        return e;
    }
}

unsigned congruence_closure::state::get_mt(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return n->m_mt;
    } else {
        return m_gmt;
    }
}

bool congruence_closure::state::is_congr_root(expr const & e) const {
    if (auto n = m_entries.find(e)) {
        return e == n->m_cg_root;
    } else {
        return true;
    }
}

bool congruence_closure::state::in_heterogeneous_eqc(expr const & e) const {
    if (auto n = m_entries.find(get_root(e)))
        return n->m_heq_proofs;
    else
        return false;
}

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
(em               : bool)
 */
vm_obj congruence_closure::state::mk_vm_cc_config() const {
    vm_obj ho_fns;
    if (get_config().m_all_ho) {
        ho_fns = mk_vm_none();
    } else {
        buffer<name> fns;
        m_ho_fns.to_buffer(fns);
        ho_fns = mk_vm_some(to_obj(fns));
    }
    vm_obj ignore_instances = mk_vm_bool(get_config().m_ignore_instances);
    vm_obj ac               = mk_vm_bool(get_config().m_ac);
    vm_obj em               = mk_vm_bool(get_config().m_em);
    return mk_vm_constructor(0, ignore_instances, ac, ho_fns, em);
}

/** \brief Return true iff the given function application are congruent

    See paper: Congruence Closure for Intensional Type Theory. */
bool congruence_closure::is_congruent(expr const & e1, expr const & e2) const {
    lean_assert(is_app(e1) && is_app(e2));
    if (get_entry(e1)->m_fo) {
        buffer<expr> args1, args2;
        expr const & f1 = get_app_args(e1, args1);
        expr const & f2 = get_app_args(e2, args2);
        if (args1.size() != args2.size()) return false;
        for (unsigned i = 0; i < args1.size(); i++) {
            if (get_root(args1[i]) != get_root(args2[i]))
                return false;
        }
        if (f1 == f2) return true;
        if (get_root(f1) != get_root(f2)) {
            /* f1 and f2 are not equivalent */
            return false;
        }
        if (is_def_eq(m_ctx.infer(f1), m_ctx.infer(f2))) {
            /* f1 and f2 have the same type, then we can create a congruence proof for e1 == e2 */
            return true;
        }
        return false;
    } else {
        /* Given e1 := f a,  e2 := g b */
        expr f = app_fn(e1);
        expr a = app_arg(e1);
        expr g = app_fn(e2);
        expr b = app_arg(e2);
        if (get_root(a) != get_root(b)) {
            /* a and b are not equivalent */
            return false;
        }
        if (get_root(f) != get_root(g)) {
            /* f and g are not equivalent */
            return false;
        }
        if (is_def_eq(m_ctx.infer(f), m_ctx.infer(g))) {
            /* Case 1: f and g have the same type, then we can create a congruence proof for f a == g b */
            return true;
        }
        if (is_app(f) && is_app(g)) {
            /* Case 2: f and g are congruent */
            return is_congruent(f, g);
        }
        /*
        f and g are not congruent nor they have the same type.
        We can't generate a congruence proof in this case because the following lemma

            hcongr : f1 == f2 -> a1 == a2 -> f1 a1 == f2 a2

        is not provable. Remark: it is also not provable in MLTT, Coq and Agda (even if we assume UIP). */
        return false;
    }
}

/* Auxiliary function for comparing (lhs1 ~ rhs1) and (lhs2 ~ rhs2),
   when ~ is symmetric/commutative.
   It returns true (equal) for (a ~ b) (b ~ a) */
bool congruence_closure::compare_symm(expr lhs1, expr rhs1, expr lhs2, expr rhs2) const {
    lhs1 = get_root(lhs1);
    rhs1 = get_root(rhs1);
    lhs2 = get_root(lhs2);
    rhs2 = get_root(rhs2);
    if (is_lt(lhs1, rhs1, true))
        std::swap(lhs1, rhs1);
    if (is_lt(lhs2, rhs2, true))
        std::swap(lhs2, rhs2);
    return lhs1 == lhs2 && rhs1 == rhs2;
}

bool congruence_closure::compare_symm(pair<expr, name> const & k1, pair<expr, name> const & k2) const {
    if (k1.second != k2.second)
        return false;
    expr const & e1 = k1.first;
    expr const & e2 = k2.first;
    if (k1.second == get_eq_name() || k1.second == get_iff_name()) {
        return compare_symm(app_arg(app_fn(e1)), app_arg(e1), app_arg(app_fn(e2)), app_arg(e2));
    } else {
        expr lhs1, rhs1, lhs2, rhs2;
        is_symm_relation(e1, lhs1, rhs1);
        is_symm_relation(e2, lhs2, rhs2);
        return compare_symm(lhs1, rhs1, lhs2, rhs2);
    }
}

unsigned congruence_closure::mk_symm_hash(expr const & lhs, expr const & rhs) const {
    unsigned h1 = get_root(lhs).hash();
    unsigned h2 = get_root(rhs).hash();
    if (h1 > h2)
        std::swap(h1, h2);
    return (h1 << 16) | (h2 & 0xFFFF);
}

unsigned congruence_closure::mk_congr_hash(expr const & e) const {
    lean_assert(is_app(e));
    unsigned h;
    if (get_entry(e)->m_fo) {
        /* first-order case, where we do not consider all partial applications */
        h = get_root(app_arg(e)).hash();
        expr const * it = &(app_fn(e));
        while (is_app(*it)) {
            h  = hash(h, get_root(app_arg(*it)).hash());
            it = &app_fn(*it);
        }
        h = hash(h, get_root(*it).hash());
    } else {
        expr const & f = app_fn(e);
        expr const & a = app_arg(e);
        h = hash(get_root(f).hash(), get_root(a).hash());
    }
    return h;
}

optional<name> congruence_closure::is_binary_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (!is_app(e)) return optional<name>();
    expr fn = get_app_fn(e);
    if (!is_constant(fn)) return optional<name>();
    if (auto info = m_rel_info_getter(const_name(fn))) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() != info->get_arity()) return optional<name>();
        lhs = args[info->get_lhs_pos()];
        rhs = args[info->get_rhs_pos()];
        return optional<name>(const_name(fn));
    }
    return optional<name>();
}

optional<name> congruence_closure::is_symm_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (is_eq(e, lhs, rhs)) {
        return optional<name>(get_eq_name());
    } else if (is_iff(e, lhs, rhs)) {
        return optional<name>(get_iff_name());
    } else if (auto r = is_binary_relation(e, lhs, rhs)) {
        if (!m_symm_info_getter(const_name(get_app_fn(e)))) return optional<name>();
        return r;
    }
    return optional<name>();
}

optional<name> congruence_closure::is_refl_relation(expr const & e, expr & lhs, expr & rhs) const {
    if (is_eq(e, lhs, rhs)) {
        return optional<name>(get_eq_name());
    } else if (is_iff(e, lhs, rhs)) {
        return optional<name>(get_iff_name());
    } else if (auto r = is_binary_relation(e, lhs, rhs)) {
        if (!m_refl_info_getter(const_name(get_app_fn(e)))) return optional<name>();
        return r;
    }
    return optional<name>();
}

bool congruence_closure::is_symm_relation(expr const & e) {
    expr lhs, rhs;
    return static_cast<bool>(is_symm_relation(e, lhs, rhs));
}

void congruence_closure::push_todo(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof) {
    m_todo.emplace_back(lhs, rhs, H, heq_proof);
}

void congruence_closure::push_heq(expr const & lhs, expr const & rhs, expr const & H) {
    m_todo.emplace_back(lhs, rhs, H, true);
}

void congruence_closure::push_eq(expr const & lhs, expr const & rhs, expr const & H) {
    m_todo.emplace_back(lhs, rhs, H, false);
}

expr congruence_closure::normalize(expr const & e) {
    if (m_normalizer)
        return m_normalizer->normalize(e);
    else
        return e;
}

void congruence_closure::process_subsingleton_elem(expr const & e) {
    expr type = m_ctx.infer(e);
    optional<expr> ss = m_ctx.mk_subsingleton_instance(type);
    if (!ss) return; /* type is not a subsingleton */
    type = normalize(type);
    /* Make sure type has been internalized */
    internalize_core(type, none_expr(), get_generation_of(e));
    /* Try to find representative */
    if (auto it = m_state.m_subsingleton_reprs.find(type)) {
        push_subsingleton_eq(e, *it);
    } else {
        m_state.m_subsingleton_reprs.insert(type, e);
    }
    expr type_root     = get_root(type);
    if (type_root == type)
        return;
    if (auto it2 = m_state.m_subsingleton_reprs.find(type_root)) {
        push_subsingleton_eq(e, *it2);
    } else {
        m_state.m_subsingleton_reprs.insert(type_root, e);
    }
}

/* This method is invoked during internalization and eagerly apply basic equivalences for term \c e
   Examples:
   - If e := cast H e', then it merges the equivalence classes of (cast H e') and e'

   In principle, we could mark theorems such as cast_eq as simplification rules, but this creates
   problems with the builtin support for cast-introduction in the ematching module.

   Eagerly merging the equivalence classes is also more efficient. */
void congruence_closure::apply_simple_eqvs(expr const & e) {
    if (is_app_of(e, get_cast_name(), 4)) {
        /* cast H a == a

           theorem cast_heq : ∀ {A B : Type.{l_1}} (H : A = B) (a : A), @cast.{l_1} A B H a == a
        */
        buffer<expr> args;
        expr const & cast = get_app_args(e, args);
        expr const & a    = args[3];
        expr proof        = mk_app(mk_constant(get_cast_heq_name(), const_levels(cast)), args);
        push_heq(e, a, proof);
    }

    if (is_app_of(e, get_eq_rec_name(), 6)) {
        /* eq.rec p H == p

           theorem eq_rec_heq : ∀ {A : Type.{l_1}} {P : A → Type.{l_2}} {a a' : A} (H : a = a') (p : P a), @eq.rec.{l_2 l_1} A a P p a' H == p
        */
        buffer<expr> args;
        expr const & eq_rec = get_app_args(e, args);
        expr A = args[0]; expr a = args[1]; expr P = args[2]; expr p = args[3];
        expr a_prime = args[4]; expr H = args[5];
        level l_2  = head(const_levels(eq_rec));
        level l_1  = head(tail(const_levels(eq_rec)));
        expr proof = mk_app({mk_constant(get_eq_rec_heq_name(), {l_1, l_2}), A, P, a, a_prime, H, p});
        push_heq(e, p, proof);
    }

    if (is_app_of(e, get_ne_name(), 3)) {
        /* (a ≠ b) = (not (a = b)) */
        expr const & a = app_arg(app_fn(e));
        expr const & b = app_arg(e);
        expr new_e     = mk_not(mk_eq(m_ctx, a, b));
        internalize_core(new_e, none_expr(), get_generation_of(e));
        push_refl_eq(e, new_e);
    }

    if (auto r = m_ctx.reduce_projection(e)) {
        push_refl_eq(e, *r);
    }

    expr const & fn = get_app_fn(e);
    if (is_lambda(fn)) {
        expr reduced_e = head_beta_reduce(e);
        if (m_phandler)
            m_phandler->new_aux_cc_term(reduced_e);
        internalize_core(reduced_e, none_expr(), get_generation_of(e));
        push_refl_eq(e, reduced_e);
    }

    buffer<expr> rev_args;
    auto it = e;
    while (is_app(it)) {
        rev_args.push_back(app_arg(it));
        expr const & fn = app_fn(it);
        expr root_fn  = get_root(fn);
        auto en = get_entry(root_fn);
        if (en && en->m_has_lambdas) {
            buffer<expr> lambdas;
            get_eqc_lambdas(root_fn, lambdas);
            buffer<expr> new_lambda_apps;
            propagate_beta(fn, rev_args, lambdas, new_lambda_apps);
            for (expr const & new_app : new_lambda_apps) {
                internalize_core(new_app, none_expr(), get_generation_of(e));
            }
        }
        it = fn;
    }

    propagate_up(e);
}

void congruence_closure::add_occurrence(expr const & parent, expr const & child, bool symm_table) {
    parent_occ_set ps;
    expr child_root = get_root(child);
    if (auto old_ps = m_state.m_parents.find(child_root))
        ps = *old_ps;
    ps.insert(parent_occ(parent, symm_table));
    m_state.m_parents.insert(child_root, ps);
}

static expr * g_congr_mark   = nullptr; // dummy congruence proof, it is just a placeholder.
static expr * g_eq_true_mark = nullptr; // dummy eq_true proof, it is just a placeholder.
static expr * g_refl_mark    = nullptr; // dummy refl proof, it is just a placeholder.

void congruence_closure::push_refl_eq(expr const & lhs, expr const & rhs) {
    m_todo.emplace_back(lhs, rhs, *g_refl_mark, false);
}

void congruence_closure::add_congruence_table(expr const & e) {
    lean_assert(is_app(e));
    unsigned h = mk_congr_hash(e);
    if (list<expr> const * es = m_state.m_congruences.find(h)) {
        for (expr const & old_e : *es) {
            if (is_congruent(e, old_e)) {
                /*
                  Found new equivalence: e ~ old_e
                  1. Update m_cg_root field for e
                */
                entry new_entry     = *get_entry(e);
                new_entry.m_cg_root = old_e;
                m_state.m_entries.insert(e, new_entry);
                /* 2. Put new equivalence in the todo queue */
                /* TODO(Leo): check if the following line is a bottleneck */
                bool heq_proof = !is_def_eq(m_ctx.infer(e), m_ctx.infer(old_e));
                push_todo(e, old_e, *g_congr_mark, heq_proof);
                return;
            }
        }
        m_state.m_congruences.insert(h, cons(e, *es));
    } else {
        m_state.m_congruences.insert(h, to_list(e));
    }
}

void congruence_closure::check_eq_true(expr const & e) {
    expr lhs, rhs;
    if (!is_refl_relation(e, lhs, rhs))
        return;
    if (is_eqv(e, mk_true()))
        return; // it is already equivalent to true
    lhs = get_root(lhs);
    rhs = get_root(rhs);
    if (lhs != rhs) return;
    // Add e = true
    push_eq(e, mk_true(), *g_eq_true_mark);
}

void congruence_closure::add_symm_congruence_table(expr const & e) {
    lean_assert(is_symm_relation(e));
    expr lhs, rhs;
    auto rel = is_symm_relation(e, lhs, rhs);
    lean_assert(rel);
    unsigned h = mk_symm_hash(lhs, rhs);
    pair<expr, name> new_p(e, *rel);
    if (list<pair<expr, name>> const * ps = m_state.m_symm_congruences.find(h)) {
        for (pair<expr, name> const & p : *ps) {
            if (compare_symm(new_p, p)) {
                /*
                  Found new equivalence: e ~ p.first
                  1. Update m_cg_root field for e
                */
                entry new_entry     = *get_entry(e);
                new_entry.m_cg_root = p.first;
                m_state.m_entries.insert(e, new_entry);
                /* 2. Put new equivalence in the TODO queue */
                push_eq(e, p.first, *g_congr_mark);
                check_eq_true(e);
                return;
            }
        }
        m_state.m_symm_congruences.insert(h, cons(new_p, *ps));
        check_eq_true(e);
    } else {
        m_state.m_symm_congruences.insert(h, to_list(new_p));
        check_eq_true(e);
    }
}

congruence_closure::state::state(name_set const & ho_fns, config const & cfg):
    m_ho_fns(ho_fns), m_config(cfg) {
    bool interpreted = true;
    bool constructor = false;
    unsigned gen     = 0;
    mk_entry_core(mk_true(), interpreted, constructor, gen);
    mk_entry_core(mk_false(), interpreted, constructor, gen);
}

void congruence_closure::state::mk_entry_core(expr const & e, bool interpreted, bool constructor, unsigned gen) {
    lean_assert(m_entries.find(e) == nullptr);
    entry n;
    n.m_next         = e;
    n.m_root         = e;
    n.m_cg_root      = e;
    n.m_size         = 1;
    n.m_flipped      = false;
    n.m_interpreted  = interpreted;
    n.m_constructor  = constructor;
    n.m_has_lambdas  = is_lambda(e);
    n.m_heq_proofs   = false;
    n.m_mt           = m_gmt;
    n.m_fo           = false;
    n.m_generation   = gen;
    m_entries.insert(e, n);
}

void congruence_closure::mk_entry(expr const & e, bool interpreted, unsigned gen) {
    if (get_entry(e)) return;
    bool constructor = static_cast<bool>(is_constructor_app(env(), e));
    m_state.mk_entry_core(e, interpreted, constructor, gen);
    process_subsingleton_elem(e);
}

/** Return true if 'e' represents a value (numeral, character, or string).
    TODO(Leo): move this code to a different place. */
bool congruence_closure::is_value(expr const & e) {
    return is_signed_num(e) || is_char_value(m_ctx, e) || is_string_value(e);
}

/** Return true if 'e' represents a value (nat/int numereal, character, or string).
    TODO(Leo): move this code to a different place. */
bool congruence_closure::is_interpreted_value(expr const & e) {
    if (is_string_value(e))
        return true;
    if (is_char_value(m_ctx, e))
        return true;
    if (is_signed_num(e)) {
        expr type = m_ctx.infer(e);
        return is_def_eq(type, mk_nat_type()) || is_def_eq(type, mk_int_type());
    }
    return false;
}

/** Given (f a b c), store in r, (f a), (f a b), (f a b c), and return f.
    Remark: this procedure is very similar to get_app_args.
    TODO(Leo): move this code to a differen place. */
static expr const & get_app_apps(expr const & e, buffer<expr> & r) {
    unsigned sz = r.size();
    expr const * it = &e;
    while (is_app(*it)) {
        r.push_back(*it);
        it = &(app_fn(*it));
    }
    std::reverse(r.begin() + sz, r.end());
    return *it;
}

void congruence_closure::propagate_inst_implicit(expr const & e) {
    bool updated;
    expr new_e = m_defeq_canonizer.canonize(e, updated);
    if (e != new_e) {
        mk_entry(new_e, false, get_generation_of(e));
        push_refl_eq(e, new_e);
    }
}

void congruence_closure::set_ac_var(expr const & e) {
    expr e_root = get_root(e);
    auto root_entry = get_entry(e_root);
    if (root_entry->m_ac_var) {
        m_ac.add_eq(*root_entry->m_ac_var, e);
    } else {
        entry new_root_entry = *root_entry;
        new_root_entry.m_ac_var = some_expr(e);
        m_state.m_entries.insert(e_root, new_root_entry);
    }
}

void congruence_closure::internalize_app(expr const & e, unsigned gen) {
    if (is_interpreted_value(e)) {
        bool interpreted = true;
        mk_entry(e, interpreted, gen);
        if (m_state.m_config.m_values) {
            /* we treat values as atomic symbols */
            return;
        }
    } else {
        bool interpreted = false;
        mk_entry(e, interpreted, gen);
        if (m_state.m_config.m_values && is_value(e)) {
            /* we treat values as atomic symbols */
            return;
        }
    }

    expr lhs, rhs;
    if (is_symm_relation(e, lhs, rhs)) {
        internalize_core(lhs, some_expr(e), gen);
        internalize_core(rhs, some_expr(e), gen);
        bool symm_table = true;
        add_occurrence(e, lhs, symm_table);
        add_occurrence(e, rhs, symm_table);
        add_symm_congruence_table(e);
    } else if (auto lemma = mk_ext_congr_lemma(e)) {
        bool symm_table = false;
        buffer<expr> apps;
        expr const & fn = get_app_apps(e, apps);
        lean_assert(apps.size() > 0);
        lean_assert(apps.back() == e);
        list<param_info> pinfos;
        if (m_state.m_config.m_ignore_instances)
            pinfos = get_fun_info(m_ctx, fn, apps.size()).get_params_info();
        if (!m_state.m_config.m_all_ho && is_constant(fn) && !m_state.m_ho_fns.contains(const_name(fn))) {
            for (unsigned i = 0; i < apps.size(); i++) {
                expr const & arg = app_arg(apps[i]);
                add_occurrence(e, arg, symm_table);
                if (pinfos && head(pinfos).is_inst_implicit()) {
                    /* We do not recurse on instances when m_state.m_config.m_ignore_instances is true. */
                    bool interpreted = false;
                    mk_entry(arg, interpreted, gen);
                    propagate_inst_implicit(arg);
                } else {
                    internalize_core(arg, some_expr(e), gen);
                }
                if (pinfos) pinfos = tail(pinfos);
            }
            internalize_core(fn, some_expr(e), gen);
            add_occurrence(e, fn, symm_table);
            set_fo(e);
            add_congruence_table(e);
        } else {
            /* Expensive case where we store a quadratic number of occurrences,
               as described in the paper "Congruence Closure in Internsional Type Theory" */
            for (unsigned i = 0; i < apps.size(); i++) {
                expr const & curr = apps[i];
                lean_assert(is_app(curr));
                expr const & curr_arg  = app_arg(curr);
                expr const & curr_fn   = app_fn(curr);
                if (i < apps.size() - 1) {
                    bool interpreted = false;
                    mk_entry(curr, interpreted, gen);
                }
                for (unsigned j = i; j < apps.size(); j++) {
                    add_occurrence(apps[j], curr_arg, symm_table);
                    add_occurrence(apps[j], curr_fn, symm_table);
                }
                if (pinfos && head(pinfos).is_inst_implicit()) {
                    /* We do not recurse on instances when m_state.m_config.m_ignore_instances is true. */
                    bool interpreted = false;
                    mk_entry(curr_arg, interpreted, gen);
                    mk_entry(curr_fn, interpreted, gen);
                    propagate_inst_implicit(curr_arg);
                } else {
                    internalize_core(curr_arg, some_expr(e), gen);
                    bool interpreted = false;
                    mk_entry(curr_fn, interpreted, gen);
                }
                if (pinfos) pinfos = tail(pinfos);
                add_congruence_table(curr);
            }
        }
    }
    apply_simple_eqvs(e);
}

void congruence_closure::internalize_core(expr const & e, optional<expr> const & parent, unsigned gen) {
    lean_assert(closed(e));
    /* We allow metavariables after partitions have been frozen. */
    if (has_expr_metavar(e) && !m_state.m_froze_partitions)
        return;
    /* Check whether 'e' has already been internalized. */
    if (!get_entry(e)) {
        switch (e.kind()) {
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Sort:
            break;
        case expr_kind::Constant:
        case expr_kind::Meta:
            mk_entry(e, false, gen);
            break;
        case expr_kind::Lambda:
        case expr_kind::Let:
            mk_entry(e, false, gen);
            break;
        case expr_kind::Local:
            mk_entry(e, false, gen);
            if (is_local_decl_ref(e)) {
                if (auto d = m_ctx.lctx().find_local_decl(e)) {
                    if (auto v = d->get_value()) {
                        push_refl_eq(e, *v);
                    }
                }
            }
            break;
        case expr_kind::Macro:
            if (is_interpreted_value(e)) {
                bool interpreted = true;
                mk_entry(e, interpreted, gen);
            } else {
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    internalize_core(macro_arg(e, i), some_expr(e), gen);
                bool interpreted = false;
                mk_entry(e, interpreted, gen);
                if (is_annotation(e))
                    push_refl_eq(e, get_annotation_arg(e));
            }
            break;
        case expr_kind::Pi:
            if (is_arrow(e) && m_ctx.is_prop(binding_domain(e)) && m_ctx.is_prop(binding_body(e))) {
                internalize_core(binding_domain(e), some_expr(e), gen);
                internalize_core(binding_body(e), some_expr(e), gen);
                bool symm_table = false;
                add_occurrence(e, binding_domain(e), symm_table);
                add_occurrence(e, binding_body(e), symm_table);
                propagate_imp_up(e);
            }
            if (m_ctx.is_prop(e)) {
                mk_entry(e, false, gen);
            }
            break;
        case expr_kind::App: {
            internalize_app(e, gen);
            break;
        }}
    }

    /* Remark: if should invoke m_ac.internalize even if the test !get_entry(e) above failed.
       Reason, the first time e was visited, it may have been visited with a different parent. */
    if (m_state.m_config.m_ac)
        m_ac.internalize(e, parent);
}

/*
  The fields m_target and m_proof in e's entry are encoding a transitivity proof
  Let target(e) and proof(e) denote these fields.

  e    = target(e)           :  proof(e)
   ... = target(target(e))   :  proof(target(e))
   ... ...
       = root(e)             : ...

  The transitivity proof eventually reaches the root of the equivalence class.
  This method "inverts" the proof. That is, the m_target goes from root(e) to e after
  we execute it.
*/
void congruence_closure::invert_trans(expr const & e, bool new_flipped, optional<expr> new_target, optional<expr> new_proof) {
    auto n = get_entry(e);
    lean_assert(n);
    entry new_n = *n;
    if (n->m_target)
        invert_trans(*new_n.m_target, !new_n.m_flipped, some_expr(e), new_n.m_proof);
    new_n.m_target  = new_target;
    new_n.m_proof   = new_proof;
    new_n.m_flipped = new_flipped;
    m_state.m_entries.insert(e, new_n);
}

void congruence_closure::invert_trans(expr const & e) {
    invert_trans(e, false, none_expr(), none_expr());
}

void congruence_closure::remove_parents(expr const & e, buffer<expr> & parents_to_propagate) {
    auto ps = m_state.m_parents.find(e);
    if (!ps) return;
    ps->for_each([&](parent_occ const & pocc) {
            expr const & p = pocc.m_expr;
            lean_trace(name({"debug", "cc"}), scope_trace_env(m_ctx.env(), m_ctx); tout() << "remove parent: " << p << "\n";);
            if (may_propagate(p))
                parents_to_propagate.push_back(p);
            if (is_app(p)) {
                if (pocc.m_symm_table) {
                    expr lhs, rhs;
                    auto rel = is_symm_relation(p, lhs, rhs);
                    lean_assert(rel);
                    unsigned h = mk_symm_hash(lhs, rhs);
                    if (list<pair<expr, name>> const * lst = m_state.m_symm_congruences.find(h)) {
                        pair<expr, name> k(p, *rel);
                        list<pair<expr, name>> new_lst = filter(*lst, [&](pair<expr, name> const & k2) {
                                return !compare_symm(k, k2);
                            });
                        if (new_lst)
                            m_state.m_symm_congruences.insert(h, new_lst);
                        else
                            m_state.m_symm_congruences.erase(h);
                    }
                } else {
                    unsigned h = mk_congr_hash(p);
                    if (list<expr> const * es = m_state.m_congruences.find(h)) {
                        list<expr> new_es = remove(*es, p);
                        if (new_es)
                            m_state.m_congruences.insert(h, new_es);
                        else
                            m_state.m_congruences.erase(h);
                    }
                }
            }
        });
}

void congruence_closure::reinsert_parents(expr const & e) {
    auto ps = m_state.m_parents.find(e);
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            lean_trace(name({"debug", "cc"}), scope_trace_env(m_ctx.env(), m_ctx); tout() << "reinsert parent: " << p.m_expr << "\n";);
            if (is_app(p.m_expr)) {
                if (p.m_symm_table) {
                    add_symm_congruence_table(p.m_expr);
                } else {
                    add_congruence_table(p.m_expr);
                }
            }
        });
}

void congruence_closure::update_mt(expr const & e) {
    expr r  = get_root(e);
    auto ps = m_state.m_parents.find(r);
    if (!ps) return;
    ps->for_each([&](parent_occ const & p) {
            auto it = get_entry(p.m_expr);
            lean_assert(it);
            if (it->m_mt < m_state.m_gmt) {
                auto new_it = *it;
                new_it.m_mt = m_state.m_gmt;
                m_state.m_entries.insert(p.m_expr, new_it);
                update_mt(p.m_expr);
            }
        });
}

void congruence_closure::set_fo(expr const & e) {
    entry d = *get_entry(e);
    d.m_fo  = true;
    m_state.m_entries.insert(e, d);
}

bool congruence_closure::has_heq_proofs(expr const & root) const {
    lean_assert(get_entry(root));
    lean_assert(get_entry(root)->m_root == root);
    return get_entry(root)->m_heq_proofs;
}

expr congruence_closure::flip_proof_core(expr const & H, bool flipped, bool heq_proofs) const {
    expr new_H = H;
    if (heq_proofs && is_eq(m_ctx.relaxed_whnf(m_ctx.infer(new_H)))) {
        new_H = mk_heq_of_eq(m_ctx, new_H);
    }
    if (!flipped) {
        return new_H;
    } else {
        return heq_proofs ? mk_heq_symm(m_ctx, new_H) : mk_eq_symm(m_ctx, new_H);
    }
}

expr congruence_closure::flip_proof(expr const & H, bool flipped, bool heq_proofs) const {
    if (H == *g_congr_mark || H == *g_eq_true_mark || H == *g_refl_mark) {
        return H;
    } else if (is_cc_theory_proof(H)) {
        expr H1 = flip_proof_core(get_cc_theory_proof_arg(H), flipped, heq_proofs);
        return mark_cc_theory_proof(H1);
    } else {
        return flip_proof_core(H, flipped, heq_proofs);
    }
}

expr congruence_closure::mk_trans(expr const & H1, expr const & H2, bool heq_proofs) const {
    return heq_proofs ? mk_heq_trans(m_ctx, H1, H2) : mk_eq_trans(m_ctx, H1, H2);
}

expr congruence_closure::mk_trans(optional<expr> const & H1, expr const & H2, bool heq_proofs) const {
    if (!H1) return H2;
    return mk_trans(*H1, H2, heq_proofs);
}

expr congruence_closure::mk_congr_proof_core(expr const & lhs, expr const & rhs, bool heq_proofs) const {
    buffer<expr> lhs_args, rhs_args;
    expr const * lhs_it = &lhs;
    expr const * rhs_it = &rhs;
    if (lhs != rhs) {
        while (true) {
            lhs_args.push_back(app_arg(*lhs_it));
            rhs_args.push_back(app_arg(*rhs_it));
            lhs_it = &app_fn(*lhs_it);
            rhs_it = &app_fn(*rhs_it);
            if (*lhs_it == *rhs_it)
                break;
            if (is_def_eq(*lhs_it, *rhs_it))
                break;
            if (is_eqv(*lhs_it, *rhs_it) &&
                is_def_eq(m_ctx.infer(*lhs_it), m_ctx.infer(*rhs_it)))
                break;
        }
    }
    if (lhs_args.empty()) {
        if (heq_proofs)
            return mk_heq_refl(m_ctx, lhs);
        else
            return mk_eq_refl(m_ctx, lhs);
    }
    std::reverse(lhs_args.begin(), lhs_args.end());
    std::reverse(rhs_args.begin(), rhs_args.end());
    lean_assert(lhs_args.size() == rhs_args.size());
    expr const & lhs_fn = *lhs_it;
    expr const & rhs_fn = *rhs_it;
    lean_assert(is_eqv(lhs_fn, rhs_fn) || is_def_eq(lhs_fn, rhs_fn));
    lean_assert(is_def_eq(m_ctx.infer(lhs_fn), m_ctx.infer(rhs_fn)));
    /* Create proof for
          (lhs_fn lhs_args[0] ... lhs_args[n-1]) = (lhs_fn rhs_args[0] ... rhs_args[n-1])
       where
          n == lhs_args.size()
    */
    auto spec_lemma = mk_ext_hcongr_lemma(lhs_fn, lhs_args.size());
    lean_assert(spec_lemma);
    list<congr_arg_kind> const * kinds_it = &spec_lemma->m_congr_lemma.get_arg_kinds();
    buffer<expr> lemma_args;
    for (unsigned i = 0; i < lhs_args.size(); i++) {
        lean_assert(kinds_it);
        lemma_args.push_back(lhs_args[i]);
        lemma_args.push_back(rhs_args[i]);
        if (head(*kinds_it) == congr_arg_kind::HEq) {
            lemma_args.push_back(*get_heq_proof(lhs_args[i], rhs_args[i]));
        } else {
            lean_assert(head(*kinds_it) == congr_arg_kind::Eq);
            lemma_args.push_back(*get_eq_proof(lhs_args[i], rhs_args[i]));
        }
        kinds_it = &(tail(*kinds_it));
    }
    expr r = mk_app(spec_lemma->m_congr_lemma.get_proof(), lemma_args);
    if (spec_lemma->m_heq_result && !heq_proofs)
        r = mk_eq_of_heq(m_ctx, r);
    else if (!spec_lemma->m_heq_result && heq_proofs)
        r = mk_heq_of_eq(m_ctx, r);
    if (is_def_eq(lhs_fn, rhs_fn))
        return r;
    /* Convert r into a proof of lhs = rhs using eq.rec and
       the proof that lhs_fn = rhs_fn */
    expr lhs_fn_eq_rhs_fn = *get_eq_proof(lhs_fn, rhs_fn);
    type_context_old::tmp_locals locals(m_ctx);
    expr x                = locals.push_local("_x", m_ctx.infer(lhs_fn));
    expr motive_rhs       = mk_app(x, rhs_args);
    expr motive           = heq_proofs ? mk_heq(m_ctx, lhs, motive_rhs) : mk_eq(m_ctx, lhs, motive_rhs);
    motive                = locals.mk_lambda(motive);
    return mk_eq_rec(m_ctx, motive, r, lhs_fn_eq_rhs_fn);
}

optional<expr> congruence_closure::mk_symm_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const {
    expr lhs1, rhs1, lhs2, rhs2;
    auto R1 = is_symm_relation(e1, lhs1, rhs1);
    if (!R1) return none_expr();
    auto R2 = is_symm_relation(e2, lhs2, rhs2);
    if (!R2 || *R1 != *R2) return none_expr();
    if (!is_eqv(lhs1, lhs2)) {
        lean_assert(is_eqv(lhs1, rhs2));
        /*
          We must apply symmetry.
          The symm congruence table is implicitly using symmetry.
          That is, we have
             e1 := lhs1 ~R1~ rhs1
          and
             e2 := lhs2 ~R1~ rhs2
          But,
          (lhs1 ~R1 ~rhs2) and (rhs1 ~R1~ lhs2)
        */
        /*
         Given e1 := lhs1 ~R1~ rhs1,
         create proof for
           (lhs1 ~R1~ rhs1) = (rhs1 ~R1~ lhs1)
        */
        expr new_e1 = mk_rel(m_ctx, *R1, rhs1, lhs1);
        type_context_old::tmp_locals locals(m_ctx);
        expr h1  = locals.push_local("_h1", e1);
        expr h2  = locals.push_local("_h2", new_e1);
        expr e1_iff_new_e1 = mk_app(m_ctx, get_iff_intro_name(),
                                    m_ctx.mk_lambda(h1, mk_symm(m_ctx, *R1, h1)),
                                    m_ctx.mk_lambda(h2, mk_symm(m_ctx, *R1, h2)));
        expr e1_eq_new_e1  = mk_propext(e1, new_e1, e1_iff_new_e1);
        expr new_e1_eq_e2  = mk_congr_proof_core(new_e1, e2, heq_proofs);
        if (heq_proofs)
            e1_eq_new_e1   = mk_heq_of_eq(m_ctx, e1_eq_new_e1);
        return some_expr(mk_trans(e1_eq_new_e1, new_e1_eq_e2, heq_proofs));
    }
    return none_expr();
}

expr congruence_closure::mk_congr_proof(expr const & e1, expr const & e2, bool heq_proofs) const {
    if (auto r = mk_symm_congr_proof(e1, e2, heq_proofs))
        return *r;
    else
        return mk_congr_proof_core(e1, e2, heq_proofs);
}

expr congruence_closure::mk_proof(expr const & lhs, expr const & rhs, expr const & H, bool heq_proofs) const {
    if (H == *g_congr_mark) {
        return mk_congr_proof(lhs, rhs, heq_proofs);
    } else if (H == *g_eq_true_mark) {
        bool flip;
        expr a, b;
        name R;
        if (lhs == mk_true()) {
            R = *is_refl_relation(rhs, a, b);
            flip = true;
        } else {
            R = *is_refl_relation(lhs, a, b);
            flip = false;
        }
        expr a_R_b;
        if (R == get_eq_name()) {
            a_R_b        = *get_eq_proof(a, b);
        } else if (R == get_heq_name()) {
            a_R_b        = *get_heq_proof(a, b);
        } else {
            /* TODO(Leo): the following code assumes R is homogeneous.
               We should add support arbitrary heterogenous reflexive relations. */
            expr a_eq_b  = *get_eq_proof(a, b);
            a_R_b        = lift_from_eq(m_ctx, R, a_eq_b);
        }
        expr a_R_b_eq_true = mk_eq_true_intro(m_ctx, a_R_b);
        if (flip)
            return mk_eq_symm(m_ctx, a_R_b_eq_true);
        else
            return a_R_b_eq_true;
    } else if (H == *g_refl_mark) {
        expr type  = heq_proofs ? mk_heq(m_ctx, lhs, rhs) : mk_eq(m_ctx, lhs, rhs);
        expr proof = heq_proofs ? mk_heq_refl(m_ctx, lhs) : mk_eq_refl(m_ctx, lhs);
        return mk_app(mk_constant(get_id_name(), {mk_level_zero()}), type, proof);
    } else if (is_cc_theory_proof(H)) {
        return expand_delayed_cc_proofs(*this, get_cc_theory_proof_arg(H));
    } else {
        return H;
    }
}

/*
   If as_heq is true, then build a proof for (e1 == e2).
   Otherwise, build a proof for (e1 = e2).
   The result is none if e1 and e2 are not in the same equivalence class. */
optional<expr> congruence_closure::get_eq_proof_core(expr const & e1, expr const & e2, bool as_heq) const {
    if (has_expr_metavar(e1) || has_expr_metavar(e2)) return none_expr();
    if (is_def_eq(e1, e2))
        return as_heq ? some_expr(mk_heq_refl(m_ctx, e1)) : some_expr(mk_eq_refl(m_ctx, e1));
    auto n1 = get_entry(e1);
    if (!n1) return none_expr();
    auto n2 = get_entry(e2);
    if (!n2) return none_expr();
    if (n1->m_root != n2->m_root) return none_expr();
    bool heq_proofs = has_heq_proofs(n1->m_root);
    // 1. Retrieve "path" from e1 to root
    buffer<expr> path1, Hs1;
    rb_expr_tree visited;
    expr it1 = e1;
    while (true) {
        visited.insert(it1);
        auto it1_n = get_entry(it1);
        lean_assert(it1_n);
        if (!it1_n->m_target)
            break;
        path1.push_back(*it1_n->m_target);
        Hs1.push_back(flip_proof(*it1_n->m_proof, it1_n->m_flipped, heq_proofs));
        it1 = *it1_n->m_target;
    }
    lean_assert(it1 == n1->m_root);
    // 2. The path from e2 to root must have at least one element c in visited
    // Retrieve "path" from e2 to c
    buffer<expr> path2, Hs2;
    expr it2 = e2;
    while (true) {
        if (visited.contains(it2))
            break; // found common
        auto it2_n = get_entry(it2);
        lean_assert(it2_n);
        lean_assert(it2_n->m_target);
        path2.push_back(it2);
        Hs2.push_back(flip_proof(*it2_n->m_proof, !it2_n->m_flipped, heq_proofs));
        it2 = *it2_n->m_target;
    }
    // it2 is the common element...
    // 3. Shrink path1/Hs1 until we find it2 (the common element)
    while (true) {
        if (path1.empty()) {
            lean_assert(it2 == e1);
            break;
        }
        if (path1.back() == it2) {
            // found it!
            break;
        }
        path1.pop_back();
        Hs1.pop_back();
    }

    // 4. Build transitivity proof
    optional<expr> pr;
    expr lhs = e1;
    for (unsigned i = 0; i < path1.size(); i++) {
        pr  = mk_trans(pr, mk_proof(lhs, path1[i], Hs1[i], heq_proofs), heq_proofs);
        lhs = path1[i];
    }
    unsigned i = Hs2.size();
    while (i > 0) {
        --i;
        pr  = mk_trans(pr, mk_proof(lhs, path2[i], Hs2[i], heq_proofs), heq_proofs);
        lhs = path2[i];
    }
    lean_assert(pr);
    if (heq_proofs && !as_heq)
        pr = mk_eq_of_heq(m_ctx, *pr);
    else if (!heq_proofs && as_heq)
        pr = mk_heq_of_eq(m_ctx, *pr);
    return pr;
}

optional<expr> congruence_closure::get_eq_proof(expr const & e1, expr const & e2) const {
    return get_eq_proof_core(e1, e2, false);
}

optional<expr> congruence_closure::get_heq_proof(expr const & e1, expr const & e2) const {
    return get_eq_proof_core(e1, e2, true);
}

optional<expr> congruence_closure::get_proof(expr const & e1, expr const & e2) const {
    auto n1 = get_entry(e1);
    if (!n1) return none_expr();
    if (!has_heq_proofs(n1->m_root))
        return get_eq_proof(e1, e2);
    else if (relaxed_is_def_eq(m_ctx.infer(e1), m_ctx.infer(e2)))
        return get_eq_proof(e1, e2);
    else
        return get_heq_proof(e1, e2);
}

void congruence_closure::push_subsingleton_eq(expr const & a, expr const & b) {
    /* Remark: we must use normalize here because we have use it before
       internalizing the types of 'a' and 'b'. */
    expr A = normalize(m_ctx.infer(a));
    expr B = normalize(m_ctx.infer(b));
    /* TODO(Leo): check if the following test is a performance bottleneck */
    if (relaxed_is_def_eq(A, B)) {
        /* TODO(Leo): to improve performance we can create the following proof lazily */
        expr proof     = mk_app(m_ctx, get_subsingleton_elim_name(), a, b);
        push_eq(a, b, proof);
    } else {
        expr A_eq_B    = *get_eq_proof(A, B);
        expr proof     = mk_app(m_ctx, get_subsingleton_helim_name(), A_eq_B, a, b);
        push_heq(a, b, proof);
    }
}

void congruence_closure::check_new_subsingleton_eq(expr const & old_root, expr const & new_root) {
    lean_assert(is_eqv(old_root, new_root));
    lean_assert(get_root(old_root) == new_root);
    auto it1 = m_state.m_subsingleton_reprs.find(old_root);
    if (!it1) return;
    if (auto it2 = m_state.m_subsingleton_reprs.find(new_root)) {
        push_subsingleton_eq(*it1, *it2);
    } else {
        m_state.m_subsingleton_reprs.insert(new_root, *it1);
    }
}

/* Given a new equality e1 = e2, where e1 and e2 are constructor applications.
   Implement the following implications:

   - c a_1 ... a_n = c b_1 ... b_n => a_1 = b_1, ..., a_n = b_n

   - c_1 ... = c_2 ... => false

   where c, c_1 and c_2 are constructors */
void congruence_closure::propagate_constructor_eq(expr const & e1, expr const & e2) {
    /* Remark: is_constructor_app does not check for partially applied constructor applications.
       So, we must check whether mk_constructor_eq_constructor_inconsistency_proof fails,
       and we should not assume that mk_constructor_eq_constructor_implied_eqs will succeed. */
    optional<name> c1 = is_constructor_app(env(), e1);
    optional<name> c2 = is_constructor_app(env(), e2);
    lean_assert(c1 && c2);
    if (!is_def_eq(m_ctx.infer(e1), m_ctx.infer(e2))) {
        /* The implications above only hold if the types are equal.

           TODO(Leo): if the types are different, we may still propagate by searching the equivalence
           classes of e1 and e2 for other constructors that may have compatible types. */
        return;
    }
    expr type       = mk_eq(m_ctx, e1, e2);
    expr h          = *get_eq_proof(e1, e2);
    if (*c1 == *c2) {
        buffer<std::tuple<expr, expr, expr>> implied_eqs;
        mk_constructor_eq_constructor_implied_eqs(m_ctx, e1, e2, h, implied_eqs);
        for (std::tuple<expr, expr, expr> const & t : implied_eqs) {
            expr lhs, rhs, H;
            std::tie(lhs, rhs, H) = t;
            if (is_def_eq(m_ctx.infer(lhs), m_ctx.infer(rhs)))
                push_eq(lhs, rhs, H);
            else
                push_heq(lhs, rhs, H);
        }
    } else {
        if (optional<expr> false_pr = mk_constructor_eq_constructor_inconsistency_proof(m_ctx, e1, e2, h)) {
            expr H        = mk_app(mk_constant(get_true_eq_false_of_false_name()), *false_pr);
            push_eq(mk_true(), mk_false(), H);
        }
    }
}

/* Given c a constructor application, if p is a projection application such that major premise is equal to c,
   then propagate new equality.

   Example: if p is of the form b.1, c is of the form (x, y), and b = c, we add the equality
   (x, y).1 = x */
void congruence_closure::propagate_projection_constructor(expr const & p, expr const & c) {
    lean_verify(is_constructor_app(env(), c));
    expr const & p_fn = get_app_fn(p);
    if (!is_constant(p_fn)) return;
    projection_info const * info = get_projection_info(env(), const_name(p_fn));
    if (!info) return;
    buffer<expr> p_args;
    get_app_args(p, p_args);
    if (p_args.size() <= info->m_nparams) return;
    unsigned mkidx  = info->m_nparams;
    if (!is_eqv(p_args[mkidx], c)) return;
    if (!relaxed_is_def_eq(m_ctx.infer(p_args[mkidx]), m_ctx.infer(c))) return;
    /* Create new projection application using c (e.g., (x, y).1), and internalize it.
       The internalizer will add the new equality. */
    p_args[mkidx] = c;
    expr new_p = mk_app(p_fn, p_args);
    internalize_core(new_p, none_expr(), get_generation_of(p));
}

bool congruence_closure::is_eq_true(expr const & e) const {
    return is_eqv(e, mk_true());
}

bool congruence_closure::is_eq_false(expr const & e) const {
    return is_eqv(e, mk_false());
}

// Remark: possible optimization: use delayed proof macros for get_eq_true_proof, get_eq_false_proof and get_prop_eq_proof

expr congruence_closure::get_eq_true_proof(expr const & e) const {
    lean_assert(is_eq_true(e));
    return *get_eq_proof(e, mk_true());
}

expr congruence_closure::get_eq_false_proof(expr const & e) const {
    lean_assert(is_eq_false(e));
    return *get_eq_proof(e, mk_false());
}

expr congruence_closure::get_prop_eq_proof(expr const & a, expr const & b) const {
    lean_assert(is_eqv(a, b));
    return *get_eq_proof(a, b);
}

static expr * g_iff_eq_of_eq_true_left  = nullptr;
static expr * g_iff_eq_of_eq_true_right = nullptr;
static expr * g_iff_eq_true_of_eq       = nullptr;

void congruence_closure::propagate_iff_up(expr const & e) {
    expr a, b;
    lean_verify(is_iff(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (iff a b) = b
        push_eq(e, b, mk_app(*g_iff_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (iff a b) = a
        push_eq(e, a, mk_app(*g_iff_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (iff a b) = true
        push_eq(e, mk_true(), mk_app(*g_iff_eq_true_of_eq, a, b, get_prop_eq_proof(a, b)));
    }
}

static expr * g_and_eq_of_eq_true_left   = nullptr;
static expr * g_and_eq_of_eq_true_right  = nullptr;
static expr * g_and_eq_of_eq_false_left  = nullptr;
static expr * g_and_eq_of_eq_false_right = nullptr;
static expr * g_and_eq_of_eq             = nullptr;

void congruence_closure::propagate_and_up(expr const & e) {
    expr a, b;
    lean_verify(is_and(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (and a b) = b
        push_eq(e, b, mk_app(*g_and_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (and a b) = a
        push_eq(e, a, mk_app(*g_and_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(a)) {
        // a = false -> (and a b) = false
        push_eq(e, mk_false(), mk_app(*g_and_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_false(b)) {
        // b = false -> (and a b) = false
        push_eq(e, mk_false(), mk_app(*g_and_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (and a b) = a
        push_eq(e, a, mk_app(*g_and_eq_of_eq, a, b, get_prop_eq_proof(a, b)));
    }

    // We may also add
    // a = not b -> (and a b) = false
}

static expr * g_or_eq_of_eq_true_left   = nullptr;
static expr * g_or_eq_of_eq_true_right  = nullptr;
static expr * g_or_eq_of_eq_false_left  = nullptr;
static expr * g_or_eq_of_eq_false_right = nullptr;
static expr * g_or_eq_of_eq             = nullptr;

void congruence_closure::propagate_or_up(expr const & e) {
    expr a, b;
    lean_verify(is_or(e, a, b));

    if (is_eq_true(a)) {
        // a = true  -> (or a b) = true
        push_eq(e, mk_true(), mk_app(*g_or_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (or a b) = true
        push_eq(e, mk_true(), mk_app(*g_or_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(a)) {
        // a = false -> (or a b) = b
        push_eq(e, b, mk_app(*g_or_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_false(b)) {
        // b = false -> (or a b) = a
        push_eq(e, a, mk_app(*g_or_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
    } else if (is_eqv(a, b)) {
        // a = b     -> (or a b) = a
        push_eq(e, a, mk_app(*g_or_eq_of_eq, a, b, get_prop_eq_proof(a, b)));
    }

    // We may also add
    // a = not b -> (or a b) = true
}

static expr * g_not_eq_of_eq_true   = nullptr;
static expr * g_not_eq_of_eq_false  = nullptr;
static expr * g_false_of_a_eq_not_a = nullptr;

void congruence_closure::propagate_not_up(expr const & e) {
    expr a;
    lean_verify(is_not(e, a));

    if (is_eq_true(a)) {
        // a = true  -> not a = false
        push_eq(e, mk_false(), mk_app(*g_not_eq_of_eq_true, a, get_eq_true_proof(a)));
    } else if (is_eq_false(a)) {
        // a = false -> not a = true
        push_eq(e, mk_true(), mk_app(*g_not_eq_of_eq_false, a, get_eq_false_proof(a)));
    } else if (is_eqv(a, e)) {
        expr false_pr = mk_app(*g_false_of_a_eq_not_a, a, get_prop_eq_proof(a, e));
        expr H        = mk_app(mk_constant(get_true_eq_false_of_false_name()), false_pr);
        push_eq(mk_true(), mk_false(), H);
    }
}

static expr * g_imp_eq_of_eq_true_left       = nullptr;
static expr * g_imp_eq_of_eq_false_left      = nullptr;
static expr * g_imp_eq_of_eq_true_right      = nullptr;
static expr * g_imp_eq_true_of_eq            = nullptr;
static expr * g_not_imp_eq_of_eq_false_right = nullptr;
static expr * g_imp_eq_of_eq_false_right     = nullptr;

void congruence_closure::propagate_imp_up(expr const & e) {
    lean_assert(is_arrow(e));
    expr a = binding_domain(e);
    expr b = binding_body(e);

    if (is_eq_true(a)) {
        // a = true  -> (a -> b) = b
        push_eq(e, b, mk_app(*g_imp_eq_of_eq_true_left, a, b, get_eq_true_proof(a)));
    } else if (is_eq_false(a)) {
        // a = false -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_of_eq_false_left, a, b, get_eq_false_proof(a)));
    } else if (is_eq_true(b)) {
        // b = true  -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_of_eq_true_right, a, b, get_eq_true_proof(b)));
    } else if (is_eq_false(b)) {
        expr arg;
        if (is_not(a, arg)) {
            if (m_state.m_config.m_em) {
                // b = false -> (not a -> b) = a
                push_eq(e, arg, mk_app(*g_not_imp_eq_of_eq_false_right, arg, b, get_eq_false_proof(b)));
            }
        } else {
            // b = false -> (a -> b) = not a
            expr not_a = mk_not(a);
            internalize_core(not_a, none_expr(), get_generation_of(e));
            push_eq(e, not_a, mk_app(*g_imp_eq_of_eq_false_right, a, b, get_eq_false_proof(b)));
        }
    } else if (is_eqv(a, b)) {
        // a = b     -> (a -> b) = true
        push_eq(e, mk_true(), mk_app(*g_imp_eq_true_of_eq, a, b, get_prop_eq_proof(a, b)));
    }
}

static name * g_if_eq_of_eq_true  = nullptr;
static name * g_if_eq_of_eq_false = nullptr;
static name * g_if_eq_of_eq       = nullptr;

void congruence_closure::propagate_ite_up(expr const & e) {
    expr c, d, A, a, b;
    lean_verify(is_ite(e, c, d, A, a, b));

    if (is_eq_true(c)) {
        // c = true  -> (ite c a b) = a
        level lvl = get_level(m_ctx, A);
        push_eq(e, a, mk_app({mk_constant(*g_if_eq_of_eq_true, {lvl}), c, d, A, a, b, get_eq_true_proof(c)}));
    } else if (is_eq_false(c)) {
        // c = false -> (ite c a b) = b
        level lvl = get_level(m_ctx, A);
        push_eq(e, b, mk_app({mk_constant(*g_if_eq_of_eq_false, {lvl}), c, d, A, a, b, get_eq_false_proof(c)}));
    } else if (is_eqv(a, b)) {
        // a = b     -> (ite c a b) = a
        level lvl = get_level(m_ctx, A);
        push_eq(e, a, mk_app({mk_constant(*g_if_eq_of_eq, {lvl}), c, d, A, a, b, get_prop_eq_proof(a, b)}));
    }
}

bool congruence_closure::may_propagate(expr const & e) {
    return
        is_iff(e) || is_and(e) || is_or(e) || is_not(e) || is_arrow(e) || is_ite(e);
}

static name * g_ne_of_eq_of_ne = nullptr;
static name * g_ne_of_ne_of_eq = nullptr;

optional<expr> congruence_closure::mk_ne_of_eq_of_ne(expr const & a, expr const & a1, expr const & a1_ne_b) {
    lean_assert(is_eqv(a, a1));
    if (a == a1)
        return some_expr(a1_ne_b);
    auto a_eq_a1 = get_eq_proof(a, a1);
    if (!a_eq_a1) return none_expr(); // failed to build proof
    return some_expr(mk_app(m_ctx, *g_ne_of_eq_of_ne, 6, *a_eq_a1, a1_ne_b));
}

optional<expr> congruence_closure::mk_ne_of_ne_of_eq(expr const & a_ne_b1, expr const & b1, expr const & b) {
    lean_assert(is_eqv(b, b1));
    if (b == b1)
        return some_expr(a_ne_b1);
    auto b1_eq_b = get_eq_proof(b1, b);
    if (!b1_eq_b) return none_expr(); // failed to build proof
    return some_expr(mk_app(m_ctx, *g_ne_of_ne_of_eq, 6, a_ne_b1, *b1_eq_b));
}

void congruence_closure::propagate_eq_up(expr const & e) {
    /* Remark: the positive case is implemented at check_eq_true
       for any reflexive relation. */
    expr a, b;
    lean_verify(is_eq(e, a, b));
    expr ra = get_root(a);
    expr rb = get_root(b);
    if (ra != rb) {
        optional<expr> ra_ne_rb;
        if (is_interpreted_value(ra) && is_interpreted_value(rb)) {
            ra_ne_rb = mk_val_ne_proof(m_ctx, ra, rb);
        } else {
            if (optional<name> c1 = is_constructor_app(env(), ra))
            if (optional<name> c2 = is_constructor_app(env(), rb))
            if (c1 && c2 && *c1 != *c2)
                ra_ne_rb = mk_constructor_ne_constructor_proof(m_ctx, ra, rb);
        }
        if (ra_ne_rb)
        if (auto a_ne_rb = mk_ne_of_eq_of_ne(a, ra, *ra_ne_rb))
        if (auto a_ne_b = mk_ne_of_ne_of_eq(*a_ne_rb, rb, b))
            push_eq(e, mk_false(), mk_eq_false_intro(m_ctx, *a_ne_b));
    }
}

void congruence_closure::propagate_up(expr const & e) {
    if (m_state.m_inconsistent) return;
    if (is_iff(e)) {
        propagate_iff_up(e);
    } else if (is_and(e)) {
        propagate_and_up(e);
    } else if (is_or(e)) {
        propagate_or_up(e);
    } else if (is_not(e)) {
        propagate_not_up(e);
    } else if (is_arrow(e)) {
        propagate_imp_up(e);
    } else if (is_ite(e)) {
        propagate_ite_up(e);
    } else if (is_eq(e)) {
        propagate_eq_up(e);
    }
}

static expr * g_eq_true_of_and_eq_true_left  = nullptr;
static expr * g_eq_true_of_and_eq_true_right = nullptr;

void congruence_closure::propagate_and_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a, b;
        lean_verify(is_and(e, a, b));
        expr h = get_eq_true_proof(e);
        push_eq(a, mk_true(), mk_app(*g_eq_true_of_and_eq_true_left, a, b, h));
        push_eq(b, mk_true(), mk_app(*g_eq_true_of_and_eq_true_right, a, b, h));
    }
}

static expr * g_eq_false_of_or_eq_false_left  = nullptr;
static expr * g_eq_false_of_or_eq_false_right = nullptr;

void congruence_closure::propagate_or_down(expr const & e) {
    if (is_eq_false(e)) {
        expr a, b;
        lean_verify(is_or(e, a, b));
        expr h = get_eq_false_proof(e);
        push_eq(a, mk_false(), mk_app(*g_eq_false_of_or_eq_false_left, a, b, h));
        push_eq(b, mk_false(), mk_app(*g_eq_false_of_or_eq_false_right, a, b, h));
    }
}

static expr * g_eq_false_of_not_eq_true = nullptr;
static expr * g_eq_true_of_not_eq_false = nullptr;

void congruence_closure::propagate_not_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a;
        lean_verify(is_not(e, a));
        push_eq(a, mk_false(), mk_app(*g_eq_false_of_not_eq_true, a, get_eq_true_proof(e)));
    } else if (m_state.m_config.m_em && is_eq_false(e)) {
        expr a;
        lean_verify(is_not(e, a));
        push_eq(a, mk_true(), mk_app(*g_eq_true_of_not_eq_false, a, get_eq_false_proof(e)));
    }
}

void congruence_closure::propagate_eq_down(expr const & e) {
    if (is_eq_true(e)) {
        expr a, b;
        if (is_eq(e, a, b) || is_iff(e, a, b)) {
            push_eq(a, b, mk_of_eq_true(m_ctx, get_eq_true_proof(e)));
        } else {
            lean_unreachable();
        }
    }
}

/** Given (h_not_ex : not ex) where ex is of the form (exists x, p x),
    return a (forall x, not p x) and a proof for it.

    This function handles nested existentials. */
expr_pair congruence_closure::to_forall_not(expr const & ex, expr const & h_not_ex) {
    lean_assert(is_exists(ex));
    expr A, p;
    lean_verify(is_exists(ex, A, p));
    type_context_old::tmp_locals locals(m_ctx);
    level lvl         = get_level(m_ctx, A);
    expr x            = locals.push_local("_x", A);
    expr px           = head_beta_reduce(mk_app(p, x));
    expr not_px       = mk_not(px);
    expr h_all_not_px = mk_app({mk_constant(get_forall_not_of_not_exists_name(), {lvl}), A, p, h_not_ex});
    if (is_exists(px)) {
        expr h_not_px = locals.push_local("_h", not_px);
        auto p               = to_forall_not(px, h_not_px);
        expr qx              = p.first;
        expr all_qx          = m_ctx.mk_pi(x, qx);
        expr h_qx            = p.second;
        expr h_not_px_imp_qx = m_ctx.mk_lambda(h_not_px, h_qx);
        expr h_all_qx        = m_ctx.mk_lambda({x}, mk_app(h_not_px_imp_qx, mk_app(h_all_not_px, x)));
        return mk_pair(all_qx, h_all_qx);
    } else {
        expr all_not_px      = m_ctx.mk_pi(x, not_px);
        return mk_pair(all_not_px, h_all_not_px);
    }
}

void congruence_closure::propagate_exists_down(expr const & e) {
    if (is_eq_false(e)) {
        expr h_not_e = mk_not_of_eq_false(m_ctx, get_eq_false_proof(e));
        expr all, h_all;
        std::tie(all, h_all) = to_forall_not(e, h_not_e);
        internalize_core(all, none_expr(), get_generation_of(e));
        push_eq(all, mk_true(), mk_eq_true_intro(m_ctx, h_all));
    }
}

void congruence_closure::propagate_down(expr const & e) {
    if (is_and(e)) {
        propagate_and_down(e);
    } else if (is_or(e)) {
        propagate_or_down(e);
    } else if (is_not(e)) {
        propagate_not_down(e);
    } else if (is_eq(e) || is_iff(e)) {
        propagate_eq_down(e);
    } else if (is_exists(e)) {
        propagate_exists_down(e);
    }
}

void congruence_closure::propagate_value_inconsistency(expr const & e1, expr const & e2) {
    lean_assert(is_interpreted_value(e1));
    lean_assert(is_interpreted_value(e2));
    expr ne_proof      = *mk_val_ne_proof(m_ctx, e1, e2);
    expr eq_proof      = *get_eq_proof(e1, e2);
    expr true_eq_false = mk_eq(m_ctx, mk_true(), mk_false());
    expr H             = mk_absurd(m_ctx, eq_proof, ne_proof, true_eq_false);
    push_eq(mk_true(), mk_false(), H);
}

static bool is_true_or_false(expr const & e) {
    return is_constant(e, get_true_name()) || is_constant(e, get_false_name());
}

void congruence_closure::get_eqc_lambdas(expr const & e, buffer<expr> & r) {
    lean_assert(get_root(e) == e);
    if (!get_entry(e)->m_has_lambdas) return;
    auto it = e;
    do {
        if (is_lambda(it))
            r.push_back(it);
        auto it_n = get_entry(it);
        it = it_n->m_next;
    } while (it != e);
}

void congruence_closure::propagate_beta(expr const & fn, buffer<expr> const & rev_args,
                                        buffer<expr> const & lambdas, buffer<expr> & new_lambda_apps) {
    for (expr const & lambda : lambdas) {
        lean_assert(is_lambda(lambda));
        if (fn != lambda && relaxed_is_def_eq(m_ctx.infer(fn), m_ctx.infer(lambda))) {
            expr new_app = mk_rev_app(lambda, rev_args);
            new_lambda_apps.push_back(new_app);
        }
    }
}

/* Traverse the root's equivalence class, and collect the function's equivalence class roots. */
void congruence_closure::collect_fn_roots(expr const & root, buffer<expr> & fn_roots) {
    lean_assert(get_root(root) == root);
    rb_expr_tree visited;
    auto it = root;
    do {
        expr fn_root = get_root(get_app_fn(it));
        if (!visited.contains(fn_root)) {
            visited.insert(fn_root);
            fn_roots.push_back(fn_root);
        }
        auto it_n = get_entry(it);
        it = it_n->m_next;
    } while (it != root);
}

/* For each fn_root in fn_roots traverse its parents, and look for a parent prefix that is
   in the same equivalence class of the given lambdas.

   \remark All expressions in lambdas are in the same equivalence class */
void congruence_closure::propagate_beta_to_eqc(buffer<expr> const & fn_roots, buffer<expr> const & lambdas,
                                               buffer<expr> & new_lambda_apps) {
    if (lambdas.empty()) return;
    expr const & lambda_root = get_root(lambdas.back());
    lean_assert(std::all_of(lambdas.begin(), lambdas.end(), [&](expr const & l) {
                return is_lambda(l) && get_root(l) == lambda_root;
            }));
    for (expr const & fn_root : fn_roots) {
        if (auto ps = m_state.m_parents.find(fn_root)) {
            ps->for_each([&](parent_occ const & p_occ) {
                    expr const & p = p_occ.m_expr;
                    /* Look for a prefix of p which is in the same equivalence class of lambda_root */
                    buffer<expr> rev_args;
                    expr it2 = p;
                    while (is_app(it2)) {
                        expr const & fn = app_fn(it2);
                        rev_args.push_back(app_arg(it2));
                        if (get_root(fn) == lambda_root) {
                            /* found it */
                            propagate_beta(fn, rev_args, lambdas, new_lambda_apps);
                            break;
                        }
                        it2 = app_fn(it2);
                    }
                });
        }
    }
}

void congruence_closure::add_eqv_step(expr e1, expr e2, expr const & H, bool heq_proof) {
    auto n1 = get_entry(e1);
    auto n2 = get_entry(e2);
    if (!n1 || !n2)
        return; /* e1 and e2 have not been internalized */
    if (n1->m_root == n2->m_root)
        return; /* they are already in the same equivalence class. */
    auto r1 = get_entry(n1->m_root);
    auto r2 = get_entry(n2->m_root);
    lean_assert(r1 && r2);
    bool flipped = false;

    /* We want r2 to be the root of the combined class. */

    /*
     We swap (e1,n1,r1) with (e2,n2,r2) when
     1- r1->m_interpreted && !r2->m_interpreted.
        Reason: to decide when to propagate we check whether the root of the equivalence class
        is true/false. So, this condition is to make sure if true/false is in an equivalence class,
        then one of them is the root. If both are, it doesn't matter, since the state is inconsistent
        anyway.
     2- r1->m_constructor && !r2->m_interpreted && !r2->m_constructor
        Reason: we want constructors to be the representative of their equivalence classes.
     3- r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor
        Reason: performance.
    */
    if ((r1->m_interpreted && !r2->m_interpreted) ||
        (r1->m_constructor && !r2->m_interpreted && !r2->m_constructor) ||
        (r1->m_size > r2->m_size && !r2->m_interpreted && !r2->m_constructor)) {
        std::swap(e1, e2);
        std::swap(n1, n2);
        std::swap(r1, r2);
        // Remark: we don't apply symmetry eagerly. So, we don't adjust H.
        flipped = true;
    }

    bool value_inconsistency = false;
    if (r1->m_interpreted && r2->m_interpreted) {
        if (is_true(n1->m_root) || is_true(n2->m_root)) {
            m_state.m_inconsistent = true;
        } else if (is_num(n1->m_root) && is_num(n2->m_root)) {
            /* Little hack to cope with the fact that we don't have a canonical representation
               for nat numerals. For example: is_num returns true for
               both (nat.succ nat.zero) and (@one nat nat.has_one). */
            value_inconsistency = to_num(n1->m_root) != to_num(n2->m_root);
        } else {
            value_inconsistency = true;
        }
    }

    bool constructor_eq = r1->m_constructor && r2->m_constructor;
    expr e1_root   = n1->m_root;
    expr e2_root   = n2->m_root;
    entry new_n1   = *n1;
    lean_trace(name({"debug", "cc"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               tout() << "merging:\n" << e1 << " ==> " << e1_root << "\nwith\n" << e2_root << " <== " << e2 << "\n";);

    /*
     Following target/proof we have
     e1 -> ... -> r1
     e2 -> ... -> r2
     We want
     r1 -> ... -> e1 -> e2 -> ... -> r2
    */
    invert_trans(e1);
    new_n1.m_target  = e2;
    new_n1.m_proof   = H;
    new_n1.m_flipped = flipped;
    m_state.m_entries.insert(e1, new_n1);

    buffer<expr> parents_to_propagate;
    /* The hash code for the parents is going to change */
    remove_parents(e1_root, parents_to_propagate);

    buffer<expr> lambdas1, lambdas2;
    get_eqc_lambdas(e1_root, lambdas1);
    get_eqc_lambdas(e2_root, lambdas2);
    buffer<expr> fn_roots1, fn_roots2;
    if (!lambdas1.empty()) collect_fn_roots(e2_root, fn_roots2);
    if (!lambdas2.empty()) collect_fn_roots(e1_root, fn_roots1);

    /* force all m_root fields in e1 equivalence class to point to e2_root */
    bool propagate = is_true_or_false(e2_root);
    buffer<expr> to_propagate;
    expr it = e1;
    do {
        auto it_n = get_entry(it);
        if (propagate)
            to_propagate.push_back(it);
        lean_assert(it_n);
        entry new_it_n   = *it_n;
        new_it_n.m_root = e2_root;
        m_state.m_entries.insert(it, new_it_n);
        it = new_it_n.m_next;
    } while (it != e1);

    reinsert_parents(e1_root);

    // update next of e1_root and e2_root, ac representative, and size of e2_root
    r1 = get_entry(e1_root);
    r2 = get_entry(e2_root);
    lean_assert(r1 && r2);
    lean_assert(r1->m_root == e2_root);

    entry new_r1          = *r1;
    entry new_r2          = *r2;
    new_r1.m_next         = r2->m_next;
    new_r2.m_next         = r1->m_next;
    new_r2.m_size        += r1->m_size;
    new_r2.m_has_lambdas |= r1->m_has_lambdas;
    optional<expr> ac_var1 = r1->m_ac_var;
    optional<expr> ac_var2 = r2->m_ac_var;
    if (!ac_var2)
        new_r2.m_ac_var    = ac_var1;
    if (heq_proof)
        new_r2.m_heq_proofs = true;
    m_state.m_entries.insert(e1_root, new_r1);
    m_state.m_entries.insert(e2_root, new_r2);
    lean_assert(check_invariant());

    buffer<expr> lambda_apps_to_internalize;
    propagate_beta_to_eqc(fn_roots2, lambdas1, lambda_apps_to_internalize);
    propagate_beta_to_eqc(fn_roots1, lambdas2, lambda_apps_to_internalize);

    // copy e1_root parents to e2_root
    auto ps1 = m_state.m_parents.find(e1_root);
    if (ps1) {
        parent_occ_set ps2;
        if (auto it = m_state.m_parents.find(e2_root))
            ps2 = *it;
        ps1->for_each([&](parent_occ const & p) {
                if (!is_app(p.m_expr) || is_congr_root(p.m_expr)) {
                    if (!constructor_eq && r2->m_constructor)  {
                        propagate_projection_constructor(p.m_expr, e2_root);
                    }
                    ps2.insert(p);
                }
            });
        m_state.m_parents.erase(e1_root);
        m_state.m_parents.insert(e2_root, ps2);
    }

    if (!m_state.m_inconsistent && ac_var1 && ac_var2)
        m_ac.add_eq(*ac_var1, *ac_var2);

    if (!m_state.m_inconsistent && constructor_eq)
        propagate_constructor_eq(e1_root, e2_root);

    if (!m_state.m_inconsistent && value_inconsistency)
        propagate_value_inconsistency(e1_root, e2_root);

    if (!m_state.m_inconsistent) {
        update_mt(e2_root);
        check_new_subsingleton_eq(e1_root, e2_root);
    }

    if (!m_state.m_inconsistent) {
        for (expr const & p : parents_to_propagate)
            propagate_up(p);
    }

    if (!m_state.m_inconsistent && !to_propagate.empty()) {
        for (expr const & e : to_propagate)
            propagate_down(e);
        if (m_phandler)
            m_phandler->propagated(to_propagate);
    }

    if (!m_state.m_inconsistent) {
        for (expr const & e : lambda_apps_to_internalize) {
            internalize_core(e, none_expr(), get_generation_of(e));
        }
    }

    lean_trace(name({"cc", "merge"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               tout() << e1_root << " = " << e2_root << "\n";);
    lean_trace(name({"debug", "cc"}), scope_trace_env scope(m_ctx.env(), m_ctx);
               auto out = tout();
               auto fmt = out.get_formatter();
               out << "merged: " << e1_root << " = " << e2_root << "\n";
               out << m_state.pp_eqcs(fmt) << "\n";
               if (is_trace_class_enabled(name{"debug", "cc", "parent_occs"}))
                   out << m_state.pp_parent_occs(fmt) << "\n";
               out << "--------\n";);
}

void congruence_closure::process_todo() {
    while (!m_todo.empty()) {
        if (m_state.m_inconsistent) {
            m_todo.clear();
            return;
        }
        expr lhs, rhs, H; bool heq_proof;
        std::tie(lhs, rhs, H, heq_proof) = m_todo.back();
        m_todo.pop_back();
        add_eqv_step(lhs, rhs, H, heq_proof);
    }
}

void congruence_closure::add_eqv_core(expr const & lhs, expr const & rhs, expr const & H, bool heq_proof) {
    push_todo(lhs, rhs, H, heq_proof);
    process_todo();
}

void congruence_closure::add(expr const & type, expr const & proof, unsigned gen) {
    if (m_state.m_inconsistent) return;
    m_todo.clear();
    expr p      = type;
    bool is_neg = is_not_or_ne(type, p);
    expr lhs, rhs;
    if (is_eq(type, lhs, rhs) || is_heq(type, lhs, rhs)) {
        if (is_neg) {
            bool heq_proof    = false;
            internalize_core(p, none_expr(), gen);
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, proof), heq_proof);
        } else {
            bool heq_proof    = is_heq(type);
            internalize_core(lhs, none_expr(), gen);
            internalize_core(rhs, none_expr(), gen);
            add_eqv_core(lhs, rhs, proof, heq_proof);
        }
    } else if (is_iff(type, lhs, rhs)) {
        bool heq_proof    = false;
        if (is_neg) {
            expr neq_proof = mk_neq_of_not_iff(m_ctx, proof);
            internalize_core(p, none_expr(), gen);
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, neq_proof), heq_proof);
        } else {
            internalize_core(lhs, none_expr(), gen);
            internalize_core(rhs, none_expr(), gen);
            add_eqv_core(lhs, rhs, mk_propext(lhs, rhs, proof), heq_proof);
        }
    } else if (is_neg || m_ctx.is_prop(p)) {
        bool heq_proof    = false;
        internalize_core(p, none_expr(), gen);
        if (is_neg) {
            add_eqv_core(p, mk_false(), mk_eq_false_intro(m_ctx, proof), heq_proof);
        } else {
            add_eqv_core(p, mk_true(), mk_eq_true_intro(m_ctx, proof), heq_proof);
        }
    }
}

bool congruence_closure::is_eqv(expr const & e1, expr const & e2) const {
    auto n1 = get_entry(e1);
    if (!n1) return false;
    auto n2 = get_entry(e2);
    if (!n2) return false;
    /* Remark: this method assumes that is_eqv is invoked with type correct parameters.
       An eq class may contain equality and heterogeneous equality proofs is enabled.
       When this happens, the answer is correct only if e1 and e2 have the same type. */
    return n1->m_root == n2->m_root;
}

bool congruence_closure::is_not_eqv(expr const & e1, expr const & e2) const {
    try {
        expr tmp = mk_eq(m_ctx, e1, e2);
        if (is_eqv(tmp, mk_false()))
            return true;
        tmp = mk_heq(m_ctx, e1, e2);
        return is_eqv(tmp, mk_false());
    } catch (app_builder_exception &) {
        return false;
    }
}

bool congruence_closure::proved(expr const & e) const {
    return is_eqv(e, mk_true());
}

void congruence_closure::internalize(expr const & e, unsigned gen) {
    internalize_core(e, none_expr(), gen);
    process_todo();
}

optional<expr> congruence_closure::get_inconsistency_proof() const {
    lean_assert(!m_state.m_froze_partitions);
    try {
        if (auto p = get_eq_proof(mk_true(), mk_false())) {
            return some_expr(mk_false_of_true_eq_false(m_ctx, *p));
        } else {
            return none_expr();
        }
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool congruence_closure::state::check_eqc(expr const & e) const {
    expr root     = get_root(e);
    unsigned size = 0;
    expr it       = e;
    do {
        auto it_n = m_entries.find(it);
        lean_assert(it_n);
        lean_assert(it_n->m_root == root);
        auto it2  = it;
        // following m_target fields should lead to root
        while (true) {
            auto it2_n = m_entries.find(it2);
            if (!it2_n->m_target)
                break;
            it2 = *it2_n->m_target;
        }
        lean_assert(it2 == root);
        it = it_n->m_next;
        size++;
    } while (it != e);
    lean_assert(m_entries.find(root)->m_size == size);
    return true;
}

bool congruence_closure::state::check_invariant() const {
    m_entries.for_each([&](expr const & k, entry const & n) {
            if (k == n.m_root) {
                lean_assert(check_eqc(k));
            }
        });
    return true;
}

format congruence_closure::state::pp_eqc(formatter const & fmt, expr const & e) const {
    format r;
    bool first = true;
    expr it = e;
    do {
        auto it_n = m_entries.find(it);
        if (first) first = false; else r += comma() + line();
        format fmt_it = fmt(it);
        if (is_pi(it) || is_lambda(it) || is_let(it))
            fmt_it = paren(fmt_it);
        r += fmt_it;
        it = it_n->m_next;
    } while (it != e);
    return bracket("{", group(r), "}");
}

bool congruence_closure::state::in_singleton_eqc(expr const & e) const {
    if (auto it = m_entries.find(e))
        return it->m_next == e;
    return  true;
}

format congruence_closure::state::pp_eqcs(formatter const & fmt, bool nonsingleton_only) const {
    buffer<expr> roots;
    get_roots(roots, nonsingleton_only);
    format r;
    bool first = true;
    for (expr const & root : roots) {
        if (first) first = false; else r += comma() + line();
        r += pp_eqc(fmt, root);
    }
    return bracket("{", group(r), "}");
}

format congruence_closure::state::pp_parent_occs(formatter const & fmt, expr const & e) const {
    format r = fmt(e) + line() + format(":=") + line();
    format ps;
    if (parent_occ_set const * poccs = m_parents.find(e)) {
        bool first = true;
        poccs->for_each([&](parent_occ const & o) {
                if (first) first = false; else ps += comma() + line();
                ps += fmt(o.m_expr);
            });
    }
    return group(r + bracket("{", group(ps), "}"));
}

format congruence_closure::state::pp_parent_occs(formatter const & fmt) const {
    format r;
    bool first = true;
    m_parents.for_each([&](expr const & k, parent_occ_set const &) {
            if (first) first = false; else r += comma() + line();
            r += pp_parent_occs(fmt, k);
        });
    return group(bracket("{", group(r), "}"));
}

void initialize_congruence_closure() {
    register_trace_class("cc");
    register_trace_class({"cc", "failure"});
    register_trace_class({"cc", "merge"});
    register_trace_class({"debug", "cc"});
    register_trace_class({"debug", "cc", "parent_occs"});

    name prefix     = name::mk_internal_unique_name();
    g_congr_mark    = new expr(mk_constant(name(prefix, "[congruence]")));
    g_eq_true_mark  = new expr(mk_constant(name(prefix, "[iff-true]")));
    g_refl_mark     = new expr(mk_constant(name(prefix, "[refl]")));

    g_iff_eq_of_eq_true_left  = new expr(mk_constant("iff_eq_of_eq_true_left"));
    g_iff_eq_of_eq_true_right = new expr(mk_constant("iff_eq_of_eq_true_right"));
    g_iff_eq_true_of_eq       = new expr(mk_constant("iff_eq_true_of_eq"));

    g_and_eq_of_eq_true_left   = new expr(mk_constant("and_eq_of_eq_true_left"));
    g_and_eq_of_eq_true_right  = new expr(mk_constant("and_eq_of_eq_true_right"));
    g_and_eq_of_eq_false_left  = new expr(mk_constant("and_eq_of_eq_false_left"));
    g_and_eq_of_eq_false_right = new expr(mk_constant("and_eq_of_eq_false_right"));
    g_and_eq_of_eq             = new expr(mk_constant("and_eq_of_eq"));

    g_or_eq_of_eq_true_left   = new expr(mk_constant("or_eq_of_eq_true_left"));
    g_or_eq_of_eq_true_right  = new expr(mk_constant("or_eq_of_eq_true_right"));
    g_or_eq_of_eq_false_left  = new expr(mk_constant("or_eq_of_eq_false_left"));
    g_or_eq_of_eq_false_right = new expr(mk_constant("or_eq_of_eq_false_right"));
    g_or_eq_of_eq             = new expr(mk_constant("or_eq_of_eq"));

    g_not_eq_of_eq_true       = new expr(mk_constant("not_eq_of_eq_true"));
    g_not_eq_of_eq_false      = new expr(mk_constant("not_eq_of_eq_false"));
    g_false_of_a_eq_not_a     = new expr(mk_constant("false_of_a_eq_not_a"));

    g_imp_eq_of_eq_true_left  = new expr(mk_constant("imp_eq_of_eq_true_left"));
    g_imp_eq_of_eq_false_left = new expr(mk_constant("imp_eq_of_eq_false_left"));
    g_imp_eq_of_eq_true_right = new expr(mk_constant("imp_eq_of_eq_true_right"));
    g_imp_eq_true_of_eq       = new expr(mk_constant("imp_eq_true_of_eq"));

    g_not_imp_eq_of_eq_false_right = new expr(mk_constant("not_imp_eq_of_eq_false_right"));
    g_imp_eq_of_eq_false_right     = new expr(mk_constant("imp_eq_of_eq_false_right"));

    g_if_eq_of_eq_true  = new name("if_eq_of_eq_true");
    g_if_eq_of_eq_false = new name("if_eq_of_eq_false");
    g_if_eq_of_eq       = new name("if_eq_of_eq");

    g_eq_true_of_and_eq_true_left  = new expr(mk_constant("eq_true_of_and_eq_true_left"));
    g_eq_true_of_and_eq_true_right = new expr(mk_constant("eq_true_of_and_eq_true_right"));

    g_eq_false_of_or_eq_false_left  = new expr(mk_constant("eq_false_of_or_eq_false_left"));
    g_eq_false_of_or_eq_false_right = new expr(mk_constant("eq_false_of_or_eq_false_right"));

    g_eq_false_of_not_eq_true = new expr(mk_constant("eq_false_of_not_eq_true"));
    g_eq_true_of_not_eq_false = new expr(mk_constant("eq_true_of_not_eq_false"));

    g_ne_of_eq_of_ne   = new name("ne_of_eq_of_ne");
    g_ne_of_ne_of_eq   = new name("ne_of_ne_of_eq");
}

void finalize_congruence_closure() {
    delete g_congr_mark;
    delete g_eq_true_mark;
    delete g_refl_mark;

    delete g_iff_eq_of_eq_true_left;
    delete g_iff_eq_of_eq_true_right;
    delete g_iff_eq_true_of_eq;

    delete g_and_eq_of_eq_true_left;
    delete g_and_eq_of_eq_true_right;
    delete g_and_eq_of_eq_false_left;
    delete g_and_eq_of_eq_false_right;
    delete g_and_eq_of_eq;

    delete g_or_eq_of_eq_true_left;
    delete g_or_eq_of_eq_true_right;
    delete g_or_eq_of_eq_false_left;
    delete g_or_eq_of_eq_false_right;
    delete g_or_eq_of_eq;

    delete g_not_eq_of_eq_true;
    delete g_not_eq_of_eq_false;
    delete g_false_of_a_eq_not_a;

    delete g_imp_eq_of_eq_true_left;
    delete g_imp_eq_of_eq_false_left;
    delete g_imp_eq_of_eq_true_right;
    delete g_imp_eq_true_of_eq;

    delete g_not_imp_eq_of_eq_false_right;
    delete g_imp_eq_of_eq_false_right;

    delete g_if_eq_of_eq_true;
    delete g_if_eq_of_eq_false;
    delete g_if_eq_of_eq;

    delete g_eq_true_of_and_eq_true_left;
    delete g_eq_true_of_and_eq_true_right;

    delete g_eq_false_of_or_eq_false_left;
    delete g_eq_false_of_or_eq_false_right;

    delete g_eq_false_of_not_eq_true;
    delete g_eq_true_of_not_eq_false;

    delete g_ne_of_eq_of_ne;
    delete g_ne_of_ne_of_eq;
}
}




// ========== congruence_tactics.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
bool is_cc_state(vm_obj const & o);
congruence_closure::state const & to_cc_state(vm_obj const & o);
vm_obj to_obj(congruence_closure::state const & s);

tactic_state update_defeq_canonizer_state(tactic_state const & s, congruence_closure const & cc);

void initialize_congruence_tactics();
void finalize_congruence_tactics();
}




// ========== congruence_tactics.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "library/io_state.h"
#include "library/util.h"
#include "library/app_builder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/tactic/smt/ematch.h"

namespace lean {
struct vm_cc_state : public vm_external {
    congruence_closure::state m_val;
    vm_cc_state(congruence_closure::state const & v):m_val(v) {}
    virtual ~vm_cc_state() {}
    virtual void dealloc() override {
        this->~vm_cc_state(); get_vm_allocator().deallocate(sizeof(vm_cc_state), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_cc_state(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(m_val); }
};

bool is_cc_state(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_cc_state*>(to_external(o));
}

congruence_closure::state const & to_cc_state(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_cc_state*>(to_external(o)));
    return static_cast<vm_cc_state*>(to_external(o))->m_val;
}

vm_obj to_obj(congruence_closure::state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_cc_state))) vm_cc_state(s));
}

/*
structure cc_config :=
(ignore_instances : bool)
(ac               : bool)
(ho_fns           : option (list name))
(em               : bool)
*/
pair<name_set, congruence_closure::config> to_ho_fns_cc_config(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    c.m_ignore_instances = to_bool(cfield(cfg, 0));
    c.m_ac               = to_bool(cfield(cfg, 1));
    if (is_none(cfield(cfg, 2))) {
        c.m_all_ho       = true;
    } else {
        c.m_all_ho       = false;
        ho_fns           = to_name_set(to_list_name(get_some_value(cfield(cfg, 2))));
    }
    c.m_em               = to_bool(cfield(cfg, 3));
    return mk_pair(ho_fns, c);
}

static congruence_closure::state mk_core(vm_obj const & cfg) {
    congruence_closure::config c;
    name_set ho_fns;
    std::tie(ho_fns, c) = to_ho_fns_cc_config(cfg);
    return congruence_closure::state(ho_fns, c);
}

vm_obj cc_state_mk_core(vm_obj const & cfg) {
    return to_obj(mk_core(cfg));
}

vm_obj cc_state_mk_using_hs_core(vm_obj const & cfg, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        local_context lctx          = g->get_context();
        type_context_old ctx            = mk_type_context_for(s);
        defeq_can_state dcs         = s.dcs();
        congruence_closure::state r = mk_core(cfg);
        congruence_closure cc(ctx, r, dcs);
        lctx.for_each([&](local_decl const & d) {
                if (ctx.is_prop(d.get_type())) {
                    cc.add(d.get_type(), d.mk_ref(), 0);
                }
            });
        tactic_state new_s = set_dcs(s, dcs);
        return tactic::mk_success(to_obj(r), new_s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj cc_state_pp_core(vm_obj const & ccs, vm_obj const & nonsingleton, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqcs(fmt, to_bool(nonsingleton));
    return tactic::mk_success(to_obj(r), s);
}

vm_obj cc_state_pp_eqc(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    type_context_old ctx         = mk_type_context_for(s);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt            = fmtf(s.env(), s.get_options(), ctx);
    format r                 = to_cc_state(ccs).pp_eqc(fmt, to_expr(e));
    return tactic::mk_success(to_obj(r), s);
}

vm_obj cc_state_next(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_next(to_expr(e)));
}

vm_obj cc_state_root(vm_obj const & ccs, vm_obj const & e) {
    return to_obj(to_cc_state(ccs).get_root(to_expr(e)));
}

vm_obj cc_state_is_cg_root(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_bool(to_cc_state(ccs).is_congr_root(to_expr(e)));
}

vm_obj cc_state_roots_core(vm_obj const & ccs, vm_obj const & nonsingleton) {
    buffer<expr> roots;
    to_cc_state(ccs).get_roots(roots, to_bool(nonsingleton));
    return to_obj(roots);
}

vm_obj cc_state_inconsistent(vm_obj const & ccs) {
    return mk_vm_bool(to_cc_state(ccs).inconsistent());
}

vm_obj cc_state_mt(vm_obj const & ccs, vm_obj const & e) {
    return mk_vm_nat(to_cc_state(ccs).get_mt(to_expr(e)));
}

vm_obj cc_state_gmt(vm_obj const & ccs) {
    return mk_vm_nat(to_cc_state(ccs).get_gmt());
}

vm_obj cc_state_inc_gmt(vm_obj const & ccs) {
    congruence_closure::state s = to_cc_state(ccs);
    s.inc_gmt();
    return to_obj(s);
}

#define cc_state_proc(CODE)                                     \
    tactic_state const & s   = tactic::to_state(_s);             \
    try {                                                       \
        type_context_old ctx            = mk_type_context_for(s);   \
        congruence_closure::state S = to_cc_state(ccs);         \
        defeq_can_state dcs         = s.dcs();                  \
        congruence_closure cc(ctx, S, dcs);                     \
        CODE                                                    \
    } catch (exception & ex) {                                  \
        return tactic::mk_exception(ex, s);                      \
    }

#define cc_state_updt_proc(CODE) cc_state_proc({ CODE; return tactic::mk_success(to_obj(S), set_dcs(s, dcs)); })

vm_obj cc_state_add(vm_obj const & ccs, vm_obj const & H, vm_obj const & _s) {
    cc_state_updt_proc({
            expr type                   = ctx.infer(to_expr(H));
            if (!ctx.is_prop(type))
                return tactic::mk_exception("cc_state.add failed, given expression is not a proof term", s);
            cc.add(type, to_expr(H), 0);
    });
}

vm_obj cc_state_internalize(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_updt_proc({
            cc.internalize(to_expr(e), 0);
        });
}

vm_obj cc_state_is_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_is_not_eqv(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            bool r = cc.is_not_eqv(to_expr(e1), to_expr(e2));
            return tactic::mk_success(mk_vm_bool(r), s);
        });
}

vm_obj cc_state_eqv_proof(vm_obj const & ccs, vm_obj const & e1, vm_obj const & e2, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_proof(to_expr(e1), to_expr(e2))) {
                return tactic::mk_success(to_obj(*r), s);
            } else {
                return tactic::mk_exception("cc_state.eqv_proof failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_true())) {
                return tactic::mk_success(to_obj(mk_of_eq_true(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_proof_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_refutation_for(vm_obj const & ccs, vm_obj const & e, vm_obj const & _s) {
    cc_state_proc({
            if (optional<expr> r = cc.get_eq_proof(to_expr(e), mk_false())) {
                return tactic::mk_success(to_obj(mk_not_of_eq_false(cc.ctx(), *r)), s);
            } else {
                return tactic::mk_exception("cc_state.get_refutation_for failed to build proof", s);
            }
        });
}

vm_obj cc_state_proof_for_false(vm_obj const & ccs, vm_obj const & _s) {
    cc_state_proc({
            if (auto pr = cc.get_inconsistency_proof()) {
                return tactic::mk_success(to_obj(*pr), s);
            } else {
                return tactic::mk_exception("cc_state.false_proof failed, state is not inconsistent", s);
            }
        });
}

void initialize_congruence_tactics() {
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_core"}),              cc_state_mk_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "mk_using_hs_core"}),     cc_state_mk_using_hs_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_core"}),              cc_state_pp_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "pp_eqc"}),               cc_state_pp_eqc);
    DECLARE_VM_BUILTIN(name({"cc_state", "next"}),                 cc_state_next);
    DECLARE_VM_BUILTIN(name({"cc_state", "root"}),                 cc_state_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "mt"}),                   cc_state_mt);
    DECLARE_VM_BUILTIN(name({"cc_state", "gmt"}),                  cc_state_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "inc_gmt"}),              cc_state_inc_gmt);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_cg_root"}),           cc_state_is_cg_root);
    DECLARE_VM_BUILTIN(name({"cc_state", "roots_core"}),           cc_state_roots_core);
    DECLARE_VM_BUILTIN(name({"cc_state", "internalize"}),          cc_state_internalize);
    DECLARE_VM_BUILTIN(name({"cc_state", "add"}),                  cc_state_add);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_eqv"}),               cc_state_is_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "is_not_eqv"}),           cc_state_is_not_eqv);
    DECLARE_VM_BUILTIN(name({"cc_state", "inconsistent"}),         cc_state_inconsistent);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for_false"}),      cc_state_proof_for_false);
    DECLARE_VM_BUILTIN(name({"cc_state", "eqv_proof"}),            cc_state_eqv_proof);
    DECLARE_VM_BUILTIN(name({"cc_state", "proof_for"}),            cc_state_proof_for);
    DECLARE_VM_BUILTIN(name({"cc_state", "refutation_for"}),       cc_state_refutation_for);
}

void finalize_congruence_tactics() {
}
}




// ========== init_module.h ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
void initialize_smt_module();
void finalize_smt_module();
}




// ========== init_module.cpp ==========

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/smt/util.h"
#include "library/tactic/smt/congruence_closure.h"
#include "library/tactic/smt/congruence_tactics.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/tactic/smt/ematch.h"
#include "library/tactic/smt/theory_ac.h"
#include "library/tactic/smt/smt_state.h"

namespace lean {
void initialize_smt_module() {
    initialize_smt_util();
    initialize_congruence_closure();
    initialize_congruence_tactics();
    initialize_hinst_lemmas();
    initialize_ematch();
    initialize_theory_ac();
    initialize_smt_state();
}

void finalize_smt_module() {
    finalize_smt_state();
    finalize_theory_ac();
    finalize_ematch();
    finalize_hinst_lemmas();
    finalize_congruence_tactics();
    finalize_congruence_closure();
    finalize_smt_util();
}
}

