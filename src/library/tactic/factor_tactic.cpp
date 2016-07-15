/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/wolfram.h"
#include "library/app_builder.h"
#include "library/util.h"
#include "library/type_context.h"
#include <string>

namespace lean {
expr clearf(metavar_context & mctx, expr const & mvar, expr const & H) {
  /*std::string st = "Mul[Add[2, x], y] [nar] ";
  std::cout << "!!!\n";
  std::cout << wolfram_to_expr(st).to_string() << "\n";*/
    lean_assert(is_metavar(mvar));
    lean_assert(is_local(H));
    optional<metavar_decl> g   = mctx.get_metavar_decl(mvar);
    if (!g) throw exception("clear tactic failed, there are no goals to be solved");
    local_context lctx         = g->get_context();
    optional<local_decl> d     = lctx.get_local_decl(H);
    if (!d)
        throw exception(sstream() << "clear tactic failed, unknown '" << local_pp_name(H) << "' hypothesis");
    if (depends_on(g->get_type(), 1, &H))
        throw exception(sstream() << "clear tactic failed, target type depends on '" << local_pp_name(H) << "'");
    if (optional<local_decl> d2 = lctx.has_dependencies(*d))
        throw exception(sstream() << "clear tactic failed, hypothesis '" << d2->get_pp_name() << "' depends on '" << local_pp_name(H) << "'");
    lctx.clear(*d);
    expr new_mvar              = mctx.mk_metavar_decl(lctx, g->get_type());
    mctx.assign(mvar, new_mvar);
    return new_mvar;
}

  vm_obj clearf(expr const & H, expr const & H2, tactic_state const & s) {
    //lean_assert(is_local(H));
        optional<expr> mvar  = s.get_main_goal();
        if (!mvar) return mk_no_goals_exception(s);
        metavar_context  mctx = s.mctx();
        optional<metavar_decl> g   = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        local_context  lctx         = g->get_context();
	//	std::cout << "in clearf 2!\n";
	//type_context_cache const tcc = type_context_cache(s.env(), options());
	type_context tctx = mk_type_context_for(s, lctx);
	std::cout << H << ", " << H2 << "\n";
	auto addexpr = mk_mul(tctx, H, H2);
	std::cout << "addexpr: " << addexpr << "\n\n\n";

	std::string st = "Mul[Add[2, x], y]";

        auto wt = wolfram_to_tree(st);
	std::cout << "tree:\n" << wt.to_string() << "\n\n";

	std::cout << "to expression:\n" << wt.to_expr(tctx.infer(H), tctx);
	
        expr new_mvar        = clearf(mctx, *mvar, H);
    try {
    if (!is_local(H))
        return mk_tactic_exception(sstream() << "clear tactic failed, given expression is not a local constant",
                                   s);
        return mk_tactic_success(set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals()))));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj clearf_internal(name const & n, tactic_state const & s) {
     optional<metavar_decl> g   = s.get_main_goal_decl();
     if (!g) return mk_no_goals_exception(s);
     metavar_context mctx       = s.mctx();
     local_context lctx         = g->get_context();
     optional<local_decl> d     = lctx.get_local_decl(n);
     if (!d)
         return mk_tactic_exception(sstream() << "clear tactic failed, unknown '" << n << "' hypothesis", s);
     return clearf(d->mk_ref(), d->mk_ref(), s);
}

  vm_obj tactic_factor(vm_obj const & e0, vm_obj const & e01, vm_obj const & s) {
    std::cout << "add: ...\n";// << addexpr << "\n";
    const ::lean::expr & e = to_expr(e0);
    const ::lean::expr &e1 = to_expr(e01);
    return clearf(e, e1, to_tactic_state(s));
}

void initialize_factor_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "factor"}),    tactic_factor);
}

void finalize_factor_tactic() {
}
}
