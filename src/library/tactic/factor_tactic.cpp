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
#include "library/trace.h"
#include "library/constants.h"
#include "library/vm/vm_string.h"
#include <string>

namespace lean {

std::string exec(const char* cmd) {
    char buffer[128];
    std::string result = "";
    std::shared_ptr<FILE> pipe(popen(cmd, "r"), pclose);
    if (!pipe) throw std::runtime_error("popen() failed!");
    while (!feof(pipe.get())) {
        if (fgets(buffer, 128, pipe.get()) != NULL)
            result += buffer;
    }
    return result;
}
  
  
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

  vm_obj factor_string(std::string fac_str, expr tp, tactic_state const & s) {
    //lean_assert(is_local(H));
        optional<expr> mvar  = s.get_main_goal();
        if (!mvar) return mk_no_goals_exception(s);
        metavar_context  mctx = s.mctx();
        optional<metavar_decl> g   = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        local_context  lctx         = g->get_context();

	type_context tctx = mk_type_context_for(s, lctx);

	std::string st =
	  "Forall[q, nat, Forall[z, nat, Eq[Mul[Add[2, z], q], Add[Mul[2, q], Mul[z, q]]]]]";

	st = "Forall[q, nat, Exists[z, nat, And[Eq[Add[z, 1], q], Eq[q, z]]]]";
	//	st = "Forall[q, nat, Eq[Mul[Add[2, 2], q], q]]";
	st = fac_str;
	std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>();
	//mapl["x"] = mk_local(name("x"), tctx.infer(H));
	//mapl["y"] = mk_local(name("y"), tctx.infer(H));
	mapl["nat"] = tctx.infer(tp); //mk_constant(get_nat_name(), {level(level())});
	//std::cout << "make add: " << mk_add(tctx, mapl["x"], mapl["y"]);
	expr dummy = mk_var(0);
	mapl["Forall"] = dummy;
	mapl["Exists"] = dummy;
	mapl["Add"] = dummy;
	mapl["Mul"] = dummy;
	mapl["Eq"] = dummy;
	mapl["And"] = mk_constant(get_and_name(), {});
	mapl["Or"] = mk_constant(get_or_name(), {});
	mapl["Not"] = mk_constant(get_not_name(), {});
	mapl["Implies"] = mk_constant(get_implies_name(), {});
	auto wl = wolfram_to_lean(tctx, st, mapl);
	tout() << "translated " << st << " to lean expression:\n\n";
	tout() << wl << "\n\n";
	//std::cout << "full form:\n\n" << wl << "\n\n";
    try {
	return mk_tactic_success(to_obj(wl), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

  vm_obj clearf(expr const & H, expr const & H2, tactic_state const & s) {
    //lean_assert(is_local(H));
        optional<expr> mvar  = s.get_main_goal();
        if (!mvar) return mk_no_goals_exception(s);
        metavar_context  mctx = s.mctx();
        optional<metavar_decl> g   = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        local_context  lctx         = g->get_context();

	type_context tctx = mk_type_context_for(s, lctx);

	std::string st =
	  "Forall[q, nat, Forall[z, nat, Eq[Mul[Add[2, z], q], Add[Mul[2, q], Mul[z, q]]]]]";

	st = "Forall[q, nat, Exists[z, nat, And[Eq[Add[z, 1], q], Eq[q, z]]]]";
	//	st = "Forall[q, nat, Eq[Mul[Add[2, 2], q], q]]";
	std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>();
	//mapl["x"] = mk_local(name("x"), tctx.infer(H));
	//mapl["y"] = mk_local(name("y"), tctx.infer(H));
	mapl["nat"] = tctx.infer(H);
	//std::cout << "make add: " << mk_add(tctx, mapl["x"], mapl["y"]);
	expr dummy = mk_var(0);
	mapl["Forall"] = dummy;
	mapl["Exists"] = dummy;
	mapl["Add"] = dummy;
	mapl["Mul"] = dummy;
	mapl["Eq"] = dummy;
	mapl["And"] = mk_constant(get_and_name(), {});
	mapl["Or"] = mk_constant(get_or_name(), {});
	mapl["Not"] = mk_constant(get_not_name(), {});
	mapl["Implies"] = mk_constant(get_implies_name(), {});
	auto wl = wolfram_to_lean(tctx, st, mapl);
	tout() << "translated " << st << " to lean expression:\n\n";
	tout() << wl << "\n\n";
	std::cout << "full form:\n\n" << wl << "\n\n";

	std::cout << "does this make sense? " << tctx.check(wl) << "\n";
	
        expr new_mvar        = clearf(mctx, *mvar, H);
    try {
    if (!is_local(H))
        return mk_tactic_exception(sstream() << "clear tactic failed, given expression is not a local constant",
                                   s);
    //        return mk_tactic_success(set_mctx_goals(s, mctx, cons(new_mvar, tail(s.goals()))));
	return mk_tactic_success(to_obj(wl), s);
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

  vm_obj print_wl(expr e1, tactic_state const & s) {
    //    auto tc = mk_type_checker(const lean::environment &env);
    //lean_assert(is_local(H));
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return mk_no_goals_exception(s);
    metavar_context  mctx = s.mctx();
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context  lctx         = g->get_context();

    type_context tctx = mk_type_context_for(s, lctx);

    auto str = lean_to_wolfram(e1);
    std::cout << "Translated: " << e1 << "\n\nTo: " << str << "\n\n";
    std::string cmd = "WolframScript -script ~/translator/factor_script.m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());
    std::cout << "And back: " << output << "\n";

    
    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>();
    mapl["nat"] = mk_constant(get_nat_name());
    mapl["x"] = mk_local(name("x"), mapl["nat"]);
    mapl["y"] = mk_local(name("y"), mapl["nat"]);
    //std::cout << "make add: " << mk_add(tctx, mapl["x"], mapl["y"]);
    expr dummy = mk_var(0);
    mapl["Forall"] = dummy;
    mapl["Exists"] = dummy;
    mapl["Plus"] = dummy;
    mapl["Times"] = dummy;
    mapl["Eq"] = dummy;
    mapl["And"] = mk_constant(get_and_name(), {});
    mapl["Or"] = mk_constant(get_or_name(), {});
    mapl["Not"] = mk_constant(get_not_name(), {});
    mapl["Implies"] = mk_constant(get_implies_name(), {});
    
    std::cout << "lean term: " << wolfram_to_lean(tctx, output, mapl);
    return mk_tactic_success(s);
  }
  

  vm_obj tactic_translate_to_wl_test(vm_obj const & e0, vm_obj const & s) {
    
    const ::lean::expr e1 = to_expr(e0);
    return print_wl(e1, to_tactic_state(s));
}
  
  vm_obj tactic_translate_test(vm_obj const & e0, vm_obj const & tp, vm_obj const & s) {
    
    std::string e = to_string(e0);
    const ::lean::expr e1 = to_expr(tp);
    return factor_string(e, e1, to_tactic_state(s));
}

  vm_obj tactic_factor(vm_obj const & e0, vm_obj const & s0) {
    //    auto tc = mk_type_checker(const lean::environment &env);
    //lean_assert(is_local(H));
    expr e1 = to_expr(e0);
    tactic_state s = to_tactic_state(s0);
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return mk_no_goals_exception(s);
    metavar_context  mctx = s.mctx();
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context  lctx         = g->get_context();

    type_context tctx = mk_type_context_for(s, lctx);

    auto pr = lean_to_wolfram(e1, true);
    auto str = pr.first;
    std::cout << "Translated: " << e1 << "\n\nTo: " << str << "\n\n";
    std::string cmd = "WolframScript -script ~/translator/factor_script.m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());
    std::cout << "And back: " << output << "\n";

    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>(pr.second);
    mapl["nat"] = mk_constant(get_nat_name());
    mapl["x"] = mk_local(name("x"), mapl["nat"]);
    mapl["y"] = mk_local(name("y"), mapl["nat"]);
    expr dummy = mk_var(0);
    mapl["Forall"] = dummy;
    mapl["Exists"] = dummy;
    mapl["Plus"] = dummy;
    mapl["Times"] = dummy;
    mapl["Eq"] = dummy;
    mapl["And"] = mk_constant(get_and_name(), {});
    mapl["Or"] = mk_constant(get_or_name(), {});
    mapl["Not"] = mk_constant(get_not_name(), {});
    mapl["Implies"] = mk_constant(get_implies_name(), {});
    try {
      expr wlt = wolfram_to_lean(tctx, output, mapl);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
    }
  }

void initialize_factor_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "translate_to_wl_test"}),    tactic_translate_to_wl_test);
    DECLARE_VM_BUILTIN(name({"tactic", "translate_test"}),    tactic_translate_test);
    DECLARE_VM_BUILTIN(name({"tactic", "factor"}),    tactic_factor);
}

void finalize_factor_tactic() {
}
}
