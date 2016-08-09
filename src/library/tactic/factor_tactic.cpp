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
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/norm_num.h"
#include <string>
#include "library/tactic/elaborate.h"
#include "library/wl_mathlink.h"

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

  void fill_transl_map(std::unordered_map<std::string, expr> * mapl) {
    mapl->emplace("nat", mk_constant(get_nat_name()));
    expr dummy = mk_var(0);
    mapl->emplace("Forall", dummy);
    mapl->emplace("Exists", dummy);
    mapl->emplace("Plus", dummy);
    mapl->emplace("Times", dummy);
    mapl->emplace("Subtract", dummy);
    mapl->emplace("Divide", dummy);
    mapl->emplace("Negative", dummy);
    mapl->emplace("Equal", dummy);
    mapl->emplace("LeanApp", dummy);
    mapl->emplace("Power", dummy);
    mapl->emplace("ListCons", dummy);
    mapl->emplace("ListEnd", dummy);
    mapl->emplace("Rational", dummy);
    mapl->emplace("And", mk_constant(get_and_name(), {}));
    mapl->emplace("Or", mk_constant(get_or_name(), {}));
    mapl->emplace("Not", mk_constant(get_not_name(), {}));
    mapl->emplace("Implies", mk_constant(get_implies_name(), {}));
  }

  /*vm_obj factor_string(std::string fac_str, expr tp, tactic_state const & s) {
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
	mapl["Subtract"] = dummy;
	mapl["Divide"] = dummy;
	mapl["Negative"] = dummy;
	mapl["Eq"] = dummy;
	mapl["LeanApp"] = dummy;
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
    }*/

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
    /* std::string cmd = "WolframScript -script ~/translator/factor_script.m \\'" + str + "\\'";
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
    mapl["Subtract"] = dummy;
    mapl["Divide"] = dummy;
    mapl["Negative"] = dummy;
    mapl["Eq"] = dummy;
    mapl["LeanApp"] = dummy;
    mapl["And"] = mk_constant(get_and_name(), {});
    mapl["Or"] = mk_constant(get_or_name(), {});
    mapl["Not"] = mk_constant(get_not_name(), {});
    mapl["Implies"] = mk_constant(get_implies_name(), {});
    
    std::cout << "lean term: " << wolfram_to_lean(tctx, output, mapl);*/
    return mk_tactic_success(s);
  }
  

  vm_obj tactic_translate_to_wl_test(vm_obj const & e0, vm_obj const & s) {
    const ::lean::expr e1 = to_expr(e0);
    return print_wl(e1, to_tactic_state(s));
}
  
  /* vm_obj tactic_translate_test(vm_obj const & e0, vm_obj const & tp, vm_obj const & s) {
    
    std::string e = to_string(e0);
    const ::lean::expr e1 = to_expr(tp);
    return factor_string(e, e1, to_tactic_state(s));
    }*/

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
    //std::cout << "Translated: " << e1 << "\n\nTo: " << str << "\n\n";
    std::string cmd = "WolframScript -script ~/translator/factor_script.m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());
    //std::cout << "And back: " << output << "\n";

    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>(pr.second);
    /*mapl["nat"] = mk_constant(get_nat_name());
    mapl["x"] = mk_local(name("x"), mapl["nat"]);
    mapl["y"] = mk_local(name("y"), mapl["nat"]);
    expr dummy = mk_var(0);
    mapl["Forall"] = dummy;
    mapl["Exists"] = dummy;
    mapl["Plus"] = dummy;
    mapl["Times"] = dummy;
    mapl["Subtract"] = dummy;
    mapl["Divide"] = dummy;
    mapl["Negative"] = dummy;
    mapl["Eq"] = dummy;
    mapl["LeanApp"] = dummy;
    mapl["Power"] = dummy;
    mapl["And"] = mk_constant(get_and_name(), {});
    mapl["Or"] = mk_constant(get_or_name(), {});
    mapl["Not"] = mk_constant(get_not_name(), {});
    mapl["Implies"] = mk_constant(get_implies_name(), {});*/
    fill_transl_map(&mapl);
    try {
      expr wlt = wolfram_to_lean(tctx, output, mapl);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      std::cout << "wolfram to lean failed on: " << output << "\n";
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
    }
  }

  vm_obj tactic_wl_simplify(vm_obj const & e0, vm_obj const & s0) {
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
    //std::cout << "Translated: " << e1 << "\n\nTo: " << str << "\n\n";
    std::string cmd = "WolframScript -script ~/translator/simp_script.m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());
    //    std::cout << "And back: " << output << "\n";

    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>(pr.second);
    /*mapl["nat"] = mk_constant(get_nat_name());
    mapl["x"] = mk_local(name("x"), mapl["nat"]);
    mapl["y"] = mk_local(name("y"), mapl["nat"]);
    expr dummy = mk_var(0);
    mapl["Forall"] = dummy;
    mapl["Exists"] = dummy;
    mapl["Plus"] = dummy;
    mapl["Times"] = dummy;
    mapl["Subtract"] = dummy;
    mapl["Divide"] = dummy;
    mapl["Negative"] = dummy;
    mapl["Eq"] = dummy;
    mapl["Power"] = dummy;
    mapl["LeanApp"] = dummy;
    mapl["And"] = mk_constant(get_and_name(), {});
    mapl["Or"] = mk_constant(get_or_name(), {});
    mapl["Not"] = mk_constant(get_not_name(), {});
    mapl["Implies"] = mk_constant(get_implies_name(), {});*/
    fill_transl_map(&mapl);
    try {
      expr wlt = wolfram_to_lean(tctx, output, mapl);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
    }
  }

  vm_obj tactic_factor_int(vm_obj const & e0, vm_obj const & s0) {
    //    auto tc = mk_type_checker(const lean::environment &env);
    //lean_assert(is_local(H));
    auto e1 = try_to_unsigned(e0);
    tactic_state s = to_tactic_state(s0);
    //    auto nm = to_num(e1);
    if (!e1) {
      return mk_tactic_exception(sstream() << "bad input to factor_int tactic: " << e0, s);
    }
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return mk_no_goals_exception(s);
    metavar_context  mctx = s.mctx();
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context  lctx         = g->get_context();

    type_context tctx = mk_type_context_for(s, lctx);
    std::stringstream sst;
    sst << "WolframScript -script ~/translator/factor_int_script.m " << *e1;
    auto output = exec(sst.str().c_str());
    try {
      std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>();
      expr ntp = mk_constant(get_nat_name());
      mapl["Power"] = ntp;
      mapl["Times"] = ntp;
      expr wlt = wolfram_to_lean(tctx, output, mapl, ntp, true);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed in factor_int\n", s);
    }
  }

  vm_obj tactic_factor_matrix(vm_obj const & e0, vm_obj const & s0) {
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
    //std::cout << "Translated: " << e1 << "\n\nTo: " << str << "\n\n";
    std::cout << "started with: " << e1 << "\n";
    std::string cmd = "WolframScript -script ~/translator/list_simp_script.m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());
    std::cout << "And back: " << output << "\n";
    auto lvl = mctx.mk_univ_metavar_decl();
    auto tp = mctx.mk_metavar_decl(lctx, mk_sort(lvl));
    auto nile = mk_app(mk_constant(name("list", "nil"), {lvl}), tp);
    auto nate = mk_constant(get_nat_name());
    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>(pr.second);
    fill_transl_map(&mapl);
    mapl.emplace("ListNil", nile);
    mapl.emplace("x", mk_local(name("x"), nate));
    mapl.emplace("y", mk_local(name("y"), nate));
    try {
      auto strtest = "Or[Or[Equal[y, Power[Plus[-1, Power[x, 2]], Rational[1, 3]]], Equal[y, Times[Times[-1, Power[-1, Rational[1, 3]]], Power[Plus[-1, Power[x, 2]], Rational[1, 3]]]]], Equal[y, Times[Power[-1, Rational[2, 3]], Power[Plus[-1, Power[x, 2]], Rational[1, 3]]]]]";
    expr wlt1 = wolfram_to_lean(tctx, strtest, mapl, mk_constant(name("rat")), true);
    std::cout << "test:\n\n " << wlt1 << "\n\n";
    return mk_tactic_success(to_obj(wlt1), s);
      expr wlt = wolfram_to_lean(tctx, output, mapl, nate, true);
      std::cout << "finished with: " << wlt << "\n";
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      std::cout << "wolfram to lean failed on: " << output << "\n";
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
    }
  }

  vm_obj tactic_wl_execute_expr(vm_obj const & e0, vm_obj const & scr, vm_obj const & s0) {
    //    auto tc = mk_type_checker(const lean::environment &env);
    //lean_assert(is_local(H));
    expr e1 = to_expr(e0);
    auto script = to_string(scr);
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
    std::string cmd = "WolframScript -script ~/translator/" + script + ".m \\'" + str + "\\'";
    auto output = exec(cmd.c_str());

    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>(pr.second);
    fill_transl_map(&mapl);
    try {
      expr wlt = wolfram_to_lean(tctx, output, mapl);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
    }
  }

  vm_obj tactic_wl_execute_str(vm_obj const & e0, vm_obj const & scr, vm_obj const & s0) {
    //    auto tc = mk_type_checker(const lean::environment &env);
    //lean_assert(is_local(H));
    auto e1 = to_string(e0);
    auto script = to_string(scr);
    
    tactic_state s = to_tactic_state(s0);
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return mk_no_goals_exception(s);
    metavar_context  mctx = s.mctx();
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context  lctx         = g->get_context();

    type_context tctx = mk_type_context_for(s, lctx);

    //auto pr = lean_to_wolfram(e1, true);
    //auto str = pr.first;
    //std::string cmd = "WolframScript -script ~/translator/" + script + ".m \\'" + e1 + "\\'";
    //auto output = exec(cmd.c_str());

    std::unordered_map<std::string, expr> mapl = std::unordered_map<std::string, expr>();
    fill_transl_map(&mapl);
    expr e = wl_process_cmd(tctx, lctx, mapl, e1);
    /*try {
      expr wlt = wolfram_to_lean(tctx, output, mapl);
      return mk_tactic_success(to_obj(wlt), s);
    } catch (exception e) {
      return mk_tactic_exception(sstream() << "wolfram_to_lean failed\n", s);
      }*/
    return mk_tactic_success(to_obj(e), s);
  }
  
void initialize_factor_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "translate_to_wl_test"}),    tactic_translate_to_wl_test);
    // DECLARE_VM_BUILTIN(name({"tactic", "translate_test"}),    tactic_translate_test);
    DECLARE_VM_BUILTIN(name({"tactic", "factor"}),    tactic_factor);
    DECLARE_VM_BUILTIN(name({"tactic", "wl_simplify"}),    tactic_wl_simplify);
    DECLARE_VM_BUILTIN(name({"tactic", "factor_int"}), tactic_factor_int);
    DECLARE_VM_BUILTIN(name({"tactic", "factor_matrix"}), tactic_factor_matrix);
    DECLARE_VM_BUILTIN(name({"tactic", "wl_execute_expr"}), tactic_wl_execute_expr);
    DECLARE_VM_BUILTIN(name({"tactic", "wl_execute_str"}), tactic_wl_execute_str);
}

void finalize_factor_tactic() {
}
}
