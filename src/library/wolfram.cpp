/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/wolfram.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/norm_num.h"
#include "kernel/abstract.h"
#include <string>

namespace lean {
  /*

    typedef std::function<expr(expr, expr)> op;
    std::unordered_map<std::string, op> name_dict;
    name_dict["add"] = [](expr e1, expr e2) {return e1;};
*/

  expr fold(std::function<expr(type_context, expr, expr)> op,
	    buffer<w_term_tree> args, expr const & type, type_context m_tc) {
        //    std::cout << "folding! " << args.size() << "\n";
    if (args.size() == 1) {
      return to_expr(args[0], type, m_tc);
    }
    auto a1 = to_expr(args[0], type, m_tc);
    auto a2 = to_expr(args[1], type, m_tc);
    //std::cout << "have first two! of " << args.size() << " \n";
    expr val = op(m_tc, a1, a2);
    //std::cout << "made val. " << args.size() << "\n";
    for (int i = 2; i < args.size(); i++) {
      //  std::cout << "why am i in for loop?\n";
      val = op(m_tc, val, to_expr(args[i], type, m_tc));
    }
    std::cout << "have val to return\n";
    return val;
  }

  
  expr mk_mul2(type_context mtc, expr const & t1, expr const & t2) {
    return t1;
  }
  
  expr fold_add(
	    buffer<w_term_tree> const & nargs, expr const & type, type_context m_tc) {
    // auto op = [](type_context tc, expr e1, expr e2) {return lean::mk_add(tc, e1, e2);};
        //    std::cout << "folding! " << args.size() << "\n";
    auto args = buffer<w_term_tree>(nargs);
    if (args.size() == 1) {
      return to_expr(args[0], type, m_tc);
    }
    auto const & w1 = args[0];
    auto const & w2 = args[1];
    expr const a1 = to_expr(w1, type, m_tc);
    expr const a2 = to_expr(w2, type, m_tc);

    //return a1;
    //std::cout << "have first two! of " << args.size() << " \n";
    expr const & t = mk_add(m_tc, a1, a2);
    std::cout << "made t: " << t << ".\n";
    std::cout << "args contains:\n";
    for (int i = 0; i < args.size(); i++) std::cout << "  " << args[i].to_string() << "\n";
    expr val = t;
    //std::cout << "made val. " << args.size() << "\n";
    for (int i = 2; i < args.size(); i++) {
      //  std::cout << "why am i in for loop?\n";
      auto const & tex = to_expr(args[i], type, m_tc);
      expr const & t2 = mk_add(m_tc, expr(val), expr(tex));
      val = t2;
    }
    std::cout << "have val to return\n";
    expr const & rv = val;
    return rv;
  }

    expr fold_mul(
	    buffer<w_term_tree> const & nargs, expr const & type, type_context m_tc) {
      //auto op = [](type_context tc, expr e1, expr e2) {return lean::mk_mul(tc, e1, e2);};
        //    std::cout << "folding! " << args.size() << "\n";
      auto args = buffer<w_term_tree>(nargs);
    if (args.size() == 1) {
      return to_expr(args[0], type, m_tc);
    }
    
    auto const & w1 = args[0];
    auto const & w2 = args[1];
    expr const & a1 = to_expr(w1, type, m_tc);
    expr const & a2 = to_expr(w2, type, m_tc);
    //std::cout << "have first two! of " << args.size() << " \n";
    expr const & t = (mk_mul(m_tc, a1, a2));
    std::cout << "made t in mul: " << t << ". a1 and a2 are now: " << a1 << ", " << a2 << "\n";
    expr val = t;
    //std::cout << "made val. " << args.size() << "\n";
    for (int i = 2; i < args.size(); i++) {
      //  std::cout << "why am i in for loop?\n";
      auto tex = to_expr(args[i], type, m_tc);
      expr const & rval = (mk_mul(m_tc, val, tex));
      val = rval;
    }
    std::cout << "have val to return\n";
    expr const & rv = val;
    return rv;
  }


  /*  expr const & w_term_tree::mk_add(type_context tc, expr e1, expr e2) {
    return lean::mk_add(tc, e1, e2);
  }

  expr const & w_term_tree::mk_mul(expr e1, expr e2) {
    return lean::mk_mul(*m_tc, e1, e2);
    }*/

  std::string const & w_term_tree::to_string_head() {
    if (is_add()) return "Add";
    else if (is_mul()) return "Mul";
    else if (is_sub()) return "Sub";
    else if (is_div()) return "Div";
    else if (is_neg()) return "Neg";
    else if (is_const() || is_const_app()) return c_head;
    else return (*w_head).to_string();
  }

  std::string wolfram_string_of_tree(w_term_tree arg) {
    
    std::cout << "in wolfram_string_of_tree: " << arg.num_args() << "\n";
    std::string s = arg.to_string_head() + (arg.num_args() > 0 ? "[" : "");
    for (int i = 0; i < arg.num_args(); i++) {
      std::cout << "i: " << i << " size: " << arg.num_args() << "\n";
      s += wolfram_string_of_tree(arg.get_args()[i]) + (i+1 < (arg.args->size()) ? ", " : "");
    }
    if (arg.num_args() > 0) s += "]";
    std::cout << "wsot returning: " << s << "\n";
    return s;
  }
  
  expr to_expr(w_term_tree arg, expr const & type, type_context m_tc) {
    std::cout << "to_expr called. type: " << type << ". head: " << arg.to_string_head() << "\n";
    std::cout << " args: " << arg.num_args() << "\n";
    if (arg.is_const()) { // c_head is the name of a constant with no args
      std::cout << "is_const\n";
      //levels lvl = levels(get_level(m_tc, type));
      return mk_local(name(arg.to_string_head()), type);
    } else if (arg.is_add()) {
      std::cout << "is_add\n";
      //auto static mk_add = [](type_context tc, expr e1, expr e2) {return lean::mk_add(tc, e1, e2);};
      return fold_add(arg.get_args(), type, m_tc);
      //return fold(mk_add, *(arg.args), type, m_tc);
    } else if (arg.is_mul()) {
      std::cout << "is_mul\n";
      //auto static mk_mul = [](type_context tc, expr e1, expr e2) {return lean::mk_mul(tc, e1, e2);};
      return fold_mul(arg.get_args(), type, m_tc);
      //return fold(mk_mul, *(arg.args), type, m_tc);
      /* } else if (arg.is_sub()) {
      auto static mk_sub = [](type_context tc, expr e1, expr e2) {return lean::mk_sub(tc, e1, e2);};
      return fold(mk_sub, *(arg.args), type, m_tc);
    } else if (arg.is_div()) {
      auto static mk_div = [](type_context tc, expr e1, expr e2) {return lean::mk_div(tc, e1, e2);};
      return fold(mk_div, *(arg.args), type, m_tc);
    } else if (arg.is_neg()) {
      if (arg.num_args() != 1) throw exception("neg with too many args");
      return mk_neg(m_tc, to_expr(arg.get_args()[0], type, m_tc));
    } else if (arg.is_const_app()) { // c_head is the name of a constant applied to args

    } else {*/
    }
      return type;
  }

  // s has form foo[...]...
  // returns           i
  int end_sq_brackets(std::string s) {
    int i = 0;
    while (s[i] != '[') i++;
    int cntr = 1;
    while (cntr > 0) {
      i++;
      if (s[i] == '[') cntr++;
      else if (s[i] == ']') cntr--;
    }
    return i;
  }

  buffer<std::string> parse_subargs(std::string const & s) {
    int cntr = 0;
    int i = 0;
    while (i < s.size() && (cntr != 0 || s[i] != ',')) {
      if (s[i] == '[') cntr++;
      else if (s[i] == ']') cntr--;
      i++;
    }
    if (i == s.size()) {
      buffer<std::string> ret = buffer<std::string>();
      ret.push_back(s);
      return ret;
    } else {
      std::string nv = s.substr(0, i);
      std::string rv = s.substr(i+1);
      auto ret = parse_subargs(trim(rv));
      ret.insert(0, nv);
      return ret;
    }
  }

  /*pair<buffer<w_term_tree>,int> get_next_app_arg_buffer(int i, std::string nin) {
      buffer<w_term_tree> nargs = buffer<w_term_tree>();
      int end_br = end_sq_brackets(nin);
      std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
      auto subargs = parse_subargs(trim(arg_subtm));
      for (int j = 0; j < subargs.size(); j++) {
	nargs.push_back(wolfram_to_tree(subargs[j]));
      }
      return mk_pair(nargs, end_br);
  }*/

  w_term_tree tree_of_string_and_args(std::string head, buffer<w_term_tree> nargs) {
    if (head == "Add") return mk_add_tree(nargs);
    if (head == "Mul") return mk_mul_tree(nargs);
    if (head == "Sub") return mk_sub_tree(nargs);
    if (head == "Div") return mk_div_tree(nargs);
    if (head == "Neg") return mk_neg_tree(nargs);
    std::cout << "none of the above...\n";
    return w_term_tree(head, nargs);
  }


  /*  pair<buffer<std::string>,int> get_next_app_arg_expr_buffer(int i, std::string const & nin, std::unordered_map<std::string, expr> const & const_map) {
    buffer<std::string> nargs = buffer<std::string>();
      int end_br = end_sq_brackets(nin);
      std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
      auto subargs = parse_subargs(trim(arg_subtm));
      for (int j = 0; j < subargs.size(); j++) {
	nargs.push_back(wolfram_to_lean(subargs[j], const_map));
      }
      return mk_pair(nargs, end_br);
  }*/

  // lv is a local variable, pr is an expr (possibly) containing lv. makes (exists lv, pr)
  expr mk_exists(expr const & lv, expr const & pr) {
    auto exc = mk_constant(name("Exists"), levels{level()});
    auto tp = mlocal_type(lv);
    auto exb = Fun(lv, pr);
    return mk_app(exc, tp, exb);
  }

  // lv is a local variable, pr is an expr (possibly) containing lv. makes (exists lv, pr)
  expr mk_forall(expr const & lv, expr const & pr) {
    return Pi(lv,  pr);
  }

  expr mk_num_term(type_context & tctx, int k, expr const & type) {
     //expr nat_type = mk_constant(get_nat_name(), {mk_succ(level())});
    //    std::cout << "nat_type: " << nat_type << "\n";
    return num_of_mpz(tctx, mpz(k), type);
    
  }
  
  expr wolfram_to_lean(type_context & tctx, std::string const & input, std::unordered_map<std::string, expr> const & const_map, expr default_type, bool use_default_type) {
    std::string nin = trim(input);
    int i = 0;
    while (nin[i] != '[' && i < input.size()) {
      i++;
    }
    std::string hd = nin.substr(0, i);
    expr ehd;

    if (const_map.count(hd)) {
      ehd = const_map.at(hd);
    } else {
      try {
	std::string::size_type j;
	int k = std::stoi(hd, &j);
	if (j == hd.size() && use_default_type) {
	  lean_assert(i == nin.size());
	  return mk_num_term(tctx, k, default_type);
	} else {
	  throw exception("const not known");
	}
      } catch (exception e) {
	//	std::cout << "Don't know " << hd << "!\n";
	//std::cout << input << "\n";
	throw exception(e);
      }
    }
    
    if (i == nin.size()) {
      // the wolfram expression is a constant
      return ehd;
    }
    
    int end_br = end_sq_brackets(nin);
    while (end_br != nin.size() - 1) {
      nin[end_br] = ' ';
      nin[end_br+1] = ' ';
      end_br = end_sq_brackets(nin);
    }
    
    std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
    buffer<std::string> p = parse_subargs(arg_subtm);
    
    if (hd == "Forall" || hd == "Exists") {
      if (p.size() != 3) throw exception("don't understand this quantifier");
      if (!const_map.count(p[1])) throw exception("don't understand quantified type");
      std::unordered_map<std::string, expr> new_map = std::unordered_map<std::string, expr>(const_map);
      new_map[p[0]] = mk_local(name(p[0]), const_map.at(p[1]));
      //std::cout << p[0] << "has been defined as " << new_map[p[0]] << ", type " << const_map.at(p[1]) << "\n";
      expr arg = wolfram_to_lean(tctx, p[2], new_map);
      if (hd == "Forall") return mk_forall(new_map[p[0]], arg);
      else return mk_exists(new_map[p[0]], arg);
    }

    buffer<expr> args = buffer<expr>();
    if (hd == "Add" || hd == "Mul" || hd == "Eq") {
      lean_assert(p.size() == 2);
      try {
	args.push_back(wolfram_to_lean(tctx, p[0], const_map));
	expr tp = tctx.infer(args[0]);
	args.push_back(wolfram_to_lean(tctx, p[1], const_map, tp, true));
      } catch (exception e) {
	try {
	  auto v = wolfram_to_lean(tctx, p[1], const_map);
	  expr tp = tctx.infer(v);
	  args.push_back(wolfram_to_lean(tctx, p[0], const_map, tp, true));
	  args.push_back(v);
	} catch (exception e) {
	  throw e;
	}
      }
    } else {
      for (int i = 0; i < p.size(); i++) args.push_back(
							wolfram_to_lean(
									tctx, p[i],
									const_map, default_type,
									use_default_type));
    }
    if (hd == "Add") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_add(tctx, a1, a2);
    } else if (hd == "Mul") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_mul(tctx, a1, a2);
    } else if (hd == "Eq") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_eq(tctx, a1, a2);
    } else {
      for (int i = 0; i < args.size(); i++)
	ehd = mk_app(ehd, args[i]);

      return ehd;
    }          
  }

 w_term_tree mk_add_tree(buffer<w_term_tree> nargs) {
    return w_term_tree(tree_kind::Add, nargs);
  }

  w_term_tree mk_mul_tree(buffer<w_term_tree> nargs) {
    return w_term_tree(tree_kind::Mul, nargs);
  }
  
  w_term_tree mk_sub_tree(buffer<w_term_tree> nargs) {
    return w_term_tree(tree_kind::Sub, nargs);
  }
  
  w_term_tree mk_div_tree(buffer<w_term_tree> nargs) {
    return w_term_tree(tree_kind::Div, nargs);
  }
  
  w_term_tree mk_neg_tree(buffer<w_term_tree> nargs) {
    return w_term_tree(tree_kind::Neg, nargs);
  }

}
