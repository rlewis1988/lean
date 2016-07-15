/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/wolfram.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include <string>

namespace lean {
  /*

    typedef std::function<expr(expr, expr)> op;
    std::unordered_map<std::string, op> name_dict;
    name_dict["add"] = [](expr e1, expr e2) {return e1;};
*/

  expr fold(std::function<expr(type_context, expr, expr)> op,
	    buffer<w_term_tree> args, expr const & type, type_context m_tc) {
    std::cout << "folding! " << args.size() << "\n";
    if (args.size() == 1) {
      return args[0].to_expr(type, m_tc);
    }
    buffer<w_term_tree> nargs = buffer<w_term_tree>(args);
    expr val = op(m_tc, args[0].to_expr(type, m_tc), args[1].to_expr(type, m_tc));
    for (int i = 2; i < args.size(); i++) {
      val = op(m_tc, val, args[i].to_expr(type, m_tc));
    }
    return val;
  }

  /*  expr const & w_term_tree::mk_add(type_context tc, expr e1, expr e2) {
    return lean::mk_add(tc, e1, e2);
  }

  expr const & w_term_tree::mk_mul(expr e1, expr e2) {
    return lean::mk_mul(*m_tc, e1, e2);
    }*/
  
  expr w_term_tree::to_expr_aux(expr const & type) {
    std::cout << "to_expr_aux called. type: " << type << ". head: " << c_head << "\n";
    auto static mk_add = [](type_context tc, expr e1, expr e2) {return lean::mk_add(tc, e1, e2);};
    auto static mk_mul = [](type_context tc, expr e1, expr e2) {return lean::mk_mul(tc, e1, e2);};
    if (is_const_head() && is_const()) { // c_head is the name of a constant with no args
      levels lvl = levels(get_level(*m_tc, type));
      return mk_local(name(c_head), type);
    } else if (is_const_head()) { // c_head is the name of a constant applied to args
      if        (c_head == "Add") {
	return fold(mk_add, *args, type, *m_tc);
      } else if (c_head == "Mul") {
	return fold(mk_mul, *args, type, *m_tc);
      } else if (c_head == "Neg") {
      } else { // w_head is the application of a function to args, and this term is applied to args
      }
    } else {
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

  pair<buffer<w_term_tree>,int> get_next_app_arg_buffer(int i, std::string nin) {
      buffer<w_term_tree> nargs = buffer<w_term_tree>();
      int end_br = end_sq_brackets(nin);
      std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
      auto subargs = parse_subargs(trim(arg_subtm));
      for (int j = 0; j < subargs.size(); j++) {
	nargs.push_back(wolfram_to_tree(subargs[j]));
      }
      return mk_pair(nargs, end_br);
  }
  
  w_term_tree wolfram_to_tree(std::string & input) {
    name const & adn = get_add_name();
    expr const e1 = mk_constant(adn);
    expr const e2 = mk_constant(adn);
    expr const es[2] = {e1, e2};
    expr const *ess = es;
    auto ex = mk_app({e1, e2});//mk_app(adn, 2, ess);
    std::string nin = trim(input);
    int i = 0;
    while (nin[i] != '[' && i < input.size()) {
      i++;
    }
    std::string hd = nin.substr(0, i);
    std::cout << "nin: " << nin << " i: " << i << "\n";
    
    if (i == nin.size()) {
      // the wolfram expression is a constant
      std::cout << "making constant: " << hd << "\n";
      return w_term_tree(hd);
    } else {
      /*buffer<w_term_tree> nargs = buffer<w_term_tree>();
      int end_br = end_sq_brackets(nin);
      std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
      auto subargs = parse_subargs(trim(arg_subtm));
      for (int j = 0; j < subargs.size(); j++) {
	nargs.push_back(wolfram_to_expr(subargs[j]));
	}*/
      auto p = get_next_app_arg_buffer(i, nin);
      auto nargs = p.first;
      auto end_br = p.second;
      std::cout << "for " << nin << ", end_br: " << end_br << "\n";
      w_term_tree * ntt = new w_term_tree(hd, &nargs);
      std::cout << "nargs size: " << nargs.size() << "\n";
      if (end_br == nin.size() - 1)
	return *ntt;
      else {
	std::string remargs = trim(nin.substr(end_br + 1));
	while (remargs.size() > 0) {
	  auto p = get_next_app_arg_buffer(0, remargs);
	  std::cout << "in else, setting ntt. size of args:" << p.first.size() << "\n";
	  std::cout << "old ntt is const head: " << ntt -> is_const_head() << "\n";
	  auto p1 = p.first;
          ntt = new w_term_tree(ntt, &p1);
	  std::cout << "set. ntt arg size: " << ntt->args->size() << " " << ntt->is_const_head() <<  "\n";
	  std::cout << "new ntt head is const head: " << ntt->w_head->is_const_head() << "\n";
	  remargs = trim(remargs.substr(p.second + 1));
	  std::cout << "remaining: " << remargs << "\n";
	}
	return *ntt;
      }
    }
  }

}
