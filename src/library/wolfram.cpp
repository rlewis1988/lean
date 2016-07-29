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
#include "kernel/type_checker.h"
#include <string>

namespace lean {

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
    unsigned i = 0;
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

  // lv is a local variable, pr is an expr (possibly) containing lv. makes (exists lv, pr)
  expr mk_exists(expr const & lv, expr const & pr) {
    auto exc = mk_constant(name("Exists"), levels{level()});
    auto tp = mlocal_type(lv);
    auto exb = Fun(lv, pr);
    return mk_app(exc, tp, exb);
  }

  // lv is a local variable, pr is an expr (possibly) containing lv. makes (pi lv, pr)
  expr mk_forall(expr const & lv, expr const & pr) {
    return Pi(lv,  pr);
  }

  expr mk_num_term(type_context & tctx, int k, expr const & type) {
    return num_of_mpz(tctx, mpz(k), type);
    
  }

  pair<std::string, unsigned> flatten_apps(std::string const & pnin) {
    std::string nin = pnin;
    unsigned end_br = end_sq_brackets(nin);
    while (end_br != nin.size() - 1) {
      nin[end_br] = ' ';
      nin[end_br+1] = ' ';
      end_br = end_sq_brackets(nin);
    }
    return mk_pair(nin, end_br);
  }

  std::string& remove_chars(std::string& s, const std::string& chars) {
    s.erase(remove_if(s.begin(), s.end(), [&chars](const char& c) {
	  return chars.find(c) != std::string::npos;
    }), s.end());
    return s;
}
  
  expr wolfram_to_lean(type_context & tctx, std::string const & input, std::unordered_map<std::string, expr> const & const_map, expr default_type, bool use_default_type) {
    std::string nin = trim(input);
    nin = remove_chars(nin, "\"");
    unsigned i = 0;
    while (nin[i] != '[' && i < input.size()) {
      i++;
    }
    std::string hd = nin.substr(0, i);
    expr ehd;

    if (const_map.count(hd)) {
      ehd = const_map.at(hd); // the head is recognized
    } else {
      //try { // the term could be a number; if it is, create the numeral with default_type
	std::string::size_type j;
	int k;
	try {
	  k = std::stoi(hd, &j);
	} catch (std::invalid_argument e) {
	  j = 0;
	}
	if (j == hd.size() && use_default_type && i == nin.size()) {
	  if (k >= 0)
	    return mk_num_term(tctx, k, default_type);
	  else return mk_neg(tctx, mk_num_term(tctx, -k, default_type));
	} else {
	  throw exception("const not known: " + hd);
	}
    }
    
    if (i == nin.size()) {
      // the wolfram expression is a constant
      return ehd;
    }
    
    auto pr = flatten_apps(nin);
    nin = pr.first;
    unsigned end_br = pr.second;
    
    std::string arg_subtm = nin.substr(i + 1, end_br - 1 - i);
    buffer<std::string> p = parse_subargs(arg_subtm);
    
    if (hd == "Forall" || hd == "Exists") {
      // Quantifiers are handled as a special case.
      if (p.size() != 3) throw exception("quantifier has wrong number of args");

      if (!const_map.count(p[1])) throw exception("don't understand quantified type");

      std::unordered_map<std::string, expr> new_map = std::unordered_map<std::string, expr>(const_map);
      new_map[p[0]] = mk_local(name(p[0]), const_map.at(p[1]));
      expr arg = wolfram_to_lean(tctx, p[2], new_map);

      if (!tctx.is_prop(arg)) throw exception("can only quantify over propositions");

      if (hd == "Forall") return mk_forall(new_map[p[0]], arg);
      else return mk_exists(new_map[p[0]], arg);
    }

    buffer<expr> args = buffer<expr>();
    if (hd == "Plus" || hd == "Times" || hd == "Subtract" || hd == "Divide" || hd == "Eq") {
      // Arithmetic terms are also a special case: since they are expecting numerals as input,
      // we need to provide default types.
      // Either we know the default type already, or the types have to match.
      lean_assert(p.size() == 2);
      if (use_default_type) {
	args.push_back(wolfram_to_lean(tctx, p[0], const_map, default_type, true));
	args.push_back(wolfram_to_lean(tctx, p[1], const_map, default_type, true));
      } else {
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
      }
    } else if (hd == "Negative") {
      args.push_back(wolfram_to_lean(tctx, p[0], const_map, default_type, use_default_type));
    } else if (hd == "LeanApp") {
      args.push_back(wolfram_to_lean(tctx, p[0], const_map, default_type, use_default_type));
      args.push_back(wolfram_to_lean(tctx, p[1], const_map, binding_body(tctx.infer(args[0])), true));
    } else { // we make no assumptions about the types of arguments so we pass no default.
      for (unsigned i = 0; i < p.size(); i++)
	args.push_back(wolfram_to_lean(tctx, p[i], const_map));
    }
    if (hd == "Plus") { // for arithmetic, we infer the type classes
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_add(tctx, a1, a2);
    } else if (hd == "Times") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_mul(tctx, a1, a2);
    } else if (hd == "Subtract") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_mul(tctx, a1, a2);
    } else if (hd == "Divide") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_mul(tctx, a1, a2);
    } else if (hd == "Negative") {
      return mk_neg(tctx, args[0]);
    } else if (hd == "Eq") {
      expr const & a1 = args[0];
      expr const & a2 = args[1];
      return mk_eq(tctx, a1, a2);
    } else if (hd == "LeanApp") {
      return mk_app(args[0], args[1]);
    } else {
      for (unsigned i = 0; i < args.size(); i++)
	ehd = mk_app(ehd, args[i]);

      return ehd;
    }          
  }

std::string lean_to_wolfram_aux_ne(expr const & e, stringmap * fvn, stringexprmap * fve, int * fvn_next,
		 std::unordered_map<unsigned, std::string> const & vn, unsigned dpt, bool rename) {    
    std::stringstream st;
    if (is_pi(e) || is_lambda(e)) {
      //      std::cout << "have pi.\nBinding name: " << binding_name(e) << "\nBinding domain: " << binding_domain(e) << "\nBinding body: " << binding_body(e) << "\n" << "binding info: " << binding_info(e) << "\n\n";
      auto nmap = std::unordered_map<unsigned, std::string>(vn);
      std::string nname;
      if (rename) {
	nname = "mv__"+std::to_string(*fvn_next);
	(*fvn_next)++;
      } else {
	nname = binding_name(e).get_string();
      }
      nmap[dpt] = nname;
      auto bd = lean_to_wolfram_aux_ne(binding_domain(e), fvn, fve, fvn_next, vn, dpt, rename);
      auto bb = lean_to_wolfram_aux_ne(binding_body(e), fvn, fve, fvn_next, nmap, dpt+1, rename);
      st << "Lean" << (is_pi(e) ? "Pi[" : "Lambda[")
	 << "LeanVar[\"" << nname << "\"], "
	 << bd << ", "
	 << bb << "]";
    } else if (is_var(e)) {
      if (vn.count(dpt-var_idx(e)-1)) {
	st << "LeanVar[\"" << vn.at(dpt-var_idx(e)-1) << "\"]";
      } else {
	st << "LeanVar[\"" << e << "\"]";
      }
    } else if (is_constant(e)) {
      auto cst = const_name(e).to_string();
      st << "LeanConst[\"" << cst << "\"]";
    } else if (is_app(e)) {
      auto hd = lean_to_wolfram_aux_ne(app_fn(e), fvn, fve, fvn_next, vn, dpt, rename);
      auto arg = lean_to_wolfram_aux_ne(app_arg(e), fvn, fve, fvn_next, vn, dpt, rename);
      st << "LeanApp[" << hd << ", " << arg << "]";
    } else if (is_sort(e)) {
      st << "LeanType[" << sort_level(e) << "]"; // strip level info?
    } else if (is_local(e)) {
      auto cst = local_pp_name(e).to_string();
      if (rename && fvn->count(cst)) {
	st << "LeanVar[\"" << fvn->at(cst) << "\"]";
      } else if (rename) {
	fvn->emplace(cst, "mv__"+std::to_string(*fvn_next));
	fve->emplace("mv__"+std::to_string(*fvn_next), e);
	(*fvn_next)++;
	st << "LeanVar[\"" << fvn->at(cst) << "\"]";
      } else {
	st << "LeanVar[\"" << cst << "\"]";
	fve->emplace(cst, e);
      }
      
    } else { // Meta, Let, Macro- these shouldn't show up
      st << e;
    }
    return st.str();
  }

  std::string lean_to_wolfram_aux(expr const & e, stringmap * fvn, stringexprmap * fve, int * fvn_next,
		 std::unordered_map<unsigned, std::string> const & vn, unsigned dpt, bool rename) {    
    std::stringstream st;
    if (is_pi(e) || is_lambda(e)) {
      //      std::cout << "have pi.\nBinding name: " << binding_name(e) << "\nBinding domain: " << binding_domain(e) << "\nBinding body: " << binding_body(e) << "\n" << "binding info: " << binding_info(e) << "\n\n";
      auto nmap = std::unordered_map<unsigned, std::string>(vn);
      std::string nname;
      if (rename) {
	nname = "mv__"+std::to_string(*fvn_next);
	(*fvn_next)++;
      } else {
	nname = binding_name(e).get_string();
      }
      nmap[dpt] = nname;
      auto bd = lean_to_wolfram_aux(binding_domain(e), fvn, fve, fvn_next, vn, dpt, rename);
      auto bb = lean_to_wolfram_aux(binding_body(e), fvn, fve, fvn_next, nmap, dpt+1, rename);
      st << "Lean" << (is_pi(e) ? "Pi[" : "Lambda[")
	 << "LeanVar[\\\"" << nname << "\\\"], "
	 << bd << ", "
	 << bb << "]";
    } else if (is_var(e)) {
      if (vn.count(dpt-var_idx(e)-1)) {
	st << "LeanVar[\\\"" << vn.at(dpt-var_idx(e)-1) << "\\\"]";
      } else {
	st << "LeanVar[\\\"" << e << "\\\"]";
      }
    } else if (is_constant(e)) {
      auto cst = const_name(e).to_string();
      st << "LeanConst[\\\"" << cst << "\\\"]";
    } else if (is_app(e)) {
      auto hd = lean_to_wolfram_aux(app_fn(e), fvn, fve, fvn_next, vn, dpt, rename);
      auto arg = lean_to_wolfram_aux(app_arg(e), fvn, fve, fvn_next, vn, dpt, rename);
      st << "LeanApp[" << hd << ", " << arg << "]";
    } else if (is_sort(e)) {
      st << "LeanType[" << sort_level(e) << "]"; // strip level info?
    } else if (is_local(e)) {
      auto cst = local_pp_name(e).to_string();
      if (rename && fvn->count(cst)) {
	st << "LeanVar[\\\"" << fvn->at(cst) << "\\\"]";
      } else if (rename) {
	fvn->emplace(cst, "mv__"+std::to_string(*fvn_next));
	fve->emplace("mv__"+std::to_string(*fvn_next), e);
	(*fvn_next)++;
	st << "LeanVar[\\\"" << fvn->at(cst) << "\\\"]";
      } else {
	st << "LeanVar[\\\"" << cst << "\\\"]";
	fve->emplace(cst, e);
      }
      
    } else { // Meta, Let, Macro- these shouldn't show up
      st << e;
    }
    return st.str();
  }

  
    pair<std::string, stringexprmap> lean_to_wolfram(expr const & e, bool const & rename) {
    stringmap * fvn = new stringmap();
    stringexprmap * fve = new stringexprmap();
    int inv = 0;
    int * next_var = &inv;
    return mk_pair(
	 lean_to_wolfram_aux(e, fvn, fve, next_var,
			     std::unordered_map<unsigned, std::string>(), 0, rename),
	 *fve);
  }

}
