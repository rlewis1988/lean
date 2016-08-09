/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/wl_mathlink.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include <fstream>
#include <string>

using namespace std;

namespace lean {

  /* set_wl_command must always be followed by reset_link */
MLINK send_wl_command(string cmd) {
  int pid;

  MLINK lp;
  MLEnvironment env;

  ifstream infile;
  infile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  char output[9];
  if (infile.is_open()) {
    while (!infile.eof()) infile >> output;
  }
  infile.close();
  printf("read in: %s\n", output);

  char * args[5] = {"-linkname", output, "-linkmode", "connect",  NULL};
  env=MLInitialize(NULL);
  if (env==NULL) {printf("null env\n"); return lp;}
  int open_error;
  lp = MLOpenInEnv(env, 4, args, &open_error);
  if (lp==NULL) {printf("null lp\n"); return lp;}
  MLActivate(lp);

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutSymbol(lp, "$ProcessID");
  MLEndPacket(lp);
  while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  MLGetInteger(lp, &pid);
  printf("process id: %d\n", pid);

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp, cmd.c_str());
  MLEndPacket(lp);
  while(MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  
  return lp;
}

void reset_link(MLINK lp) {
  std::cout << "bench 0\n";
  MLNewPacket(lp);

  while (MLReady(lp)) {MLNextPacket(lp); MLNewPacket(lp);}
  std::cout << "\n";

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp, "newParentLink=LinkCreate[]");
  MLEndPacket(lp);
  std::cout << "bench 0.5\n";
  int pkt;
  while ((pkt=MLNextPacket(lp)) && pkt != RETURNPKT) MLNewPacket(lp);
  if (!pkt) {
    std::cout << "have error!\n";
    MLClearError(lp);
  }
  MLNewPacket(lp);
  std::cout << "bench 1\n";

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "First", 1);
  MLPutSymbol(lp, "newParentLink");
  MLEndPacket(lp);
  while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  const char* link_name;
  MLGetString(lp, &link_name);
  std::cout << "bench 2 " << link_name << "\n";
  
  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp,
    "MathLink`AddSharingLink[newParentLink, MathLink`SendInputNamePacket -> True, MathLink`Terminating -> True]; MathLink`SetTerminating[$ParentLink, False]");
  MLEndPacket(lp);
  // while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  MLNewPacket(lp);
  MLClose(lp);
  std::cout << "bench 3\n";
  
  printf("link name: %s\n", link_name);
  ofstream outfile;
  outfile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  outfile << link_name;
  outfile.close();
  std::cout << "bench 4\n";
}

  typedef std::function<expr(expr *)> expr_fn;
  typedef std::pair<unsigned, expr_fn> expr_fn_ar;
  typedef std::unordered_map<string, expr> const_map;


  const expr_fn mk_translate_constructor(type_context ctx, local_context lctx, string hd) {
    if (hd == "Plus") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_add_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_add_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0, e1});*/
	return mk_app(mk_constant(get_add_name()), args[0], args[1]);
      };

    } else if (hd == "Times") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_mul_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_mul_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0, e1});*/
	return mk_app(mk_constant(get_mul_name()), args[0], args[1]);
      };

    } else if (hd == "Subtract") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_sub_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_sub_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0, e1});*/
	return mk_app(mk_constant(get_sub_name()), args[0], args[1]);
      };

    } else if (hd == "Divide" || hd == "Rational") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_div_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_div_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0, e1});*/
	return mk_app(mk_constant(get_div_name()), args[0], args[1]);
      };

    } else if (hd == "Negative") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_neg_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_neg_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0});*/
	return mk_app(mk_constant(get_neg_name()), args[0]);
      };

    } else if (hd == "Equal") {
      return [&ctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_eq_name(), {lvl});
	return mk_app({addname, tp, e0, e1});*/
	return mk_app(mk_constant(get_eq_name()), args[0], args[1]);
      };

    } else if (hd == "Power") {

    } else if (hd == "LeanApp") {
      return [](expr * args) {
	expr e0 = args[0];
	expr e1 = args[1];
	return mk_app(e0, e1);
      };

    } else if (hd == "ListCons") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr consname = mk_constant(name("list", "cons"), {lvl});
	return mk_app({consname, tp, e0, e1});*/
	return mk_app(mk_constant(name("list", "cons")), args[0], args[1]);
      };

    } else if (hd == "ListEnd") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr tp = ctx.infer(e0);
	level lvl = get_level(ctx, tp);
	expr consname = mk_constant(name("list", "cons"), {lvl});
        expr nilname = mk_constant(name("list", "nil"), {lvl});
	expr e1 = mk_app(nilname, tp);
	return mk_app({consname, tp, e0, e1});*/
	return mk_app(mk_constant(name("list", "cons")), args[0], mk_constant(name("list", "nil")));
      };

      /*} else if (hd == "Rational") {
      return [&ctx, &lctx](expr * args) {
	/*expr e0 = args[0];
	expr e1 = args[1];
	expr tp = mk_constant(name("rat"));
	level lvl = get_level(ctx, tp);
	expr addname = mk_constant(get_div_name(), {lvl});
	expr has_add = mk_app({mk_constant(get_has_div_name(), {lvl}), tp});
	expr hamv = ctx.mk_metavar_decl(lctx, has_add);
	return mk_app({addname, tp, hamv, e0, e1});
	};*/

    } else if (hd == "LeanVar" || hd == "LeanConst") {
      return [](expr * args) {
	return args[0];
      };
    }
    throw exception("reconstruction error: unknown head");
  }

  expr pnum_of_int(int n) {
    if (n < 0) return mk_app(mk_constant(get_neg_name()), pnum_of_int(-n));
    if (n == 0) return mk_constant(get_zero_name());
    if (n == 1) return mk_constant(get_one_name());
    if (n%2 == 0) return mk_app(mk_constant(get_bit0_name()), pnum_of_int(n/2));
    else return mk_app(mk_constant(get_bit1_name()), pnum_of_int(n/2));
  }
  
  expr expr_from_wl_link(type_context ctx, local_context lctx, const_map cm, MLINK lp) {
    auto tp = MLGetType(lp);
    std::cout << "tp: " << tp << "\n";
    switch (tp) {
    case MLTKSTR: {
      const char *s;
      MLGetString(lp, &s); // need to release?
      if (cm.count(s)) return cm[s];
      else return expr();
      break;}
    case MLTKINT: {
      int s;
      MLGetInteger(lp, &s);
      return pnum_of_int(s);
    }
    case MLTKFUNC: {
      int len;
      MLGetArgCount(lp, &len);
      const char *hd;
      MLGetSymbol(lp, &hd); // need to release?
      buffer<expr> args = buffer<expr>();
      for (unsigned i = 0; i < len; i++) {
	args.push_back(expr_from_wl_link(ctx, lctx, cm, lp));
      }
      return mk_translate_constructor(ctx, lctx, hd)(args.data());
      break;}
    default:
      return expr();
    }
    // error
  }

  expr wl_process_cmd(type_context ctx, local_context lctx, const_map cm, string cmd) {
    MLINK lp = send_wl_command(cmd);
    std::cout << "made link!\n";
    expr e = expr_from_wl_link(ctx, lctx, cm, lp);
    std::cout << "got expr: " << e << "\n";
    reset_link(lp);
    std::cout << "reset link!\n";
    return e;
  }
  
}
