/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/wl_mathlink.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/explicit.h"
#include "library/placeholder.h"
#include "kernel/abstract.h"
#include <fstream>
#include <string>

using namespace std;

namespace lean {

MLINK send_wl_command_without_server(string cmd) {
  int pid;

  MLINK lp;
  MLEnvironment env;

  /*ifstream infile;
  infile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  char output[9];
  if (infile.is_open()) {
    while (!infile.eof()) infile >> output;
  }
  infile.close();
  printf("read in: %s\n", output);*/

  char * args[5] = {"-linkname", "math -mathlink", "-linkmode", "launch",  NULL};
  env=MLInitialize(NULL);
  if (env==NULL) {printf("null env\n"); throw exception("mathlink failed at 2 : null env");}
  int open_error;
  lp = MLOpenInEnv(env, 4, args, &open_error);
  if (lp==NULL) {printf("null lp\n"); throw exception("mathlink failed at 2 : null lp");}
  MLActivate(lp);

  
  while (MLReady(lp)) {MLNextPacket(lp); MLNewPacket(lp);}

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutSymbol(lp, "$ProcessID");
  MLEndPacket(lp);
  while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  MLGetInteger(lp, &pid);
  printf("process id: %d\n", pid);


  MLPutFunction(lp, "Get", 1);
  MLPutString(lp, "/home/rlewis/cpp/ml_lean_form.m");
  MLEndPacket(lp);
  while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  MLNewPacket(lp);
  
  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp, cmd.c_str());
  MLEndPacket(lp);
  while(MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);

  return lp;
  
}
  
  /* set_wl_command must always be followed by reset_link */
MLINK send_wl_command(string cmd) {
  ifstream infile;
  infile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  char output[9];
  if (infile.is_open()) {
    while (!infile.eof()) infile >> output;
  }
  infile.close();
  printf("read in: %s\n", output);

  if (output == "---------" || output == "*********") {
    std::cout << "cmp succ\n";
    return send_wl_command_without_server(cmd);
  }
  
  int pid;
  MLINK lp;
  //MLEnvironment env;

  char * args[5] = {"-linkname", output, "-linkmode", "connect",  NULL};
  //env=MLInitialize(NULL);
  //if (env==NULL) {printf("null env\n"); throw exception("mathlink failed: null env");}
  //int open_error;
  lp = MLOpen( 4, args);
  if (lp==NULL) {printf("null lp\n"); throw exception("mathlink failed: null link");}
  if (!MLActivate(lp)) {
    MLClose(lp);  
    ofstream outfile;
    outfile.open("/home/rlewis/cpp/tmp/key_exch.txt");
    outfile << "---------";
    outfile.close();
    return send_wl_command_without_server(cmd);
  }
  
  ofstream outfile;
  outfile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  outfile << "*********";
  outfile.close();
  
  while (MLReady(lp)) {MLNextPacket(lp); MLNewPacket(lp);}

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
  ifstream infile;
  infile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  char output[9];
  if (infile.is_open()) {
    while (!infile.eof()) infile >> output;
  }
  infile.close();
  if (output == "---------") {
    MLClose(lp);
    return;
  }
  
  MLNewPacket(lp);

  while (MLReady(lp)) {MLNextPacket(lp); MLNewPacket(lp);}
  
  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp, "newParentLink=LinkCreate[]");
  MLEndPacket(lp);
  //std::cout << "bench 0.5\n";
  int pkt;
  while ((pkt=MLNextPacket(lp)) && pkt != RETURNPKT) MLNewPacket(lp);
  if (!pkt) {
    std::cout << "have error!\n";
    MLClearError(lp);
  }
  MLNewPacket(lp);
  //std::cout << "bench 1\n";

  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "First", 1);
  MLPutSymbol(lp, "newParentLink");
  MLEndPacket(lp);
  while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  const char* link_name;
  MLGetString(lp, &link_name);
  //std::cout << "bench 2 " << link_name << "\n";
  
  MLPutFunction(lp, "EvaluatePacket", 1);
  MLPutFunction(lp, "ToExpression", 1);
  MLPutString(lp,
    "MathLink`AddSharingLink[newParentLink, MathLink`SendInputNamePacket -> True, MathLink`Terminating -> True]; MathLink`SetTerminating[$ParentLink, False]");
  MLEndPacket(lp);
  // while (MLNextPacket(lp) != RETURNPKT) MLNewPacket(lp);
  MLNewPacket(lp);
  MLClose(lp);
  //std::cout << "bench 3\n";
  
  printf("link name: %s\n", link_name);
  ofstream outfile;
  outfile.open("/home/rlewis/cpp/tmp/key_exch.txt");
  outfile << link_name;
  outfile.close();
  //std::cout << "bench 4\n";
}

  typedef std::function<expr(expr *)> expr_fn;
  typedef std::pair<unsigned, expr_fn> expr_fn_ar;
  typedef std::unordered_map<string, expr> const_map;

  const expr mk_translate_constant(string hd) {
    if (hd == "nat") {
      return mk_constant(get_nat_name());
    } else if (hd == "rat") {
      return mk_constant(name("rat"));
    } else if (hd == "int") {
      return mk_constant(get_int_name());
    }  else if (hd == "real") {
      return mk_constant(name("real"));
    }else if (hd == "True") {
      return mk_constant(get_true_name());
    } else if (hd == "False") {
      return mk_constant(get_false_name());
    } else if (hd == "LeanPlaceholder") {
      return mk_expr_placeholder();
    } else {
      return mk_local(name(hd), mk_expr_placeholder());
    }
  }

  const expr_fn mk_translate_constructor(string hd, int nargs) {
    if (hd == "LeanAdd") {
      return [](expr * args) {
	return mk_app(mk_constant(get_add_name()), args[0], args[1]);
      };

    } else if (hd == "LeanMul") {
      return [](expr * args) {
	return mk_app(mk_constant(get_mul_name()), args[0], args[1]);
      };

    } else if (hd == "Subtract") {
      return [](expr * args) {
	return mk_app(mk_constant(get_sub_name()), args[0], args[1]);
      };

    } else if (hd == "Divide" || hd == "Rational") {
      return [](expr * args) {
	return mk_app(mk_constant(get_div_name()), args[0], args[1]);
      };

    } else if (hd == "Negative") {
      return [](expr * args) {
	return mk_app(mk_constant(get_neg_name()), args[0]);
      };

    } else if (hd == "Eq") {
      return [](expr * args) {
	return mk_app(mk_constant(get_eq_name()), args[0], args[1]);
      };

    } else if (hd == "Power") {
      return [](expr * args) {
	return mk_app(mk_constant(name("pow_nat")), args[0], args[1]);
      };

    } else if (hd == "And") {
      return [](expr * args) {
	return mk_app(mk_constant(get_and_name()), args[0], args[1]);
      };

    } else if (hd == "Or") {
      return [](expr * args) {
	return mk_app(mk_constant(get_or_name()), args[0], args[1]);
      };
      
    } else if (hd == "Implies") {
      return [](expr * args) {
	return mk_app(mk_constant(get_implies_name()), args[0], args[1]);
      };
      
    } else if (hd == "Not") {
      return [](expr * args) {
	return mk_app(mk_constant(get_not_name()), args[0]);
      };

    } else if (hd == "LeanForAll") {
      return [](expr * args) {
	expr body = abstract(args[2], args[0]);
	return mk_pi(mlocal_name(args[0]), args[1], body);
      };

    } else if (hd == "LeanExists") {
      return [](expr * args) {
	expr body = abstract(args[2], args[0]);
	expr lam = mk_lambda(mlocal_name(args[0]), args[1], body);
	return mk_app(mk_constant(get_Exists_name()), args[1], lam);
      };
      
    } else if (hd == "LeanApp") {
      return [](expr * args) {
	expr e0 = args[0];
	expr e1 = args[1];
	std::cout << "making app: " << mk_app(e0, e1) << "\n";
	return mk_app(e0, e1); // mk_as_is?
      };

    } else if (hd == "ListCons") {
      return [](expr * args) {
	return mk_app(mk_constant(name("list", "cons")), args[0], args[1]);
      };

    } else if (hd == "ListEnd") {
      return [](expr * args) {
	return mk_app(mk_constant(name("list", "cons")), args[0], mk_constant(name("list", "nil")));
      };

    } else if (hd == "LeanAnd") {
      return [](expr * args) {
	return mk_app(mk_constant(get_and_name()), args[0], args[1]);
      };

    } else if (hd == "LeanOr") {
      return [](expr * args) {
	return mk_app(mk_constant(get_or_name()), args[0], args[1]);
      };

    } else if (hd == "Function") {
      return [](expr * args) {
	return Fun(args[0], args[1]);
      };
      
    } else if (hd == "LeanVar") {
      return [](expr * args) {
	name nm = mlocal_name(args[0]);
	return mk_local(nm, mk_expr_placeholder());
      };
    } else if (hd == "LeanLocal") {
      return [](expr * args) {
        return args[0];
      };
    } else if (hd == "LeanConst") {
      return [](expr * args) {
	return mk_partial_explicit(mk_constant(mlocal_name(args[0]), {mk_level_placeholder()}));
      };
    } else if (hd == "LeanPair") {
      return [](expr * args) {
	return mk_app(mk_constant(get_prod_mk_name()), args[0], args[1]);
      };
    } else {
      return [&hd, &nargs](expr * args) {
	std::cout << "making explicit hd: " << hd << "\n";
	expr ah = mk_partial_explicit(mk_constant(name(hd), {mk_level_placeholder()}));
	buffer<expr> newargs = buffer<expr>();
	newargs.push_back(ah);
	for (int i = 0; i < nargs; i++) {
	  newargs.push_back(args[i]);
	}
	return mk_app(newargs); // mk_as_is?
      };
    }
  }

  expr pnum_of_int(int n) {
    if (n < 0) return mk_app(mk_constant(get_neg_name()), pnum_of_int(-n));
    if (n == 0) return mk_constant(get_zero_name());
    if (n == 1) return mk_constant(get_one_name());
    if (n%2 == 0) return mk_app(mk_constant(get_bit0_name()), pnum_of_int(n/2));
    else return mk_app(mk_constant(get_bit1_name()), pnum_of_int(n/2));
  }
  
  expr expr_from_wl_link(const_map cm, MLINK lp) {
    auto tp = MLGetType(lp);
    //std::cout << "tp: " << tp << "\n";
    switch (tp) {
    case MLTKSTR: { // Return a string wrapped in a local variable. This should be unpacked immediately
      const char *s;
      MLGetString(lp, &s); // need to release?
      std::cout << "link gave string: " << s << " in map? " << cm.count(s) << "\n";
      if (cm.count(s)) return cm[s];
      else return mk_local(name(s), mk_metavar(name("_"+(std::string)s +"_m"), mk_sort(mk_meta_univ(name("_"+(std::string)s+"_u")))));
      break;
    }
    case MLTKINT: {
      int s;
      MLGetInteger(lp, &s);
      std::cout << "link gave int: " << s << "\n";
      return pnum_of_int(s);
      break;
    }
    case MLTKFUNC: {
      int len;
      MLGetArgCount(lp, &len);
      const char *hd;
      MLGetSymbol(lp, &hd); // need to release?
      std::cout << "link gave func: " << hd << len << "\n";
      buffer<expr> args = buffer<expr>();
      for (int i = 0; i < len; i++) {
	std::cout << "getting arg " << i << " for " << hd << "\n";
	args.push_back(expr_from_wl_link(cm, lp));
	std::cout << "got arg " << i << " for " << hd << "\n";
      }
      std::cout << "got arg data for " << hd << "\n";
      if (cm.count(hd)) {
	std::cout << "in table! " << hd << "\n";
	args.insert(0, cm[hd]);
	return mk_app(args);
      } else {
	return mk_translate_constructor(hd, len)(args.data());
      }
      break;
    }
    case MLTKREAL: {
      double d;
      MLGetReal(lp, &d);
      std::cout << "link gave real: " << d << "\n";
      throw exception("cannot handle reals from mathematica");
      break;
    }
    case MLTKSYM: {
      const char *s;
      MLGetSymbol(lp, &s); // need to release?
      std::cout << "link gave symbol: " << s << " in map? " << cm.count(s) << "\n";
      //if (cm.count(s)) return cm[s];
      //else return mk_local(name(s), expr());//mk_explicit(mk_constant(name(s), {mk_level_placeholder()}));
      return mk_translate_constant(s);
      break;
    }
    default:
      //std::cout << "link gave ???\n";
      throw exception("MathLink type not understood");
    }
    // error
  }

  expr wl_process_cmd(const_map cm, string cmd) {
    std::cout << "starting process_cmd\n";
    MLINK lp = send_wl_command(cmd);
    std::cout << "made link!\n";
    expr e = expr_from_wl_link(cm, lp);
    std::cout << "got expr: " << e << "\n";
    reset_link(lp);
    std::cout << "reset link!\n";
    return e;
  }
  
}
