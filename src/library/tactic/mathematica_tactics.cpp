/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robert Y. Lewis
*/
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm_string.h"
#include "library/wl_mathlink.h"
#include "library/tactic/mathematica_tactics.h"

namespace lean {
  
  vm_obj tactic_wl_execute_str(vm_obj const & e, vm_obj const & s) {
    expr e1 = wl_process_cmd(to_string(e));
    return tactic::mk_success(to_obj(e1), tactic::to_state(s));
  }

  vm_obj tactic_wl_execute_global_str(vm_obj const & e, vm_obj const & s) {
    expr e1 = wl_process_global_cmd(to_string(e));
    return tactic::mk_success(to_obj(e1), tactic::to_state(s));
  }

  vm_obj tactic_get_mathematica_path() {
    return to_obj(get_mm_extras_path());
  }

  void initialize_mathematica_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "mathematica", "execute"}), tactic_wl_execute_str);
    DECLARE_VM_BUILTIN(name({"tactic", "mathematica", "execute_global"}), tactic_wl_execute_global_str);
    DECLARE_VM_BUILTIN(name({"tactic", "mathematica", "extras_path"}), tactic_get_mathematica_path);
  }

  void finalize_mathematica_tactic() {
  }

}
