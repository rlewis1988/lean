/*
Copyright (c) 2016 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#pragma once
#include "mathlink.h"
#include "library/type_context.h"
#include <string>
#include <unordered_map>
//#include "wl_get_executable.h"


namespace lean {
  expr wl_process_cmd(std::string cmd);
  expr wl_process_global_cmd(std::string cmd);

  std::string get_mm_extras_path();
  
}
