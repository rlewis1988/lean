
#include <iostream>
#include <math.h>
#include "library/vm/vm.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_string.h"

namespace lean {
// =======================================
// Builtin nat operations

struct vm_float : public vm_external {
    float m_val;
    vm_float(float const & v): m_val(v) {}
    virtual ~vm_float() {}
    virtual void dealloc() override { this->~vm_float(); get_vm_allocator().deallocate(sizeof(vm_float), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_float(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(m_val); }
};
  
vm_obj mk_vm_float(float n) {
  return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(n));
}

  float to_float(vm_obj const & o) {
    //return cidx(o);
    //    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_eigen))) vm_eigen(v));
    return static_cast<vm_float*>(to_external(o))->m_val;
  }

  vm_obj float_add(vm_obj const & e1, vm_obj const & e2) {
    return mk_vm_float(to_float(e1) + to_float(e2));
  }

    vm_obj float_sub(vm_obj const & e1, vm_obj const & e2) {
    return mk_vm_float(to_float(e1) - to_float(e2));
  }

    vm_obj float_mul(vm_obj const & e1, vm_obj const & e2) {
    return mk_vm_float(to_float(e1) * to_float(e2));
  }

    vm_obj float_log(vm_obj const & e1) {
      return mk_vm_float(log(to_float(e1)));
  }

    vm_obj float_lt(vm_obj const & e1, vm_obj const & e2) {
    return mk_vm_bool(to_float(e1) < to_float(e2));
  }

  vm_obj float_of_int(vm_obj const & i) {
    return mk_vm_float(to_int(i));
  }

  vm_obj float_to_string(vm_obj const & flt) {
    return to_obj(std::to_string(to_float(flt)));
  }

  vm_obj float_pi() {
    return mk_vm_float(3.14159);
  }
  
  void initialize_vm_float() {
  //    DECLARE_VM_BUILTIN(name({"float", "of_int"}), );
    DECLARE_VM_BUILTIN(name({"float", "add"}),             float_add);
    DECLARE_VM_BUILTIN(name({"float", "sub"}),             float_sub);
    DECLARE_VM_BUILTIN(name({"float", "mul"}),             float_mul);
    DECLARE_VM_BUILTIN(name({"float", "lt"}),             float_lt);
    DECLARE_VM_BUILTIN(name({"float", "log"}),             float_log);
    DECLARE_VM_BUILTIN(name({"float", "to_string"}),             float_to_string);
    DECLARE_VM_BUILTIN(name({"float", "pi"}),             float_pi);
    DECLARE_VM_BUILTIN(name({"float", "float_of_int"}),             float_of_int);
  }

  void finalize_vm_float() {

  }
  // add, sub, mul, log, lt
}
