#include <stdio.h>
#include <lean/lean.h>

// TODO
// extern uint64_t my_map(lean_obj_arg);

extern void lean_initialize_runtime_module();
extern void lean_initialize();
extern void lean_io_mark_end_initialization();
extern lean_object * initialize_MapArray(uint8_t builtin, lean_object *);

int main() {
  lean_initialize_runtime_module();
  lean_object * res;
  // Use same default as for Lean executables
  // See https://github.com/leanprover/lean4/blob/master/doc/dev/ffi.md#initialization
  uint8_t builtin = 1;
  res = initialize_MapArray(builtin, lean_io_mk_world());
  if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
  } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      return 1;  // do not access Lean declarations if initialization failed
  }
  lean_io_mark_end_initialization();

  // TODO actual program

  // lean_object * s = lean_mk_string("hello!");
  // uint64_t l = my_length(s);
  // printf("output: %ld\n", l);
  printf("Hello world\n");
}
