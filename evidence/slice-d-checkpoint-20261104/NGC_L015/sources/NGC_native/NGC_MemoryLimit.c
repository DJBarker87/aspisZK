// Lean compiler output
// Module: NGC_MemoryLimit
// Imports: public import Init public meta import Init import all Lean.Shell
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_internal_set_max_memory(size_t);
static lean_once_cell_t l_NFA__MemoryLimit_set___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_NFA__MemoryLimit_set___closed__0;
LEAN_EXPORT lean_object* l_NFA__MemoryLimit_set();
LEAN_EXPORT lean_object* l_NFA__MemoryLimit_set___boxed(lean_object*);
static size_t _init_l_NFA__MemoryLimit_set___closed__0(void){
_start:
{
size_t v___x_1_; size_t v___x_2_; size_t v___x_3_; 
v___x_1_ = ((size_t)10ULL);
v___x_2_ = ((size_t)7168000ULL);
v___x_3_ = lean_usize_shift_left(v___x_2_, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_NFA__MemoryLimit_set(){
_start:
{
size_t v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_usize_once(&l_NFA__MemoryLimit_set___closed__0, &l_NFA__MemoryLimit_set___closed__0_once, _init_l_NFA__MemoryLimit_set___closed__0);
v___x_6_ = lean_internal_set_max_memory(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_NFA__MemoryLimit_set___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_NFA__MemoryLimit_set();
return v_res_8_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Shell(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_NGC__MemoryLimit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Shell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_NGC__MemoryLimit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Shell(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NGC__MemoryLimit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Shell(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_NGC__MemoryLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_NGC__MemoryLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_NGC__MemoryLimit(builtin);
}
#ifdef __cplusplus
}
#endif
