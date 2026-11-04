// Lean compiler output
// Module: NFO_Coherence
// Imports: public import Init public meta import Init public import Lean public import NFO_MemoryLimit
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_NFO__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_NFO__Coherence_referenceNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NFO__Coherence_referenceNames___closed__0 = (const lean_object*)&l_NFO__Coherence_referenceNames___closed__0_value;
LEAN_EXPORT lean_object* l_NFO__Coherence_referenceNames(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declarations"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edges"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dangling"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___redArg___closed__0 = (const lean_object*)&l_main___redArg___closed__0_value;
static const lean_string_object l_main___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NFO_Final"};
static const lean_object* l_main___redArg___closed__1 = (const lean_object*)&l_main___redArg___closed__1_value;
static const lean_ctor_object l_main___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(126, 20, 98, 60, 89, 5, 155, 154)}};
static const lean_object* l_main___redArg___closed__2 = (const lean_object*)&l_main___redArg___closed__2_value;
static const lean_ctor_object l_main___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__3 = (const lean_object*)&l_main___redArg___closed__3_value;
static const lean_array_object l_main___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___redArg___closed__3_value)}};
static const lean_object* l_main___redArg___closed__4 = (const lean_object*)&l_main___redArg___closed__4_value;
static const lean_array_object l_main___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___redArg___closed__5 = (const lean_object*)&l_main___redArg___closed__5_value;
static const lean_string_object l_main___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFO_LOADED.jsonl"};
static const lean_object* l_main___redArg___closed__6 = (const lean_object*)&l_main___redArg___closed__6_value;
static const lean_ctor_object l_main___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__7 = (const lean_object*)&l_main___redArg___closed__7_value;
static const lean_ctor_object l_main___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__7_value)}};
static const lean_object* l_main___redArg___closed__8 = (const lean_object*)&l_main___redArg___closed__8_value;
static const lean_string_object l_main___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modules"};
static const lean_object* l_main___redArg___closed__9 = (const lean_object*)&l_main___redArg___closed__9_value;
static const lean_string_object l_main___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dangling_references"};
static const lean_object* l_main___redArg___closed__10 = (const lean_object*)&l_main___redArg___closed__10_value;
static const lean_string_object l_main___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_main___redArg___closed__11 = (const lean_object*)&l_main___redArg___closed__11_value;
static const lean_string_object l_main___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "loaded NFO closure; raw import lists reported, no independent upstream import baseline comparison"};
static const lean_object* l_main___redArg___closed__12 = (const lean_object*)&l_main___redArg___closed__12_value;
static const lean_ctor_object l_main___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_main___redArg___closed__12_value)}};
static const lean_object* l_main___redArg___closed__13 = (const lean_object*)&l_main___redArg___closed__13_value;
static const lean_ctor_object l_main___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__11_value),((lean_object*)&l_main___redArg___closed__13_value)}};
static const lean_object* l_main___redArg___closed__14 = (const lean_object*)&l_main___redArg___closed__14_value;
static const lean_ctor_object l_main___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___redArg___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__15 = (const lean_object*)&l_main___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__2;
LEAN_EXPORT lean_object* l_main___redArg();
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg(lean_object* v_as_x27_1_, lean_object* v_b_2_){
_start:
{
if (lean_obj_tag(v_as_x27_1_) == 0)
{
return v_b_2_;
}
else
{
lean_object* v_head_3_; lean_object* v_tail_4_; lean_object* v_ctor_5_; lean_object* v_rhs_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_head_3_ = lean_ctor_get(v_as_x27_1_, 0);
v_tail_4_ = lean_ctor_get(v_as_x27_1_, 1);
v_ctor_5_ = lean_ctor_get(v_head_3_, 0);
v_rhs_6_ = lean_ctor_get(v_head_3_, 2);
lean_inc(v_ctor_5_);
v___x_7_ = lean_array_push(v_b_2_, v_ctor_5_);
lean_inc_ref(v_rhs_6_);
v___x_8_ = l_Lean_Expr_getUsedConstants(v_rhs_6_);
v___x_9_ = l_Array_append___redArg(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
v_as_x27_1_ = v_tail_4_;
v_b_2_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg___boxed(lean_object* v_as_x27_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg(v_as_x27_11_, v_b_12_);
lean_dec(v_as_x27_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_NFO__Coherence_referenceNames(lean_object* v_c_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___y_20_; uint8_t v___x_50_; lean_object* v___x_51_; 
v___x_17_ = l_Lean_ConstantInfo_type(v_c_16_);
v___x_18_ = l_Lean_Expr_getUsedConstants(v___x_17_);
v___x_50_ = 1;
lean_inc_ref(v_c_16_);
v___x_51_ = l_Lean_ConstantInfo_value_x3f(v_c_16_, v___x_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_NFO__Coherence_referenceNames___closed__0));
v___y_20_ = v___x_52_;
goto v___jp_19_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
v_val_53_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_val_53_);
lean_dec_ref_known(v___x_51_, 1);
v___x_54_ = l_Lean_Expr_getUsedConstants(v_val_53_);
v___y_20_ = v___x_54_;
goto v___jp_19_;
}
v___jp_19_:
{
lean_object* v_refs_21_; 
v_refs_21_ = l_Array_append___redArg(v___x_18_, v___y_20_);
lean_dec_ref(v___y_20_);
switch(lean_obj_tag(v_c_16_))
{
case 1:
{
lean_object* v_val_22_; lean_object* v_all_23_; lean_object* v___x_24_; lean_object* v_refs_25_; 
v_val_22_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_22_);
lean_dec_ref_known(v_c_16_, 1);
v_all_23_ = lean_ctor_get(v_val_22_, 3);
lean_inc(v_all_23_);
lean_dec_ref(v_val_22_);
v___x_24_ = lean_array_mk(v_all_23_);
v_refs_25_ = l_Array_append___redArg(v_refs_21_, v___x_24_);
lean_dec_ref(v___x_24_);
return v_refs_25_;
}
case 2:
{
lean_object* v_val_26_; lean_object* v_all_27_; lean_object* v___x_28_; lean_object* v_refs_29_; 
v_val_26_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_26_);
lean_dec_ref_known(v_c_16_, 1);
v_all_27_ = lean_ctor_get(v_val_26_, 2);
lean_inc(v_all_27_);
lean_dec_ref(v_val_26_);
v___x_28_ = lean_array_mk(v_all_27_);
v_refs_29_ = l_Array_append___redArg(v_refs_21_, v___x_28_);
lean_dec_ref(v___x_28_);
return v_refs_29_;
}
case 3:
{
lean_object* v_val_30_; lean_object* v_all_31_; lean_object* v___x_32_; lean_object* v_refs_33_; 
v_val_30_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_30_);
lean_dec_ref_known(v_c_16_, 1);
v_all_31_ = lean_ctor_get(v_val_30_, 2);
lean_inc(v_all_31_);
lean_dec_ref(v_val_30_);
v___x_32_ = lean_array_mk(v_all_31_);
v_refs_33_ = l_Array_append___redArg(v_refs_21_, v___x_32_);
lean_dec_ref(v___x_32_);
return v_refs_33_;
}
case 5:
{
lean_object* v_val_34_; lean_object* v_all_35_; lean_object* v_ctors_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_refs_40_; 
v_val_34_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_34_);
lean_dec_ref_known(v_c_16_, 1);
v_all_35_ = lean_ctor_get(v_val_34_, 3);
lean_inc(v_all_35_);
v_ctors_36_ = lean_ctor_get(v_val_34_, 4);
lean_inc(v_ctors_36_);
lean_dec_ref(v_val_34_);
v___x_37_ = lean_array_mk(v_ctors_36_);
v___x_38_ = l_Array_append___redArg(v_refs_21_, v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = lean_array_mk(v_all_35_);
v_refs_40_ = l_Array_append___redArg(v___x_38_, v___x_39_);
lean_dec_ref(v___x_39_);
return v_refs_40_;
}
case 6:
{
lean_object* v_val_41_; lean_object* v_induct_42_; lean_object* v_refs_43_; 
v_val_41_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_41_);
lean_dec_ref_known(v_c_16_, 1);
v_induct_42_ = lean_ctor_get(v_val_41_, 1);
lean_inc(v_induct_42_);
lean_dec_ref(v_val_41_);
v_refs_43_ = lean_array_push(v_refs_21_, v_induct_42_);
return v_refs_43_;
}
case 7:
{
lean_object* v_val_44_; lean_object* v_all_45_; lean_object* v_rules_46_; lean_object* v___x_47_; lean_object* v_refs_48_; lean_object* v___x_49_; 
v_val_44_ = lean_ctor_get(v_c_16_, 0);
lean_inc_ref(v_val_44_);
lean_dec_ref_known(v_c_16_, 1);
v_all_45_ = lean_ctor_get(v_val_44_, 1);
lean_inc(v_all_45_);
v_rules_46_ = lean_ctor_get(v_val_44_, 6);
lean_inc(v_rules_46_);
lean_dec_ref(v_val_44_);
v___x_47_ = lean_array_mk(v_all_45_);
v_refs_48_ = l_Array_append___redArg(v_refs_21_, v___x_47_);
lean_dec_ref(v___x_47_);
v___x_49_ = l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg(v_rules_46_, v_refs_48_);
lean_dec(v_rules_46_);
return v___x_49_;
}
default: 
{
lean_dec_ref(v_c_16_);
return v_refs_21_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0(lean_object* v_as_55_, lean_object* v_as_x27_56_, lean_object* v_b_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___redArg(v_as_x27_56_, v_b_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0___boxed(lean_object* v_as_60_, lean_object* v_as_x27_61_, lean_object* v_b_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_forIn_x27_loop___at___00NFO__Coherence_referenceNames_spec__0(v_as_60_, v_as_x27_61_, v_b_62_, v_a_63_);
lean_dec(v_as_x27_61_);
lean_dec(v_as_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(lean_object* v___x_67_, lean_object* v_val_68_, lean_object* v_as_69_, size_t v_sz_70_, size_t v_i_71_, lean_object* v_b_72_){
_start:
{
lean_object* v_a_75_; uint8_t v___x_79_; 
v___x_79_ = lean_usize_dec_lt(v_i_71_, v_sz_70_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_dec_ref(v___x_67_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_b_72_);
return v___x_80_;
}
else
{
lean_object* v_fst_81_; lean_object* v_snd_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_112_; 
v_fst_81_ = lean_ctor_get(v_b_72_, 0);
v_snd_82_ = lean_ctor_get(v_b_72_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_b_72_);
if (v_isSharedCheck_112_ == 0)
{
v___x_84_ = v_b_72_;
v_isShared_85_ = v_isSharedCheck_112_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_snd_82_);
lean_inc(v_fst_81_);
lean_dec(v_b_72_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_112_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_checked_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_checked_86_ = lean_ctor_get(v___x_67_, 2);
v___x_87_ = lean_unsigned_to_nat(1u);
v_a_88_ = lean_array_uget_borrowed(v_as_69_, v_i_71_);
v___x_89_ = lean_nat_add(v_snd_82_, v___x_87_);
lean_dec(v_snd_82_);
lean_inc_ref(v_checked_86_);
v___x_90_ = lean_task_get_own(v_checked_86_);
lean_inc(v_a_88_);
v___x_91_ = lean_environment_find(v___x_90_, v_a_88_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_92_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0));
v___x_93_ = l_Lean_ConstantInfo_name(v_val_68_);
v___x_94_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_93_, v___x_79_);
v___x_95_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_95_);
lean_ctor_set(v___x_84_, 0, v___x_92_);
v___x_97_ = v___x_84_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_108_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_98_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__1));
lean_inc(v_a_88_);
v___x_99_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_88_, v___x_79_);
v___x_100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_98_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_box(0);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_97_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = l_Lean_Json_mkObj(v___x_104_);
lean_dec_ref_known(v___x_104_, 2);
v___x_106_ = lean_array_push(v_fst_81_, v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_89_);
v_a_75_ = v___x_107_;
goto v___jp_74_;
}
}
else
{
lean_object* v___x_110_; 
lean_dec_ref_known(v___x_91_, 1);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_89_);
v___x_110_ = v___x_84_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_fst_81_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_89_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v_a_75_ = v___x_110_;
goto v___jp_74_;
}
}
}
}
v___jp_74_:
{
size_t v___x_76_; size_t v___x_77_; 
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_71_, v___x_76_);
v_i_71_ = v___x_77_;
v_b_72_ = v_a_75_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___boxed(lean_object* v___x_113_, lean_object* v_val_114_, lean_object* v_as_115_, lean_object* v_sz_116_, lean_object* v_i_117_, lean_object* v_b_118_, lean_object* v___y_119_){
_start:
{
size_t v_sz_boxed_120_; size_t v_i_boxed_121_; lean_object* v_res_122_; 
v_sz_boxed_120_ = lean_unbox_usize(v_sz_116_);
lean_dec(v_sz_116_);
v_i_boxed_121_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(v___x_113_, v_val_114_, v_as_115_, v_sz_boxed_120_, v_i_boxed_121_, v_b_118_);
lean_dec_ref(v_as_115_);
lean_dec_ref(v_val_114_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v___x_123_, lean_object* v_as_124_, size_t v_sz_125_, size_t v_i_126_, lean_object* v_b_127_){
_start:
{
lean_object* v_a_130_; uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_lt(v_i_126_, v_sz_125_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec_ref(v___x_123_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v_b_127_);
return v___x_135_;
}
else
{
lean_object* v_snd_136_; lean_object* v_fst_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_200_; 
v_snd_136_ = lean_ctor_get(v_b_127_, 1);
v_fst_137_ = lean_ctor_get(v_b_127_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_b_127_);
if (v_isSharedCheck_200_ == 0)
{
v___x_139_ = v_b_127_;
v_isShared_140_ = v_isSharedCheck_200_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_136_);
lean_inc(v_fst_137_);
lean_dec(v_b_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_200_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_fst_141_; lean_object* v_snd_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_199_; 
v_fst_141_ = lean_ctor_get(v_snd_136_, 0);
v_snd_142_ = lean_ctor_get(v_snd_136_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_snd_136_);
if (v_isSharedCheck_199_ == 0)
{
v___x_144_ = v_snd_136_;
v_isShared_145_ = v_isSharedCheck_199_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snd_142_);
lean_inc(v_fst_141_);
lean_dec(v_snd_136_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_199_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_checked_146_; lean_object* v___x_147_; lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_checked_146_ = lean_ctor_get(v___x_123_, 2);
v___x_147_ = lean_unsigned_to_nat(1u);
v_a_148_ = lean_array_uget_borrowed(v_as_124_, v_i_126_);
v___x_149_ = lean_nat_add(v_fst_137_, v___x_147_);
lean_dec(v_fst_137_);
lean_inc_ref(v_checked_146_);
v___x_150_ = lean_task_get_own(v_checked_146_);
v___x_151_ = l_Lean_ConstantInfo_name(v_a_148_);
lean_inc(v___x_151_);
v___x_152_ = lean_environment_find(v___x_150_, v___x_151_);
if (lean_obj_tag(v___x_152_) == 1)
{
lean_object* v_val_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
lean_dec(v___x_151_);
v_val_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc_n(v_val_153_, 2);
lean_dec_ref_known(v___x_152_, 1);
v___x_154_ = l_NFO__Coherence_referenceNames(v_val_153_);
if (v_isShared_145_ == 0)
{
v___x_156_ = v___x_144_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_141_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_snd_142_);
v___x_156_ = v_reuseFailAlloc_181_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
size_t v_sz_157_; size_t v___x_158_; lean_object* v___x_159_; 
v_sz_157_ = lean_array_size(v___x_154_);
v___x_158_ = ((size_t)0ULL);
lean_inc_ref(v___x_123_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0(v___x_123_, v_val_153_, v___x_154_, v_sz_157_, v___x_158_, v___x_156_);
lean_dec_ref(v___x_154_);
lean_dec(v_val_153_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v_fst_161_ = lean_ctor_get(v_a_160_, 0);
v_snd_162_ = lean_ctor_get(v_a_160_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v_a_160_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snd_162_);
lean_inc(v_fst_161_);
lean_dec(v_a_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_fst_161_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_snd_162_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_169_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_167_);
lean_ctor_set(v___x_139_, 0, v___x_149_);
v___x_169_ = v___x_139_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
v_a_130_ = v___x_169_;
goto v___jp_129_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v___x_149_);
lean_del_object(v___x_139_);
lean_dec_ref(v___x_123_);
v_a_173_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_159_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_159_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v___x_152_);
v___x_182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__0));
v___x_183_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_151_, v___x_134_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_inc_ref(v___x_184_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 1, v___x_184_);
lean_ctor_set(v___x_144_, 0, v___x_182_);
v___x_186_ = v___x_144_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_198_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__0___closed__1));
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_184_);
lean_ctor_set(v___x_139_, 0, v___x_187_);
v___x_189_ = v___x_139_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_184_);
v___x_189_ = v_reuseFailAlloc_197_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Json_mkObj(v___x_192_);
lean_dec_ref_known(v___x_192_, 2);
v___x_194_ = lean_array_push(v_fst_141_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_snd_142_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_149_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v_a_130_ = v___x_196_;
goto v___jp_129_;
}
}
}
}
}
}
v___jp_129_:
{
size_t v___x_131_; size_t v___x_132_; 
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_126_, v___x_131_);
v_i_126_ = v___x_132_;
v_b_127_ = v_a_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v___x_201_, lean_object* v_as_202_, lean_object* v_sz_203_, lean_object* v_i_204_, lean_object* v_b_205_, lean_object* v___y_206_){
_start:
{
size_t v_sz_boxed_207_; size_t v_i_boxed_208_; lean_object* v_res_209_; 
v_sz_boxed_207_ = lean_unbox_usize(v_sz_203_);
lean_dec(v_sz_203_);
v_i_boxed_208_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_201_, v_as_202_, v_sz_boxed_207_, v_i_boxed_208_, v_b_205_);
lean_dec_ref(v_as_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t v_sz_210_, size_t v_i_211_, lean_object* v_bs_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = lean_usize_dec_lt(v_i_211_, v_sz_210_);
if (v___x_213_ == 0)
{
return v_bs_212_;
}
else
{
lean_object* v_v_214_; lean_object* v_module_215_; lean_object* v___x_216_; lean_object* v_bs_x27_217_; lean_object* v___x_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v___x_221_; 
v_v_214_ = lean_array_uget_borrowed(v_bs_212_, v_i_211_);
v_module_215_ = lean_ctor_get(v_v_214_, 0);
lean_inc(v_module_215_);
v___x_216_ = lean_unsigned_to_nat(0u);
v_bs_x27_217_ = lean_array_uset(v_bs_212_, v_i_211_, v___x_216_);
v___x_218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_215_, v___x_213_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_211_, v___x_219_);
v___x_221_ = lean_array_uset(v_bs_x27_217_, v_i_211_, v___x_218_);
v_i_211_ = v___x_220_;
v_bs_212_ = v___x_221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object* v_sz_223_, lean_object* v_i_224_, lean_object* v_bs_225_){
_start:
{
size_t v_sz_boxed_226_; size_t v_i_boxed_227_; lean_object* v_res_228_; 
v_sz_boxed_226_ = lean_unbox_usize(v_sz_223_);
lean_dec(v_sz_223_);
v_i_boxed_227_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_res_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_boxed_226_, v_i_boxed_227_, v_bs_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v_a_242_, lean_object* v_range_243_, lean_object* v_b_244_, lean_object* v_i_245_){
_start:
{
lean_object* v_stop_247_; lean_object* v_step_248_; uint8_t v___x_249_; 
v_stop_247_ = lean_ctor_get(v_range_243_, 1);
v_step_248_ = lean_ctor_get(v_range_243_, 2);
v___x_249_ = lean_nat_dec_lt(v_i_245_, v_stop_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_i_245_);
lean_dec_ref(v___x_240_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_b_244_);
return v___x_250_;
}
else
{
lean_object* v_snd_251_; lean_object* v_fst_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_348_; 
v_snd_251_ = lean_ctor_get(v_b_244_, 1);
v_fst_252_ = lean_ctor_get(v_b_244_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_b_244_);
if (v_isSharedCheck_348_ == 0)
{
v___x_254_ = v_b_244_;
v_isShared_255_ = v_isSharedCheck_348_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_251_);
lean_inc(v_fst_252_);
lean_dec(v_b_244_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_348_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_347_; 
v_fst_256_ = lean_ctor_get(v_snd_251_, 0);
v_snd_257_ = lean_ctor_get(v_snd_251_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_snd_251_);
if (v_isSharedCheck_347_ == 0)
{
v___x_259_ = v_snd_251_;
v_isShared_260_ = v_isSharedCheck_347_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snd_257_);
lean_inc(v_fst_256_);
lean_dec(v_snd_251_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_347_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_moduleData_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_imports_264_; lean_object* v_constants_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v_moduleData_261_ = lean_ctor_get(v___x_239_, 6);
v___x_262_ = l_Lean_instInhabitedModuleData_default;
v___x_263_ = lean_array_get_borrowed(v___x_262_, v_moduleData_261_, v_i_245_);
v_imports_264_ = lean_ctor_get(v___x_263_, 0);
v_constants_265_ = lean_ctor_get(v___x_263_, 2);
v___x_266_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__1));
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_266_);
v___x_268_ = v___x_259_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_fst_256_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_346_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
size_t v_sz_269_; size_t v___x_270_; lean_object* v___x_271_; 
v_sz_269_ = lean_array_size(v_constants_265_);
v___x_270_ = ((size_t)0ULL);
lean_inc_ref(v___x_240_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_240_, v_constants_265_, v_sz_269_, v___x_270_, v___x_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_snd_273_; lean_object* v_fst_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_337_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v_snd_273_ = lean_ctor_get(v_a_272_, 1);
v_fst_274_ = lean_ctor_get(v_a_272_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_a_272_);
if (v_isSharedCheck_337_ == 0)
{
v___x_276_ = v_a_272_;
v_isShared_277_ = v_isSharedCheck_337_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snd_273_);
lean_inc(v_fst_274_);
lean_dec(v_a_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_337_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_336_; 
v_fst_278_ = lean_ctor_get(v_snd_273_, 0);
v_snd_279_ = lean_ctor_get(v_snd_273_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_snd_273_);
if (v_isSharedCheck_336_ == 0)
{
v___x_281_ = v_snd_273_;
v_isShared_282_ = v_isSharedCheck_336_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
lean_dec(v_snd_273_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_336_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_array_get_borrowed(v___x_283_, v___x_241_, v_i_245_);
v___x_285_ = lean_nat_add(v_snd_257_, v_snd_279_);
lean_dec(v_snd_257_);
v___x_286_ = lean_array_get_size(v_fst_278_);
v___x_287_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__2));
lean_inc(v___x_284_);
v___x_288_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_284_, v___x_249_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_289_);
lean_ctor_set(v___x_281_, 0, v___x_287_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_335_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; size_t v_sz_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_292_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__3));
v_sz_293_ = lean_array_size(v_imports_264_);
lean_inc_ref(v_imports_264_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_293_, v___x_270_, v_imports_264_);
v___x_295_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_294_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_295_);
lean_ctor_set(v___x_276_, 0, v___x_292_);
v___x_297_ = v___x_276_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_334_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_298_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4));
v___x_299_ = lean_array_get_size(v_constants_265_);
v___x_300_ = l_Lean_JsonNumber_fromNat(v___x_299_);
v___x_301_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_301_);
lean_ctor_set(v___x_254_, 0, v___x_298_);
v___x_303_ = v___x_254_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_333_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_304_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5));
v___x_305_ = l_Lean_JsonNumber_fromNat(v_snd_279_);
v___x_306_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__6));
v___x_309_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_278_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_307_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_303_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_297_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_291_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_Json_mkObj(v___x_316_);
lean_dec_ref_known(v___x_316_, 2);
v___x_318_ = l_Lean_Json_compress(v___x_317_);
v___x_319_ = l_IO_FS_Handle_putStrLn(v_a_242_, v___x_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref_known(v___x_319_, 1);
v___x_320_ = lean_nat_add(v_fst_252_, v___x_286_);
lean_dec(v_fst_252_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_fst_274_);
lean_ctor_set(v___x_321_, 1, v___x_285_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_nat_add(v_i_245_, v_step_248_);
lean_dec(v_i_245_);
v_b_244_ = v___x_322_;
v_i_245_ = v___x_323_;
goto _start;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v___x_285_);
lean_dec(v_fst_274_);
lean_dec(v_fst_252_);
lean_dec(v_i_245_);
lean_dec_ref(v___x_240_);
v_a_325_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_319_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_319_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_snd_257_);
lean_del_object(v___x_254_);
lean_dec(v_fst_252_);
lean_dec(v_i_245_);
lean_dec_ref(v___x_240_);
v_a_338_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_271_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_271_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_a_352_, lean_object* v_range_353_, lean_object* v_b_354_, lean_object* v_i_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v___x_349_, v___x_350_, v___x_351_, v_a_352_, v_range_353_, v_b_354_, v_i_355_);
lean_dec_ref(v_range_353_);
lean_dec(v_a_352_);
lean_dec_ref(v___x_351_);
lean_dec_ref(v___x_349_);
return v_res_357_;
}
}
static lean_object* _init_l_main___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_390_; lean_object* v___x_391_; 
v___x_390_ = 1;
v___x_391_ = lean_box_uint32(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_main___redArg___boxed__const__2(void){
_start:
{
uint32_t v___x_392_; lean_object* v___x_393_; 
v___x_392_ = 0;
v___x_393_ = lean_box_uint32(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_main___redArg(){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = l_NFO__MemoryLimit_set();
v___x_396_ = ((lean_object*)(l_main___redArg___closed__0));
v___x_397_ = l_Lean_findSysroot(v___x_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = lean_box(0);
v___x_400_ = l_Lean_initSearchPath(v_a_398_, v___x_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_401_) == 0)
{
uint8_t v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint32_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref_known(v___x_401_, 1);
v___x_402_ = 1;
v___x_403_ = 0;
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = ((lean_object*)(l_main___redArg___closed__4));
v___x_406_ = l_Lean_Options_empty;
v___x_407_ = 0;
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = ((lean_object*)(l_main___redArg___closed__5));
v___x_410_ = 2;
v___x_411_ = lean_box(1);
v___x_412_ = l_Lean_importModules(v___x_405_, v___x_406_, v___x_407_, v___x_409_, v___x_403_, v___x_402_, v___x_410_, v___x_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = ((lean_object*)(l_main___redArg___closed__6));
v___x_415_ = 1;
v___x_416_ = lean_io_prim_handle_mk(v___x_414_, v___x_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = l_Lean_Environment_setExporting(v_a_413_, v___x_403_);
v___x_419_ = l_Lean_Environment_header(v___x_418_);
lean_inc_ref(v___x_419_);
v___x_420_ = l_Lean_EnvironmentHeader_moduleNames(v___x_419_);
v___x_421_ = lean_array_get_size(v___x_420_);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_408_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_ctor_set(v___x_422_, 2, v___x_404_);
v___x_423_ = ((lean_object*)(l_main___redArg___closed__8));
v___x_424_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v___x_419_, v___x_418_, v___x_420_, v_a_417_, v___x_422_, v___x_423_, v___x_408_);
lean_dec_ref_known(v___x_422_, 3);
lean_dec(v_a_417_);
lean_dec_ref(v___x_420_);
lean_dec_ref(v___x_419_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_snd_426_; lean_object* v_fst_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_487_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v_snd_426_ = lean_ctor_get(v_a_425_, 1);
v_fst_427_ = lean_ctor_get(v_a_425_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_425_);
if (v_isSharedCheck_487_ == 0)
{
v___x_429_ = v_a_425_;
v_isShared_430_ = v_isSharedCheck_487_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_427_);
lean_dec(v_a_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_487_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_486_; 
v_fst_431_ = lean_ctor_get(v_snd_426_, 0);
v_snd_432_ = lean_ctor_get(v_snd_426_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_snd_426_);
if (v_isSharedCheck_486_ == 0)
{
v___x_434_ = v_snd_426_;
v_isShared_435_ = v_isSharedCheck_486_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_431_);
lean_dec(v_snd_426_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_486_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_436_ = ((lean_object*)(l_main___redArg___closed__9));
v___x_437_ = l_Lean_JsonNumber_fromNat(v___x_421_);
v___x_438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_438_);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_485_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4));
v___x_442_ = l_Lean_JsonNumber_fromNat(v_fst_431_);
v___x_443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_443_);
lean_ctor_set(v___x_429_, 0, v___x_441_);
v___x_445_ = v___x_429_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_443_);
v___x_445_ = v_reuseFailAlloc_484_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_446_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5));
v___x_447_ = l_Lean_JsonNumber_fromNat(v_snd_432_);
v___x_448_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_446_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_main___redArg___closed__10));
lean_inc(v_fst_427_);
v___x_451_ = l_Lean_JsonNumber_fromNat(v_fst_427_);
v___x_452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = ((lean_object*)(l_main___redArg___closed__15));
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_449_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_445_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_440_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_Json_mkObj(v___x_458_);
lean_dec_ref_known(v___x_458_, 2);
v___x_460_ = l_Lean_Json_compress(v___x_459_);
v___x_461_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_474_; 
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_475_);
v___x_463_ = v___x_461_;
v_isShared_464_ = v_isSharedCheck_474_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_461_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_474_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = lean_nat_dec_eq(v_fst_427_, v___x_408_);
lean_dec(v_fst_427_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l_main___redArg___boxed__const__1;
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = l_main___redArg___boxed__const__2;
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_470_);
v___x_472_ = v___x_463_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_fst_427_);
v_a_476_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_461_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_461_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
v_a_488_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_424_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_424_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_a_413_);
v_a_496_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_416_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_416_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_412_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_412_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_401_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_401_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_400_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_400_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_397_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_397_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_main___redArg();
return v_res_537_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v___args_538_){
_start:
{
lean_object* v___x_540_; 
lean_dec(v___args_538_);
v___x_540_ = l_main___redArg();
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v___args_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = _lean_main(v___args_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_a_547_, lean_object* v_range_548_, lean_object* v_b_549_, lean_object* v_i_550_, lean_object* v_hs_551_, lean_object* v_hl_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v___x_544_, v___x_545_, v___x_546_, v_a_547_, v_range_548_, v_b_549_, v_i_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_a_558_, lean_object* v_range_559_, lean_object* v_b_560_, lean_object* v_i_561_, lean_object* v_hs_562_, lean_object* v_hl_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(v___x_555_, v___x_556_, v___x_557_, v_a_558_, v_range_559_, v_b_560_, v_i_561_, v_hs_562_, v_hl_563_);
lean_dec_ref(v_range_559_);
lean_dec(v_a_558_);
lean_dec_ref(v___x_557_);
lean_dec_ref(v___x_555_);
return v_res_565_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFO__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFO__Coherence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NFO__MemoryLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___redArg___boxed__const__1 = _init_l_main___redArg___boxed__const__1();
lean_mark_persistent(l_main___redArg___boxed__const__1);
l_main___redArg___boxed__const__2 = _init_l_main___redArg___boxed__const__2();
lean_mark_persistent(l_main___redArg___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = initialize_NFO__Coherence(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
