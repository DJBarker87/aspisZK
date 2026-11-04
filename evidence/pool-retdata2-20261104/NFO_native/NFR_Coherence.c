// Lean compiler output
// Module: NFR_Coherence
// Imports: public import Init public meta import Init public import Lean public import NFR_MemoryLimit
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_NFR__Coherence_referenceNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NFR__Coherence_referenceNames___closed__0 = (const lean_object*)&l_NFR__Coherence_referenceNames___closed__0_value;
LEAN_EXPORT lean_object* l_NFR__Coherence_referenceNames(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_main___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFR_AfterstateForward"};
static const lean_object* l_main___redArg___closed__1 = (const lean_object*)&l_main___redArg___closed__1_value;
static const lean_ctor_object l_main___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 107, 170, 101, 222, 163, 90, 186)}};
static const lean_object* l_main___redArg___closed__2 = (const lean_object*)&l_main___redArg___closed__2_value;
static const lean_ctor_object l_main___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__3 = (const lean_object*)&l_main___redArg___closed__3_value;
static const lean_string_object l_main___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_AfterstateForward00"};
static const lean_object* l_main___redArg___closed__4 = (const lean_object*)&l_main___redArg___closed__4_value;
static const lean_ctor_object l_main___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(64, 191, 200, 213, 26, 78, 32, 215)}};
static const lean_object* l_main___redArg___closed__5 = (const lean_object*)&l_main___redArg___closed__5_value;
static const lean_ctor_object l_main___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__6 = (const lean_object*)&l_main___redArg___closed__6_value;
static const lean_string_object l_main___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_AfterstateForward04"};
static const lean_object* l_main___redArg___closed__7 = (const lean_object*)&l_main___redArg___closed__7_value;
static const lean_ctor_object l_main___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 245, 203, 138, 39, 129, 111, 172)}};
static const lean_object* l_main___redArg___closed__8 = (const lean_object*)&l_main___redArg___closed__8_value;
static const lean_ctor_object l_main___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__9 = (const lean_object*)&l_main___redArg___closed__9_value;
static const lean_string_object l_main___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_AfterstateForward08"};
static const lean_object* l_main___redArg___closed__10 = (const lean_object*)&l_main___redArg___closed__10_value;
static const lean_ctor_object l_main___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(95, 127, 174, 84, 245, 93, 171, 99)}};
static const lean_object* l_main___redArg___closed__11 = (const lean_object*)&l_main___redArg___closed__11_value;
static const lean_ctor_object l_main___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__12 = (const lean_object*)&l_main___redArg___closed__12_value;
static const lean_string_object l_main___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_AfterstateForward12"};
static const lean_object* l_main___redArg___closed__13 = (const lean_object*)&l_main___redArg___closed__13_value;
static const lean_ctor_object l_main___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(87, 194, 172, 198, 191, 109, 159, 123)}};
static const lean_object* l_main___redArg___closed__14 = (const lean_object*)&l_main___redArg___closed__14_value;
static const lean_ctor_object l_main___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__15 = (const lean_object*)&l_main___redArg___closed__15_value;
static const lean_string_object l_main___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_AfterstateForward16"};
static const lean_object* l_main___redArg___closed__16 = (const lean_object*)&l_main___redArg___closed__16_value;
static const lean_ctor_object l_main___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(213, 197, 172, 244, 219, 97, 251, 215)}};
static const lean_object* l_main___redArg___closed__17 = (const lean_object*)&l_main___redArg___closed__17_value;
static const lean_ctor_object l_main___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__18 = (const lean_object*)&l_main___redArg___closed__18_value;
static const lean_string_object l_main___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "NFR_AfterstateForwardHelpers"};
static const lean_object* l_main___redArg___closed__19 = (const lean_object*)&l_main___redArg___closed__19_value;
static const lean_ctor_object l_main___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(169, 35, 95, 139, 102, 163, 39, 225)}};
static const lean_object* l_main___redArg___closed__20 = (const lean_object*)&l_main___redArg___closed__20_value;
static const lean_ctor_object l_main___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__21 = (const lean_object*)&l_main___redArg___closed__21_value;
static const lean_string_object l_main___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFR_CHelper"};
static const lean_object* l_main___redArg___closed__22 = (const lean_object*)&l_main___redArg___closed__22_value;
static const lean_ctor_object l_main___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(165, 224, 53, 95, 74, 51, 8, 57)}};
static const lean_object* l_main___redArg___closed__23 = (const lean_object*)&l_main___redArg___closed__23_value;
static const lean_ctor_object l_main___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__24 = (const lean_object*)&l_main___redArg___closed__24_value;
static const lean_string_object l_main___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFR_CHelperBridge"};
static const lean_object* l_main___redArg___closed__25 = (const lean_object*)&l_main___redArg___closed__25_value;
static const lean_ctor_object l_main___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(158, 167, 248, 207, 28, 172, 31, 109)}};
static const lean_object* l_main___redArg___closed__26 = (const lean_object*)&l_main___redArg___closed__26_value;
static const lean_ctor_object l_main___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__27 = (const lean_object*)&l_main___redArg___closed__27_value;
static const lean_string_object l_main___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFR_CSettlement"};
static const lean_object* l_main___redArg___closed__28 = (const lean_object*)&l_main___redArg___closed__28_value;
static const lean_ctor_object l_main___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(176, 192, 156, 186, 79, 112, 18, 179)}};
static const lean_object* l_main___redArg___closed__29 = (const lean_object*)&l_main___redArg___closed__29_value;
static const lean_ctor_object l_main___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__30 = (const lean_object*)&l_main___redArg___closed__30_value;
static const lean_string_object l_main___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFR_DigestForward"};
static const lean_object* l_main___redArg___closed__31 = (const lean_object*)&l_main___redArg___closed__31_value;
static const lean_ctor_object l_main___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(148, 223, 161, 77, 94, 79, 112, 220)}};
static const lean_object* l_main___redArg___closed__32 = (const lean_object*)&l_main___redArg___closed__32_value;
static const lean_ctor_object l_main___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__33 = (const lean_object*)&l_main___redArg___closed__33_value;
static const lean_string_object l_main___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFR_ExtractedDecode"};
static const lean_object* l_main___redArg___closed__34 = (const lean_object*)&l_main___redArg___closed__34_value;
static const lean_ctor_object l_main___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__34_value),LEAN_SCALAR_PTR_LITERAL(178, 162, 97, 81, 138, 120, 124, 127)}};
static const lean_object* l_main___redArg___closed__35 = (const lean_object*)&l_main___redArg___closed__35_value;
static const lean_ctor_object l_main___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__36 = (const lean_object*)&l_main___redArg___closed__36_value;
static const lean_string_object l_main___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFR_ModelJoin"};
static const lean_object* l_main___redArg___closed__37 = (const lean_object*)&l_main___redArg___closed__37_value;
static const lean_ctor_object l_main___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(116, 216, 64, 123, 238, 226, 19, 255)}};
static const lean_object* l_main___redArg___closed__38 = (const lean_object*)&l_main___redArg___closed__38_value;
static const lean_ctor_object l_main___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__38_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__39 = (const lean_object*)&l_main___redArg___closed__39_value;
static const lean_string_object l_main___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFR_PoolReturnData"};
static const lean_object* l_main___redArg___closed__40 = (const lean_object*)&l_main___redArg___closed__40_value;
static const lean_ctor_object l_main___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(202, 77, 83, 17, 123, 187, 23, 51)}};
static const lean_object* l_main___redArg___closed__41 = (const lean_object*)&l_main___redArg___closed__41_value;
static const lean_ctor_object l_main___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__41_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__42 = (const lean_object*)&l_main___redArg___closed__42_value;
static const lean_string_object l_main___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFR_RawInverse"};
static const lean_object* l_main___redArg___closed__43 = (const lean_object*)&l_main___redArg___closed__43_value;
static const lean_ctor_object l_main___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(167, 150, 189, 4, 14, 15, 211, 68)}};
static const lean_object* l_main___redArg___closed__44 = (const lean_object*)&l_main___redArg___closed__44_value;
static const lean_ctor_object l_main___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__45 = (const lean_object*)&l_main___redArg___closed__45_value;
static const lean_string_object l_main___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NFR_RawInverseFrames"};
static const lean_object* l_main___redArg___closed__46 = (const lean_object*)&l_main___redArg___closed__46_value;
static const lean_ctor_object l_main___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__46_value),LEAN_SCALAR_PTR_LITERAL(104, 240, 116, 18, 10, 200, 239, 195)}};
static const lean_object* l_main___redArg___closed__47 = (const lean_object*)&l_main___redArg___closed__47_value;
static const lean_ctor_object l_main___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__47_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__48 = (const lean_object*)&l_main___redArg___closed__48_value;
static const lean_string_object l_main___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFR_RawInverseHelpers"};
static const lean_object* l_main___redArg___closed__49 = (const lean_object*)&l_main___redArg___closed__49_value;
static const lean_ctor_object l_main___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__49_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 36, 200, 159, 224, 34, 75)}};
static const lean_object* l_main___redArg___closed__50 = (const lean_object*)&l_main___redArg___closed__50_value;
static const lean_ctor_object l_main___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__50_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__51 = (const lean_object*)&l_main___redArg___closed__51_value;
static const lean_string_object l_main___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFR_RawInverseValidator"};
static const lean_object* l_main___redArg___closed__52 = (const lean_object*)&l_main___redArg___closed__52_value;
static const lean_ctor_object l_main___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(152, 141, 35, 108, 113, 11, 250, 42)}};
static const lean_object* l_main___redArg___closed__53 = (const lean_object*)&l_main___redArg___closed__53_value;
static const lean_ctor_object l_main___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__53_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__54 = (const lean_object*)&l_main___redArg___closed__54_value;
static const lean_string_object l_main___redArg___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFR_ResultForward"};
static const lean_object* l_main___redArg___closed__55 = (const lean_object*)&l_main___redArg___closed__55_value;
static const lean_ctor_object l_main___redArg___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__55_value),LEAN_SCALAR_PTR_LITERAL(235, 47, 199, 112, 158, 237, 106, 194)}};
static const lean_object* l_main___redArg___closed__56 = (const lean_object*)&l_main___redArg___closed__56_value;
static const lean_ctor_object l_main___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__56_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__57 = (const lean_object*)&l_main___redArg___closed__57_value;
static const lean_string_object l_main___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "NFR_ResultForwardHelpers"};
static const lean_object* l_main___redArg___closed__58 = (const lean_object*)&l_main___redArg___closed__58_value;
static const lean_ctor_object l_main___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__58_value),LEAN_SCALAR_PTR_LITERAL(222, 184, 135, 91, 18, 142, 148, 41)}};
static const lean_object* l_main___redArg___closed__59 = (const lean_object*)&l_main___redArg___closed__59_value;
static const lean_ctor_object l_main___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__59_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___redArg___closed__60 = (const lean_object*)&l_main___redArg___closed__60_value;
static const lean_array_object l_main___redArg___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*20, .m_other = 0, .m_tag = 246}, .m_size = 20, .m_capacity = 20, .m_data = {((lean_object*)&l_main___redArg___closed__3_value),((lean_object*)&l_main___redArg___closed__6_value),((lean_object*)&l_main___redArg___closed__9_value),((lean_object*)&l_main___redArg___closed__12_value),((lean_object*)&l_main___redArg___closed__15_value),((lean_object*)&l_main___redArg___closed__18_value),((lean_object*)&l_main___redArg___closed__21_value),((lean_object*)&l_main___redArg___closed__24_value),((lean_object*)&l_main___redArg___closed__27_value),((lean_object*)&l_main___redArg___closed__30_value),((lean_object*)&l_main___redArg___closed__33_value),((lean_object*)&l_main___redArg___closed__36_value),((lean_object*)&l_main___redArg___closed__39_value),((lean_object*)&l_main___redArg___closed__42_value),((lean_object*)&l_main___redArg___closed__45_value),((lean_object*)&l_main___redArg___closed__48_value),((lean_object*)&l_main___redArg___closed__51_value),((lean_object*)&l_main___redArg___closed__54_value),((lean_object*)&l_main___redArg___closed__57_value),((lean_object*)&l_main___redArg___closed__60_value)}};
static const lean_object* l_main___redArg___closed__61 = (const lean_object*)&l_main___redArg___closed__61_value;
static const lean_array_object l_main___redArg___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___redArg___closed__62 = (const lean_object*)&l_main___redArg___closed__62_value;
static const lean_string_object l_main___redArg___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFR_LOADED.jsonl"};
static const lean_object* l_main___redArg___closed__63 = (const lean_object*)&l_main___redArg___closed__63_value;
static const lean_ctor_object l_main___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__64 = (const lean_object*)&l_main___redArg___closed__64_value;
static const lean_ctor_object l_main___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__64_value)}};
static const lean_object* l_main___redArg___closed__65 = (const lean_object*)&l_main___redArg___closed__65_value;
static const lean_string_object l_main___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modules"};
static const lean_object* l_main___redArg___closed__66 = (const lean_object*)&l_main___redArg___closed__66_value;
static const lean_string_object l_main___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dangling_references"};
static const lean_object* l_main___redArg___closed__67 = (const lean_object*)&l_main___redArg___closed__67_value;
static const lean_string_object l_main___redArg___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_main___redArg___closed__68 = (const lean_object*)&l_main___redArg___closed__68_value;
static const lean_string_object l_main___redArg___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "loaded NFR closure; raw import lists reported, no independent upstream import baseline comparison"};
static const lean_object* l_main___redArg___closed__69 = (const lean_object*)&l_main___redArg___closed__69_value;
static const lean_ctor_object l_main___redArg___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_main___redArg___closed__69_value)}};
static const lean_object* l_main___redArg___closed__70 = (const lean_object*)&l_main___redArg___closed__70_value;
static const lean_ctor_object l_main___redArg___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__68_value),((lean_object*)&l_main___redArg___closed__70_value)}};
static const lean_object* l_main___redArg___closed__71 = (const lean_object*)&l_main___redArg___closed__71_value;
static const lean_ctor_object l_main___redArg___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___redArg___closed__71_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__72 = (const lean_object*)&l_main___redArg___closed__72_value;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__2;
LEAN_EXPORT lean_object* l_main___redArg();
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg(lean_object* v_as_x27_1_, lean_object* v_b_2_){
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg___boxed(lean_object* v_as_x27_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg(v_as_x27_11_, v_b_12_);
lean_dec(v_as_x27_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_NFR__Coherence_referenceNames(lean_object* v_c_16_){
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
v___x_52_ = ((lean_object*)(l_NFR__Coherence_referenceNames___closed__0));
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
v___x_49_ = l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg(v_rules_46_, v_refs_48_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0(lean_object* v_as_55_, lean_object* v_as_x27_56_, lean_object* v_b_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___redArg(v_as_x27_56_, v_b_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0___boxed(lean_object* v_as_60_, lean_object* v_as_x27_61_, lean_object* v_b_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_forIn_x27_loop___at___00NFR__Coherence_referenceNames_spec__0(v_as_60_, v_as_x27_61_, v_b_62_, v_a_63_);
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
v___x_154_ = l_NFR__Coherence_referenceNames(v_val_153_);
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
uint32_t v___x_561_; lean_object* v___x_562_; 
v___x_561_ = 1;
v___x_562_ = lean_box_uint32(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_main___redArg___boxed__const__2(void){
_start:
{
uint32_t v___x_563_; lean_object* v___x_564_; 
v___x_563_ = 0;
v___x_564_ = lean_box_uint32(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_main___redArg(){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = l_NFO__MemoryLimit_set();
v___x_567_ = ((lean_object*)(l_main___redArg___closed__0));
v___x_568_ = l_Lean_findSysroot(v___x_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_initSearchPath(v_a_569_, v___x_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_572_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_572_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_572_) == 0)
{
uint8_t v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint32_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref_known(v___x_572_, 1);
v___x_573_ = 1;
v___x_574_ = 0;
v___x_575_ = ((lean_object*)(l_main___redArg___closed__61));
v___x_576_ = l_Lean_Options_empty;
v___x_577_ = 0;
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = ((lean_object*)(l_main___redArg___closed__62));
v___x_580_ = 2;
v___x_581_ = lean_box(1);
v___x_582_ = l_Lean_importModules(v___x_575_, v___x_576_, v___x_577_, v___x_579_, v___x_574_, v___x_573_, v___x_580_, v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = ((lean_object*)(l_main___redArg___closed__63));
v___x_585_ = 1;
v___x_586_ = lean_io_prim_handle_mk(v___x_584_, v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = l_Lean_Environment_setExporting(v_a_583_, v___x_574_);
v___x_589_ = l_Lean_Environment_header(v___x_588_);
lean_inc_ref(v___x_589_);
v___x_590_ = l_Lean_EnvironmentHeader_moduleNames(v___x_589_);
v___x_591_ = lean_array_get_size(v___x_590_);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_578_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
v___x_594_ = ((lean_object*)(l_main___redArg___closed__65));
v___x_595_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v___x_589_, v___x_588_, v___x_590_, v_a_587_, v___x_593_, v___x_594_, v___x_578_);
lean_dec_ref_known(v___x_593_, 3);
lean_dec(v_a_587_);
lean_dec_ref(v___x_590_);
lean_dec_ref(v___x_589_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v_snd_597_; lean_object* v_fst_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_658_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v_snd_597_ = lean_ctor_get(v_a_596_, 1);
v_fst_598_ = lean_ctor_get(v_a_596_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_658_ == 0)
{
v___x_600_ = v_a_596_;
v_isShared_601_ = v_isSharedCheck_658_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_597_);
lean_inc(v_fst_598_);
lean_dec(v_a_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_658_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_657_; 
v_fst_602_ = lean_ctor_get(v_snd_597_, 0);
v_snd_603_ = lean_ctor_get(v_snd_597_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_657_ == 0)
{
v___x_605_ = v_snd_597_;
v_isShared_606_ = v_isSharedCheck_657_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_snd_603_);
lean_inc(v_fst_602_);
lean_dec(v_snd_597_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_657_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_607_ = ((lean_object*)(l_main___redArg___closed__66));
v___x_608_ = l_Lean_JsonNumber_fromNat(v___x_591_);
v___x_609_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_609_);
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_609_);
v___x_611_ = v_reuseFailAlloc_656_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_612_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__4));
v___x_613_ = l_Lean_JsonNumber_fromNat(v_fst_602_);
v___x_614_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_614_);
lean_ctor_set(v___x_600_, 0, v___x_612_);
v___x_616_ = v___x_600_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_655_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_617_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg___closed__5));
v___x_618_ = l_Lean_JsonNumber_fromNat(v_snd_603_);
v___x_619_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_617_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = ((lean_object*)(l_main___redArg___closed__67));
lean_inc(v_fst_598_);
v___x_622_ = l_Lean_JsonNumber_fromNat(v_fst_598_);
v___x_623_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = ((lean_object*)(l_main___redArg___closed__72));
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_620_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_616_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_611_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_Json_mkObj(v___x_629_);
lean_dec_ref_known(v___x_629_, 2);
v___x_631_ = l_Lean_Json_compress(v___x_630_);
v___x_632_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_645_; 
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_646_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_645_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_eq(v_fst_598_, v___x_578_);
lean_dec(v_fst_598_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = l_main___redArg___boxed__const__1;
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_main___redArg___boxed__const__2;
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_641_);
v___x_643_ = v___x_634_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_fst_598_);
v_a_647_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_632_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_632_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
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
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_595_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_595_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_583_);
v_a_667_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_586_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_586_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_582_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_582_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_572_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_572_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_571_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_571_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_568_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_568_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_main___redArg();
return v_res_708_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v___args_709_){
_start:
{
lean_object* v___x_711_; 
lean_dec(v___args_709_);
v___x_711_ = l_main___redArg();
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v___args_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = _lean_main(v___args_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_a_718_, lean_object* v_range_719_, lean_object* v_b_720_, lean_object* v_i_721_, lean_object* v_hs_722_, lean_object* v_hl_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___redArg(v___x_715_, v___x_716_, v___x_717_, v_a_718_, v_range_719_, v_b_720_, v_i_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v_a_729_, lean_object* v_range_730_, lean_object* v_b_731_, lean_object* v_i_732_, lean_object* v_hs_733_, lean_object* v_hl_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__3(v___x_726_, v___x_727_, v___x_728_, v_a_729_, v_range_730_, v_b_731_, v_i_732_, v_hs_733_, v_hl_734_);
lean_dec_ref(v_range_730_);
lean_dec(v_a_729_);
lean_dec_ref(v___x_728_);
lean_dec_ref(v___x_726_);
return v_res_736_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFR__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFR__Coherence(uint8_t builtin) {
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
res = initialize_NFR__MemoryLimit(builtin);
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
  res = initialize_NFR__Coherence(1 /* builtin */);
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
