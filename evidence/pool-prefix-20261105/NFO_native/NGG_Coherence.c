// Lean compiler output
// Module: NGG_Coherence
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_NGG__Coherence_referenceNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NGG__Coherence_referenceNames___closed__0 = (const lean_object*)&l_NGG__Coherence_referenceNames___closed__0_value;
LEAN_EXPORT lean_object* l_NGG__Coherence_referenceNames(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declarations"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edges"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dangling"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___redArg___closed__0 = (const lean_object*)&l_main___redArg___closed__0_value;
static const lean_string_object l_main___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFV_PoolReturnData"};
static const lean_object* l_main___redArg___closed__1 = (const lean_object*)&l_main___redArg___closed__1_value;
static const lean_ctor_object l_main___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(213, 190, 254, 127, 158, 3, 109, 55)}};
static const lean_object* l_main___redArg___closed__2 = (const lean_object*)&l_main___redArg___closed__2_value;
static const lean_string_object l_main___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NGG_Count"};
static const lean_object* l_main___redArg___closed__3 = (const lean_object*)&l_main___redArg___closed__3_value;
static const lean_ctor_object l_main___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 233, 182, 34, 249, 101, 118, 192)}};
static const lean_object* l_main___redArg___closed__4 = (const lean_object*)&l_main___redArg___closed__4_value;
static const lean_string_object l_main___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NGG_Loader"};
static const lean_object* l_main___redArg___closed__5 = (const lean_object*)&l_main___redArg___closed__5_value;
static const lean_ctor_object l_main___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 184, 99, 73, 240, 195, 188)}};
static const lean_object* l_main___redArg___closed__6 = (const lean_object*)&l_main___redArg___closed__6_value;
static const lean_string_object l_main___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NGG_Compare"};
static const lean_object* l_main___redArg___closed__7 = (const lean_object*)&l_main___redArg___closed__7_value;
static const lean_ctor_object l_main___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(161, 93, 206, 222, 189, 157, 248, 51)}};
static const lean_object* l_main___redArg___closed__8 = (const lean_object*)&l_main___redArg___closed__8_value;
static const lean_string_object l_main___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NGG_Metadata"};
static const lean_object* l_main___redArg___closed__9 = (const lean_object*)&l_main___redArg___closed__9_value;
static const lean_ctor_object l_main___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(92, 215, 214, 143, 250, 146, 74, 135)}};
static const lean_object* l_main___redArg___closed__10 = (const lean_object*)&l_main___redArg___closed__10_value;
static const lean_string_object l_main___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NGG_Payer"};
static const lean_object* l_main___redArg___closed__11 = (const lean_object*)&l_main___redArg___closed__11_value;
static const lean_ctor_object l_main___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(38, 132, 132, 105, 203, 244, 180, 121)}};
static const lean_object* l_main___redArg___closed__12 = (const lean_object*)&l_main___redArg___closed__12_value;
static const lean_string_object l_main___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NGG_Transport"};
static const lean_object* l_main___redArg___closed__13 = (const lean_object*)&l_main___redArg___closed__13_value;
static const lean_ctor_object l_main___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(4, 25, 146, 54, 115, 36, 170, 11)}};
static const lean_object* l_main___redArg___closed__14 = (const lean_object*)&l_main___redArg___closed__14_value;
static const lean_string_object l_main___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NGG_Scalar"};
static const lean_object* l_main___redArg___closed__15 = (const lean_object*)&l_main___redArg___closed__15_value;
static const lean_ctor_object l_main___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 71, 121, 160, 166, 237, 230, 4)}};
static const lean_object* l_main___redArg___closed__16 = (const lean_object*)&l_main___redArg___closed__16_value;
static const lean_string_object l_main___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NGG_LayoutValue"};
static const lean_object* l_main___redArg___closed__17 = (const lean_object*)&l_main___redArg___closed__17_value;
static const lean_ctor_object l_main___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 78, 131, 43, 206, 224, 181)}};
static const lean_object* l_main___redArg___closed__18 = (const lean_object*)&l_main___redArg___closed__18_value;
static const lean_string_object l_main___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NGG_DecodePrefix"};
static const lean_object* l_main___redArg___closed__19 = (const lean_object*)&l_main___redArg___closed__19_value;
static const lean_ctor_object l_main___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(46, 115, 132, 234, 163, 86, 31, 208)}};
static const lean_object* l_main___redArg___closed__20 = (const lean_object*)&l_main___redArg___closed__20_value;
static const lean_string_object l_main___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NGG_RequestLength"};
static const lean_object* l_main___redArg___closed__21 = (const lean_object*)&l_main___redArg___closed__21_value;
static const lean_ctor_object l_main___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(234, 152, 250, 219, 13, 69, 124, 250)}};
static const lean_object* l_main___redArg___closed__22 = (const lean_object*)&l_main___redArg___closed__22_value;
static const lean_string_object l_main___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NGG_LayoutBounds"};
static const lean_object* l_main___redArg___closed__23 = (const lean_object*)&l_main___redArg___closed__23_value;
static const lean_ctor_object l_main___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(70, 233, 63, 79, 42, 179, 249, 156)}};
static const lean_object* l_main___redArg___closed__24 = (const lean_object*)&l_main___redArg___closed__24_value;
static const lean_string_object l_main___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NGG_PaymentWindows"};
static const lean_object* l_main___redArg___closed__25 = (const lean_object*)&l_main___redArg___closed__25_value;
static const lean_ctor_object l_main___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 204, 86, 55, 60, 53, 53)}};
static const lean_object* l_main___redArg___closed__26 = (const lean_object*)&l_main___redArg___closed__26_value;
static const lean_string_object l_main___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NGG_EnvelopePrefix"};
static const lean_object* l_main___redArg___closed__27 = (const lean_object*)&l_main___redArg___closed__27_value;
static const lean_ctor_object l_main___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__27_value),LEAN_SCALAR_PTR_LITERAL(49, 37, 164, 112, 198, 185, 26, 95)}};
static const lean_object* l_main___redArg___closed__28 = (const lean_object*)&l_main___redArg___closed__28_value;
static const lean_string_object l_main___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NGG_MarkerZero"};
static const lean_object* l_main___redArg___closed__29 = (const lean_object*)&l_main___redArg___closed__29_value;
static const lean_ctor_object l_main___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_object* l_main___redArg___closed__30 = (const lean_object*)&l_main___redArg___closed__30_value;
static const lean_string_object l_main___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NGG_ErrorImage"};
static const lean_object* l_main___redArg___closed__31 = (const lean_object*)&l_main___redArg___closed__31_value;
static const lean_ctor_object l_main___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(203, 39, 227, 93, 116, 70, 12, 8)}};
static const lean_object* l_main___redArg___closed__32 = (const lean_object*)&l_main___redArg___closed__32_value;
static const lean_array_object l_main___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*16, .m_other = 0, .m_tag = 246}, .m_size = 16, .m_capacity = 16, .m_data = {((lean_object*)&l_main___redArg___closed__2_value),((lean_object*)&l_main___redArg___closed__4_value),((lean_object*)&l_main___redArg___closed__6_value),((lean_object*)&l_main___redArg___closed__8_value),((lean_object*)&l_main___redArg___closed__10_value),((lean_object*)&l_main___redArg___closed__12_value),((lean_object*)&l_main___redArg___closed__14_value),((lean_object*)&l_main___redArg___closed__16_value),((lean_object*)&l_main___redArg___closed__18_value),((lean_object*)&l_main___redArg___closed__20_value),((lean_object*)&l_main___redArg___closed__22_value),((lean_object*)&l_main___redArg___closed__24_value),((lean_object*)&l_main___redArg___closed__26_value),((lean_object*)&l_main___redArg___closed__28_value),((lean_object*)&l_main___redArg___closed__30_value),((lean_object*)&l_main___redArg___closed__32_value)}};
static const lean_object* l_main___redArg___closed__33 = (const lean_object*)&l_main___redArg___closed__33_value;
static lean_once_cell_t l_main___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_main___redArg___closed__34;
static lean_once_cell_t l_main___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___redArg___closed__35;
static const lean_array_object l_main___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___redArg___closed__36 = (const lean_object*)&l_main___redArg___closed__36_value;
static const lean_string_object l_main___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NGG_LOADED.jsonl"};
static const lean_object* l_main___redArg___closed__37 = (const lean_object*)&l_main___redArg___closed__37_value;
static const lean_ctor_object l_main___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__38 = (const lean_object*)&l_main___redArg___closed__38_value;
static const lean_ctor_object l_main___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___redArg___closed__38_value)}};
static const lean_object* l_main___redArg___closed__39 = (const lean_object*)&l_main___redArg___closed__39_value;
static const lean_string_object l_main___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modules"};
static const lean_object* l_main___redArg___closed__40 = (const lean_object*)&l_main___redArg___closed__40_value;
static const lean_string_object l_main___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dangling_references"};
static const lean_object* l_main___redArg___closed__41 = (const lean_object*)&l_main___redArg___closed__41_value;
static const lean_string_object l_main___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_main___redArg___closed__42 = (const lean_object*)&l_main___redArg___closed__42_value;
static const lean_string_object l_main___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 123, .m_capacity = 123, .m_length = 122, .m_data = "local NGG/Pool closure; combined headline import FAILED B053; raw import lists and every unresolved reference, none waived"};
static const lean_object* l_main___redArg___closed__43 = (const lean_object*)&l_main___redArg___closed__43_value;
static const lean_ctor_object l_main___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_main___redArg___closed__43_value)}};
static const lean_object* l_main___redArg___closed__44 = (const lean_object*)&l_main___redArg___closed__44_value;
static const lean_ctor_object l_main___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___redArg___closed__42_value),((lean_object*)&l_main___redArg___closed__44_value)}};
static const lean_object* l_main___redArg___closed__45 = (const lean_object*)&l_main___redArg___closed__45_value;
static const lean_ctor_object l_main___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___redArg___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___redArg___closed__46 = (const lean_object*)&l_main___redArg___closed__46_value;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_main___redArg___boxed__const__2;
LEAN_EXPORT lean_object* l_main___redArg();
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg(lean_object* v_as_x27_1_, lean_object* v_b_2_){
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg___boxed(lean_object* v_as_x27_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg(v_as_x27_11_, v_b_12_);
lean_dec(v_as_x27_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_NGG__Coherence_referenceNames(lean_object* v_c_16_){
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
v___x_52_ = ((lean_object*)(l_NGG__Coherence_referenceNames___closed__0));
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
v___x_49_ = l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg(v_rules_46_, v_refs_48_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0(lean_object* v_as_55_, lean_object* v_as_x27_56_, lean_object* v_b_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___redArg(v_as_x27_56_, v_b_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0___boxed(lean_object* v_as_60_, lean_object* v_as_x27_61_, lean_object* v_b_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_forIn_x27_loop___at___00NGG__Coherence_referenceNames_spec__0(v_as_60_, v_as_x27_61_, v_b_62_, v_a_63_);
lean_dec(v_as_x27_61_);
lean_dec(v_as_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_65_, size_t v_i_66_, lean_object* v_bs_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_usize_dec_lt(v_i_66_, v_sz_65_);
if (v___x_68_ == 0)
{
return v_bs_67_;
}
else
{
lean_object* v_v_69_; lean_object* v___x_70_; lean_object* v_bs_x27_71_; uint8_t v___x_72_; lean_object* v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; 
v_v_69_ = lean_array_uget(v_bs_67_, v_i_66_);
v___x_70_ = lean_unsigned_to_nat(0u);
v_bs_x27_71_ = lean_array_uset(v_bs_67_, v_i_66_, v___x_70_);
v___x_72_ = 0;
v___x_73_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_73_, 0, v_v_69_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_68_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1 + 1, v___x_68_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1 + 2, v___x_72_);
v___x_74_ = ((size_t)1ULL);
v___x_75_ = lean_usize_add(v_i_66_, v___x_74_);
v___x_76_ = lean_array_uset(v_bs_x27_71_, v_i_66_, v___x_73_);
v_i_66_ = v___x_75_;
v_bs_67_ = v___x_76_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_78_, lean_object* v_i_79_, lean_object* v_bs_80_){
_start:
{
size_t v_sz_boxed_81_; size_t v_i_boxed_82_; lean_object* v_res_83_; 
v_sz_boxed_81_ = lean_unbox_usize(v_sz_78_);
lean_dec(v_sz_78_);
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_81_, v_i_boxed_82_, v_bs_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3(size_t v_sz_84_, size_t v_i_85_, lean_object* v_bs_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = lean_usize_dec_lt(v_i_85_, v_sz_84_);
if (v___x_87_ == 0)
{
return v_bs_86_;
}
else
{
lean_object* v_v_88_; lean_object* v_module_89_; lean_object* v___x_90_; lean_object* v_bs_x27_91_; lean_object* v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v_v_88_ = lean_array_uget_borrowed(v_bs_86_, v_i_85_);
v_module_89_ = lean_ctor_get(v_v_88_, 0);
lean_inc(v_module_89_);
v___x_90_ = lean_unsigned_to_nat(0u);
v_bs_x27_91_ = lean_array_uset(v_bs_86_, v_i_85_, v___x_90_);
v___x_92_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_89_, v___x_87_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_i_85_, v___x_93_);
v___x_95_ = lean_array_uset(v_bs_x27_91_, v_i_85_, v___x_92_);
v_i_85_ = v___x_94_;
v_bs_86_ = v___x_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3___boxed(lean_object* v_sz_97_, lean_object* v_i_98_, lean_object* v_bs_99_){
_start:
{
size_t v_sz_boxed_100_; size_t v_i_boxed_101_; lean_object* v_res_102_; 
v_sz_boxed_100_ = lean_unbox_usize(v_sz_97_);
lean_dec(v_sz_97_);
v_i_boxed_101_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3(v_sz_boxed_100_, v_i_boxed_101_, v_bs_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v___x_105_, lean_object* v_val_106_, lean_object* v_as_107_, size_t v_sz_108_, size_t v_i_109_, lean_object* v_b_110_){
_start:
{
lean_object* v_a_113_; uint8_t v___x_117_; 
v___x_117_ = lean_usize_dec_lt(v_i_109_, v_sz_108_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v___x_105_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_b_110_);
return v___x_118_;
}
else
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_150_; 
v_fst_119_ = lean_ctor_get(v_b_110_, 0);
v_snd_120_ = lean_ctor_get(v_b_110_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_b_110_);
if (v_isSharedCheck_150_ == 0)
{
v___x_122_ = v_b_110_;
v_isShared_123_ = v_isSharedCheck_150_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_b_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_150_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_checked_124_; lean_object* v___x_125_; lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_checked_124_ = lean_ctor_get(v___x_105_, 2);
v___x_125_ = lean_unsigned_to_nat(1u);
v_a_126_ = lean_array_uget_borrowed(v_as_107_, v_i_109_);
v___x_127_ = lean_nat_add(v_snd_120_, v___x_125_);
lean_dec(v_snd_120_);
lean_inc_ref(v_checked_124_);
v___x_128_ = lean_task_get_own(v_checked_124_);
lean_inc(v_a_126_);
v___x_129_ = lean_environment_find(v___x_128_, v_a_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0));
v___x_131_ = l_Lean_ConstantInfo_name(v_val_106_);
v___x_132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_131_, v___x_117_);
v___x_133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_133_);
lean_ctor_set(v___x_122_, 0, v___x_130_);
v___x_135_ = v___x_122_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_146_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
lean_inc(v_a_126_);
v___x_137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_126_, v___x_117_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_136_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_135_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_Lean_Json_mkObj(v___x_142_);
lean_dec_ref_known(v___x_142_, 2);
v___x_144_ = lean_array_push(v_fst_119_, v___x_143_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_127_);
v_a_113_ = v___x_145_;
goto v___jp_112_;
}
}
else
{
lean_object* v___x_148_; 
lean_dec_ref_known(v___x_129_, 1);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_127_);
v___x_148_ = v___x_122_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_127_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
v_a_113_ = v___x_148_;
goto v___jp_112_;
}
}
}
}
v___jp_112_:
{
size_t v___x_114_; size_t v___x_115_; 
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_add(v_i_109_, v___x_114_);
v_i_109_ = v___x_115_;
v_b_110_ = v_a_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v___x_151_, lean_object* v_val_152_, lean_object* v_as_153_, lean_object* v_sz_154_, lean_object* v_i_155_, lean_object* v_b_156_, lean_object* v___y_157_){
_start:
{
size_t v_sz_boxed_158_; size_t v_i_boxed_159_; lean_object* v_res_160_; 
v_sz_boxed_158_ = lean_unbox_usize(v_sz_154_);
lean_dec(v_sz_154_);
v_i_boxed_159_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_res_160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_151_, v_val_152_, v_as_153_, v_sz_boxed_158_, v_i_boxed_159_, v_b_156_);
lean_dec_ref(v_as_153_);
lean_dec_ref(v_val_152_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object* v___x_161_, lean_object* v_as_162_, size_t v_sz_163_, size_t v_i_164_, lean_object* v_b_165_){
_start:
{
lean_object* v_a_168_; uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_164_, v_sz_163_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec_ref(v___x_161_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_b_165_);
return v___x_173_;
}
else
{
lean_object* v_snd_174_; lean_object* v_fst_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_238_; 
v_snd_174_ = lean_ctor_get(v_b_165_, 1);
v_fst_175_ = lean_ctor_get(v_b_165_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_b_165_);
if (v_isSharedCheck_238_ == 0)
{
v___x_177_ = v_b_165_;
v_isShared_178_ = v_isSharedCheck_238_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_snd_174_);
lean_inc(v_fst_175_);
lean_dec(v_b_165_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_238_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_237_; 
v_fst_179_ = lean_ctor_get(v_snd_174_, 0);
v_snd_180_ = lean_ctor_get(v_snd_174_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_snd_174_);
if (v_isSharedCheck_237_ == 0)
{
v___x_182_ = v_snd_174_;
v_isShared_183_ = v_isSharedCheck_237_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_snd_180_);
lean_inc(v_fst_179_);
lean_dec(v_snd_174_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_237_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_checked_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_checked_184_ = lean_ctor_get(v___x_161_, 2);
v___x_185_ = lean_unsigned_to_nat(1u);
v_a_186_ = lean_array_uget_borrowed(v_as_162_, v_i_164_);
v___x_187_ = lean_nat_add(v_fst_175_, v___x_185_);
lean_dec(v_fst_175_);
lean_inc_ref(v_checked_184_);
v___x_188_ = lean_task_get_own(v_checked_184_);
v___x_189_ = l_Lean_ConstantInfo_name(v_a_186_);
lean_inc(v___x_189_);
v___x_190_ = lean_environment_find(v___x_188_, v___x_189_);
if (lean_obj_tag(v___x_190_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
lean_dec(v___x_189_);
v_val_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc_n(v_val_191_, 2);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = l_NGG__Coherence_referenceNames(v_val_191_);
if (v_isShared_183_ == 0)
{
v___x_194_ = v___x_182_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_fst_179_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_snd_180_);
v___x_194_ = v_reuseFailAlloc_219_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
size_t v_sz_195_; size_t v___x_196_; lean_object* v___x_197_; 
v_sz_195_ = lean_array_size(v___x_192_);
v___x_196_ = ((size_t)0ULL);
lean_inc_ref(v___x_161_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_161_, v_val_191_, v___x_192_, v_sz_195_, v___x_196_, v___x_194_);
lean_dec_ref(v___x_192_);
lean_dec(v_val_191_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v_fst_199_; lean_object* v_snd_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_210_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_197_, 1);
v_fst_199_ = lean_ctor_get(v_a_198_, 0);
v_snd_200_ = lean_ctor_get(v_a_198_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_202_ = v_a_198_;
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_snd_200_);
lean_inc(v_fst_199_);
lean_dec(v_a_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_210_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_fst_199_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_snd_200_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_205_);
lean_ctor_set(v___x_177_, 0, v___x_187_);
v___x_207_ = v___x_177_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v_a_168_ = v___x_207_;
goto v___jp_167_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v___x_187_);
lean_del_object(v___x_177_);
lean_dec_ref(v___x_161_);
v_a_211_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_197_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_197_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec(v___x_190_);
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0));
v___x_221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_189_, v___x_172_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_inc_ref(v___x_222_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___x_222_);
lean_ctor_set(v___x_182_, 0, v___x_220_);
v___x_224_ = v___x_182_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_236_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1));
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_222_);
lean_ctor_set(v___x_177_, 0, v___x_225_);
v___x_227_ = v___x_177_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_222_);
v___x_227_ = v_reuseFailAlloc_235_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_224_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Json_mkObj(v___x_230_);
lean_dec_ref_known(v___x_230_, 2);
v___x_232_ = lean_array_push(v_fst_179_, v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_snd_180_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_187_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v_a_168_ = v___x_234_;
goto v___jp_167_;
}
}
}
}
}
}
v___jp_167_:
{
size_t v___x_169_; size_t v___x_170_; 
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_164_, v___x_169_);
v_i_164_ = v___x_170_;
v_b_165_ = v_a_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object* v___x_239_, lean_object* v_as_240_, lean_object* v_sz_241_, lean_object* v_i_242_, lean_object* v_b_243_, lean_object* v___y_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_241_);
lean_dec(v_sz_241_);
v_i_boxed_246_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___x_239_, v_as_240_, v_sz_boxed_245_, v_i_boxed_246_, v_b_243_);
lean_dec_ref(v_as_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(lean_object* v___x_259_, lean_object* v___x_260_, lean_object* v___x_261_, lean_object* v_a_262_, lean_object* v_range_263_, lean_object* v_b_264_, lean_object* v_i_265_){
_start:
{
lean_object* v_stop_267_; lean_object* v_step_268_; uint8_t v___x_269_; 
v_stop_267_ = lean_ctor_get(v_range_263_, 1);
v_step_268_ = lean_ctor_get(v_range_263_, 2);
v___x_269_ = lean_nat_dec_lt(v_i_265_, v_stop_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v_i_265_);
lean_dec_ref(v___x_261_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_b_264_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_array_get_borrowed(v___x_271_, v___x_259_, v_i_265_);
lean_inc(v___x_272_);
v___x_273_ = l_Lean_findOLean(v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_snd_274_; lean_object* v_a_275_; lean_object* v_fst_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_374_; 
v_snd_274_ = lean_ctor_get(v_b_264_, 1);
lean_inc(v_snd_274_);
v_a_275_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_273_, 1);
v_fst_276_ = lean_ctor_get(v_b_264_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_b_264_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_b_264_, 1);
lean_dec(v_unused_375_);
v___x_278_ = v_b_264_;
v_isShared_279_ = v_isSharedCheck_374_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_fst_276_);
lean_dec(v_b_264_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_374_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_373_; 
v_fst_280_ = lean_ctor_get(v_snd_274_, 0);
v_snd_281_ = lean_ctor_get(v_snd_274_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_snd_274_);
if (v_isSharedCheck_373_ == 0)
{
v___x_283_ = v_snd_274_;
v_isShared_284_ = v_isSharedCheck_373_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_snd_281_);
lean_inc(v_fst_280_);
lean_dec(v_snd_274_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_373_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_moduleData_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_imports_288_; lean_object* v_constants_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v_moduleData_285_ = lean_ctor_get(v___x_260_, 6);
v___x_286_ = l_Lean_instInhabitedModuleData_default;
v___x_287_ = lean_array_get_borrowed(v___x_286_, v_moduleData_285_, v_i_265_);
v_imports_288_ = lean_ctor_get(v___x_287_, 0);
v_constants_289_ = lean_ctor_get(v___x_287_, 2);
v___x_290_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__1));
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_290_);
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_280_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_290_);
v___x_292_ = v_reuseFailAlloc_372_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
size_t v_sz_293_; size_t v___x_294_; lean_object* v___x_295_; 
v_sz_293_ = lean_array_size(v_constants_289_);
v___x_294_ = ((size_t)0ULL);
lean_inc_ref(v___x_261_);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___x_261_, v_constants_289_, v_sz_293_, v___x_294_, v___x_292_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_snd_297_; lean_object* v_fst_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_363_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v_snd_297_ = lean_ctor_get(v_a_296_, 1);
v_fst_298_ = lean_ctor_get(v_a_296_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_363_ == 0)
{
v___x_300_ = v_a_296_;
v_isShared_301_ = v_isSharedCheck_363_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_297_);
lean_inc(v_fst_298_);
lean_dec(v_a_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_363_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_362_; 
v_fst_302_ = lean_ctor_get(v_snd_297_, 0);
v_snd_303_ = lean_ctor_get(v_snd_297_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_snd_297_);
if (v_isSharedCheck_362_ == 0)
{
v___x_305_ = v_snd_297_;
v_isShared_306_ = v_isSharedCheck_362_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_snd_303_);
lean_inc(v_fst_302_);
lean_dec(v_snd_297_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_362_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_307_ = lean_nat_add(v_snd_281_, v_snd_303_);
lean_dec(v_snd_281_);
v___x_308_ = lean_array_get_size(v_fst_302_);
v___x_309_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__2));
lean_inc(v___x_272_);
v___x_310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_272_, v___x_269_);
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_311_);
lean_ctor_set(v___x_305_, 0, v___x_309_);
v___x_313_ = v___x_305_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_361_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__3));
v___x_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_315_, 0, v_a_275_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_315_);
lean_ctor_set(v___x_300_, 0, v___x_314_);
v___x_317_ = v___x_300_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_360_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; size_t v_sz_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_318_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__4));
v_sz_319_ = lean_array_size(v_imports_288_);
lean_inc_ref(v_imports_288_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__3(v_sz_319_, v___x_294_, v_imports_288_);
v___x_321_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_320_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_321_);
lean_ctor_set(v___x_278_, 0, v___x_318_);
v___x_323_ = v___x_278_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_359_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_324_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__5));
v___x_325_ = lean_array_get_size(v_constants_289_);
v___x_326_ = l_Lean_JsonNumber_fromNat(v___x_325_);
v___x_327_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__6));
v___x_330_ = l_Lean_JsonNumber_fromNat(v_snd_303_);
v___x_331_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__7));
v___x_334_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_302_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_332_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_328_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_323_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_317_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_313_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = l_Lean_Json_mkObj(v___x_342_);
lean_dec_ref_known(v___x_342_, 2);
v___x_344_ = l_Lean_Json_compress(v___x_343_);
v___x_345_ = l_IO_FS_Handle_putStrLn(v_a_262_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref_known(v___x_345_, 1);
v___x_346_ = lean_nat_add(v_fst_276_, v___x_308_);
lean_dec(v_fst_276_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_fst_298_);
lean_ctor_set(v___x_347_, 1, v___x_307_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_nat_add(v_i_265_, v_step_268_);
lean_dec(v_i_265_);
v_b_264_ = v___x_348_;
v_i_265_ = v___x_349_;
goto _start;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v___x_307_);
lean_dec(v_fst_298_);
lean_dec(v_fst_276_);
lean_dec(v_i_265_);
lean_dec_ref(v___x_261_);
v_a_351_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_345_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
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
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_snd_281_);
lean_del_object(v___x_278_);
lean_dec(v_fst_276_);
lean_dec(v_a_275_);
lean_dec(v_i_265_);
lean_dec_ref(v___x_261_);
v_a_364_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_295_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_295_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_i_265_);
lean_dec_ref(v_b_264_);
lean_dec_ref(v___x_261_);
v_a_376_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_273_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_273_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___boxed(lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_range_388_, lean_object* v_b_389_, lean_object* v_i_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v___x_384_, v___x_385_, v___x_386_, v_a_387_, v_range_388_, v_b_389_, v_i_390_);
lean_dec_ref(v_range_388_);
lean_dec(v_a_387_);
lean_dec_ref(v___x_385_);
lean_dec_ref(v___x_384_);
return v_res_392_;
}
}
static size_t _init_l_main___redArg___closed__34(void){
_start:
{
lean_object* v___x_476_; size_t v_sz_477_; 
v___x_476_ = ((lean_object*)(l_main___redArg___closed__33));
v_sz_477_ = lean_array_size(v___x_476_);
return v_sz_477_;
}
}
static lean_object* _init_l_main___redArg___closed__35(void){
_start:
{
lean_object* v___x_478_; size_t v___x_479_; size_t v_sz_480_; lean_object* v___x_481_; 
v___x_478_ = ((lean_object*)(l_main___redArg___closed__33));
v___x_479_ = ((size_t)0ULL);
v_sz_480_ = lean_usize_once(&l_main___redArg___closed__34, &l_main___redArg___closed__34_once, _init_l_main___redArg___closed__34);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_480_, v___x_479_, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_main___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_502_; lean_object* v___x_503_; 
v___x_502_ = 1;
v___x_503_ = lean_box_uint32(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_main___redArg___boxed__const__2(void){
_start:
{
uint32_t v___x_504_; lean_object* v___x_505_; 
v___x_504_ = 0;
v___x_505_ = lean_box_uint32(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_main___redArg(){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = l_NFO__MemoryLimit_set();
v___x_508_ = ((lean_object*)(l_main___redArg___closed__0));
v___x_509_ = l_Lean_findSysroot(v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = lean_box(0);
v___x_512_ = l_Lean_initSearchPath(v_a_510_, v___x_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; 
lean_dec_ref_known(v___x_512_, 1);
v___x_513_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; uint32_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; uint8_t v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = lean_obj_once(&l_main___redArg___closed__35, &l_main___redArg___closed__35_once, _init_l_main___redArg___closed__35);
v___x_515_ = l_Lean_Options_empty;
v___x_516_ = 0;
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = ((lean_object*)(l_main___redArg___closed__36));
v___x_519_ = 0;
v___x_520_ = 1;
v___x_521_ = 2;
v___x_522_ = lean_box(1);
v___x_523_ = l_Lean_importModules(v___x_514_, v___x_515_, v___x_516_, v___x_518_, v___x_519_, v___x_520_, v___x_521_, v___x_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = ((lean_object*)(l_main___redArg___closed__37));
v___x_526_ = 1;
v___x_527_ = lean_io_prim_handle_mk(v___x_525_, v___x_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Lean_Environment_setExporting(v_a_524_, v___x_519_);
v___x_530_ = l_Lean_Environment_header(v___x_529_);
lean_inc_ref(v___x_530_);
v___x_531_ = l_Lean_EnvironmentHeader_moduleNames(v___x_530_);
v___x_532_ = lean_array_get_size(v___x_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v___x_517_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
v___x_535_ = ((lean_object*)(l_main___redArg___closed__39));
v___x_536_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v___x_531_, v___x_530_, v___x_529_, v_a_528_, v___x_534_, v___x_535_, v___x_517_);
lean_dec_ref_known(v___x_534_, 3);
lean_dec(v_a_528_);
lean_dec_ref(v___x_530_);
lean_dec_ref(v___x_531_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v_snd_538_; lean_object* v_fst_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_599_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v_snd_538_ = lean_ctor_get(v_a_537_, 1);
v_fst_539_ = lean_ctor_get(v_a_537_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_a_537_);
if (v_isSharedCheck_599_ == 0)
{
v___x_541_ = v_a_537_;
v_isShared_542_ = v_isSharedCheck_599_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_538_);
lean_inc(v_fst_539_);
lean_dec(v_a_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_599_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_598_; 
v_fst_543_ = lean_ctor_get(v_snd_538_, 0);
v_snd_544_ = lean_ctor_get(v_snd_538_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_snd_538_);
if (v_isSharedCheck_598_ == 0)
{
v___x_546_ = v_snd_538_;
v_isShared_547_ = v_isSharedCheck_598_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_543_);
lean_dec(v_snd_538_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_598_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_548_ = ((lean_object*)(l_main___redArg___closed__40));
v___x_549_ = l_Lean_JsonNumber_fromNat(v___x_532_);
v___x_550_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_550_);
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_597_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_553_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__5));
v___x_554_ = l_Lean_JsonNumber_fromNat(v_fst_543_);
v___x_555_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_555_);
lean_ctor_set(v___x_541_, 0, v___x_553_);
v___x_557_ = v___x_541_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_596_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_558_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg___closed__6));
v___x_559_ = l_Lean_JsonNumber_fromNat(v_snd_544_);
v___x_560_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_558_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = ((lean_object*)(l_main___redArg___closed__41));
lean_inc(v_fst_539_);
v___x_563_ = l_Lean_JsonNumber_fromNat(v_fst_539_);
v___x_564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_562_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l_main___redArg___closed__46));
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_561_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_557_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_552_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_Json_mkObj(v___x_570_);
lean_dec_ref_known(v___x_570_, 2);
v___x_572_ = l_Lean_Json_compress(v___x_571_);
v___x_573_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_586_; 
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_587_);
v___x_575_ = v___x_573_;
v_isShared_576_ = v_isSharedCheck_586_;
goto v_resetjp_574_;
}
else
{
lean_dec(v___x_573_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_586_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
uint8_t v___x_577_; 
v___x_577_ = lean_nat_dec_eq(v_fst_539_, v___x_517_);
lean_dec(v_fst_539_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = l_main___redArg___boxed__const__1;
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = l_main___redArg___boxed__const__2;
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_582_);
v___x_584_ = v___x_575_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_fst_539_);
v_a_588_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_573_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_573_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
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
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_536_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_536_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_524_);
v_a_608_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_527_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_527_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_523_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_523_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_a_624_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_513_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_513_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_512_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_512_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_509_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_509_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___redArg___boxed(lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_main___redArg();
return v_res_649_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v___args_650_){
_start:
{
lean_object* v___x_652_; 
lean_dec(v___args_650_);
v___x_652_ = l_main___redArg();
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v___args_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = _lean_main(v___args_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4(lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v_a_659_, lean_object* v_range_660_, lean_object* v_b_661_, lean_object* v_i_662_, lean_object* v_hs_663_, lean_object* v_hl_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___redArg(v___x_656_, v___x_657_, v___x_658_, v_a_659_, v_range_660_, v_b_661_, v_i_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4___boxed(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v_a_670_, lean_object* v_range_671_, lean_object* v_b_672_, lean_object* v_i_673_, lean_object* v_hs_674_, lean_object* v_hl_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00main_spec__4(v___x_667_, v___x_668_, v___x_669_, v_a_670_, v_range_671_, v_b_672_, v_i_673_, v_hs_674_, v_hl_675_);
lean_dec_ref(v_range_671_);
lean_dec(v_a_670_);
lean_dec_ref(v___x_668_);
lean_dec_ref(v___x_667_);
return v_res_677_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFR__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NGG__Coherence(uint8_t builtin) {
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
  res = initialize_NGG__Coherence(1 /* builtin */);
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
