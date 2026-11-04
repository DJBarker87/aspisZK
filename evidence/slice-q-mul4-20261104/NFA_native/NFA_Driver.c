// Lean compiler output
// Module: NFA_Driver
// Imports: public import Init public meta import Init public import Lean public import NFA_MemoryLimit public import NFA_WALKER
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_NEP_audit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_NFA__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "printAxioms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 183, 89, 85, 6, 216, 148, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "#print"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "axioms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "NEP_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_array_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEP_Driver"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static lean_once_cell_t l_main___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__5;
static lean_once_cell_t l_main___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__6;
static lean_once_cell_t l_main___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__7;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Unknown NFA audit mode"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "4"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "5"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "6"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "7"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "8"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "9"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "10"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "11"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "12"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "13"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "14"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "15"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "16"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "17"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "18"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "19"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "20"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "21"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "22"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "23"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "24"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "25"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "26"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "27"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_string_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "28"};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "29"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_string_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "30"};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "31"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_string_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "32"};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "33"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_string_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "34"};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "35"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_string_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "36"};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "37"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "38"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_string_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "39"};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "40"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_string_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "41"};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "42"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_string_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "43"};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_string_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "44"};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "45"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_string_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "46"};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "47"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_string_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "48"};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_string_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "49"};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "50"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "51"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_string_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "52"};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "53"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "54"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "55"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_string_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "56"};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_string_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "57"};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_array_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_string_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotResult"};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_ctor_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_array_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__69_value)}};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_string_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "result_state_effects"};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_ctor_object l_main___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__72_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(255, 171, 112, 111, 120, 231, 138, 95)}};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_array_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__72_value)}};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_string_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_ctor_object l_main___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__75_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(195, 240, 240, 108, 178, 127, 156, 191)}};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_array_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__75_value)}};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_string_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "inner"};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_ctor_object l_main___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__78_value_aux_0),((lean_object*)&l_main___closed__77_value),LEAN_SCALAR_PTR_LITERAL(161, 170, 171, 99, 193, 166, 197, 59)}};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_array_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__78_value)}};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_string_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NEV_FourResult"};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_ctor_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_array_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__81_value)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_ctor_object l_main___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__83_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(151, 203, 215, 138, 71, 20, 48, 159)}};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_ctor_object l_main___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(123, 104, 208, 19, 220, 163, 239, 112)}};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_string_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "calls"};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_ctor_object l_main___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__86_value_aux_0),((lean_object*)&l_main___closed__85_value),LEAN_SCALAR_PTR_LITERAL(193, 207, 189, 100, 203, 16, 185, 164)}};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_array_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__83_value),((lean_object*)&l_main___closed__84_value),((lean_object*)&l_main___closed__86_value)}};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_string_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_DotSchedule"};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_ctor_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_array_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__89_value)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_ctor_object l_main___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(240, 211, 148, 244, 207, 192, 41, 128)}};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_string_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reached"};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_ctor_object l_main___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__94_value_aux_0),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(70, 94, 174, 195, 203, 213, 144, 3)}};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_string_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unique_block"};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_ctor_object l_main___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__96_value_aux_0),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(86, 132, 221, 90, 64, 246, 63, 124)}};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_string_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "remaining"};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_ctor_object l_main___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__98_value_aux_0),((lean_object*)&l_main___closed__97_value),LEAN_SCALAR_PTR_LITERAL(170, 9, 154, 167, 238, 10, 71, 17)}};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_string_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "adjacent"};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_ctor_object l_main___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_0),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(229, 63, 141, 233, 164, 171, 60, 134)}};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_string_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "advance_mathematics"};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_ctor_object l_main___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__102_value_aux_0),((lean_object*)&l_main___closed__101_value),LEAN_SCALAR_PTR_LITERAL(148, 241, 222, 46, 68, 213, 221, 236)}};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_string_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "finished"};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_ctor_object l_main___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__104_value_aux_0),((lean_object*)&l_main___closed__103_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 29, 113, 210, 204, 137, 166)}};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_array_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__92_value),((lean_object*)&l_main___closed__94_value),((lean_object*)&l_main___closed__96_value),((lean_object*)&l_main___closed__98_value),((lean_object*)&l_main___closed__100_value),((lean_object*)&l_main___closed__102_value),((lean_object*)&l_main___closed__104_value)}};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_string_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_DotEightTotal"};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_ctor_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_array_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__107_value)}};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_string_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "eight"};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_ctor_object l_main___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__110_value_aux_0),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(90, 236, 255, 136, 0, 51, 66, 247)}};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_string_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_ctor_object l_main___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__112_value_aux_0),((lean_object*)&l_main___closed__111_value),LEAN_SCALAR_PTR_LITERAL(143, 85, 213, 68, 34, 10, 56, 130)}};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_string_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_ctor_object l_main___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__114_value_aux_0),((lean_object*)&l_main___closed__113_value),LEAN_SCALAR_PTR_LITERAL(230, 53, 58, 48, 123, 160, 9, 205)}};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_array_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__110_value),((lean_object*)&l_main___closed__112_value),((lean_object*)&l_main___closed__114_value)}};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_string_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotInputs"};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_ctor_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__116_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_array_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__117_value)}};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_string_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "selected"};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_ctor_object l_main___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__116_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__120_value_aux_0),((lean_object*)&l_main___closed__119_value),LEAN_SCALAR_PTR_LITERAL(106, 252, 122, 59, 66, 92, 86, 52)}};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_string_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "limbs"};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_ctor_object l_main___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__116_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__122_value_aux_0),((lean_object*)&l_main___closed__121_value),LEAN_SCALAR_PTR_LITERAL(237, 127, 116, 172, 196, 61, 112, 98)}};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_string_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tail_index"};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_ctor_object l_main___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__116_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__124_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(248, 177, 197, 79, 199, 100, 61, 119)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_array_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__120_value),((lean_object*)&l_main___closed__122_value),((lean_object*)&l_main___closed__124_value)}};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_string_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_DotReadDomain"};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_ctor_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_array_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__127_value)}};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_string_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_ctor_object l_main___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_ctor_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_0),((lean_object*)&l_main___closed__129_value),LEAN_SCALAR_PTR_LITERAL(29, 4, 124, 132, 240, 221, 12, 207)}};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_ctor_object l_main___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_ctor_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__131_value_aux_0),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(144, 12, 99, 54, 96, 127, 86, 153)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_array_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__130_value),((lean_object*)&l_main___closed__131_value)}};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_string_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_DotSweepStep"};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_ctor_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_array_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__134_value)}};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_string_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_ctor_object l_main___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_ctor_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_0),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(174, 234, 216, 181, 233, 82, 134, 235)}};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_string_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "next_term"};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_ctor_object l_main___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_ctor_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__139_value_aux_0),((lean_object*)&l_main___closed__138_value),LEAN_SCALAR_PTR_LITERAL(21, 163, 171, 29, 11, 228, 207, 27)}};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_array_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__137_value),((lean_object*)&l_main___closed__139_value)}};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_string_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_DotSweep"};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_ctor_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_array_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__142_value)}};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_string_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "write"};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_ctor_object l_main___closed__145_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__145_value_aux_0),((lean_object*)&l_main___closed__144_value),LEAN_SCALAR_PTR_LITERAL(193, 3, 185, 49, 2, 13, 7, 119)}};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_string_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "current"};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_ctor_object l_main___closed__147_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__147_value_aux_0),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(209, 91, 27, 114, 109, 124, 152, 109)}};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_string_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "native_domain"};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_ctor_object l_main___closed__149_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__149_value_aux_0),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(174, 135, 218, 80, 92, 132, 48, 146)}};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_array_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__145_value),((lean_object*)&l_main___closed__147_value),((lean_object*)&l_main___closed__149_value)}};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_string_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_DotEight"};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_ctor_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(34, 249, 36, 212, 240, 45, 165, 138)}};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_array_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__152_value)}};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_ctor_object l_main___closed__154_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(34, 249, 36, 212, 240, 45, 165, 138)}};
static const lean_ctor_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__154_value_aux_0),((lean_object*)&l_main___closed__113_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 242, 139, 40, 197, 114, 85)}};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_array_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__154_value)}};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_string_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_DotCell"};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_ctor_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__156_value),LEAN_SCALAR_PTR_LITERAL(198, 50, 110, 209, 126, 234, 105, 249)}};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_array_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__157_value)}};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_string_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "total"};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_ctor_object l_main___closed__160_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__156_value),LEAN_SCALAR_PTR_LITERAL(198, 50, 110, 209, 126, 234, 105, 249)}};
static const lean_ctor_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__160_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(248, 233, 237, 73, 250, 64, 147, 227)}};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_array_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__160_value)}};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_string_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_ActualDotStep"};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_ctor_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__162_value),LEAN_SCALAR_PTR_LITERAL(78, 134, 44, 53, 228, 48, 171, 153)}};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_array_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__163_value)}};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_string_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_string_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_ctor_object l_main___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__167_value_aux_0),((lean_object*)&l_main___closed__162_value),LEAN_SCALAR_PTR_LITERAL(115, 165, 125, 248, 87, 69, 218, 154)}};
static const lean_ctor_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__167_value_aux_1),((lean_object*)&l_main___closed__166_value),LEAN_SCALAR_PTR_LITERAL(134, 18, 18, 238, 31, 172, 208, 61)}};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_array_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__167_value)}};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_string_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_DotFoldInvariant"};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_ctor_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_array_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__170_value)}};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_ctor_object l_main___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_ctor_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__172_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(167, 235, 53, 90, 114, 46, 26, 133)}};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_ctor_object l_main___closed__173_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_ctor_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__173_value_aux_0),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(60, 124, 136, 250, 102, 13, 219, 200)}};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_array_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__172_value),((lean_object*)&l_main___closed__173_value)}};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_array_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__78_value),((lean_object*)&l_main___closed__75_value),((lean_object*)&l_main___closed__72_value)}};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_string_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotScalar"};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_ctor_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__176_value),LEAN_SCALAR_PTR_LITERAL(49, 33, 255, 251, 16, 115, 6, 25)}};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_array_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__177_value)}};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_string_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "product"};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_ctor_object l_main___closed__180_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__176_value),LEAN_SCALAR_PTR_LITERAL(49, 33, 255, 251, 16, 115, 6, 25)}};
static const lean_ctor_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__180_value_aux_0),((lean_object*)&l_main___closed__179_value),LEAN_SCALAR_PTR_LITERAL(239, 160, 141, 159, 250, 145, 86, 23)}};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_array_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__180_value)}};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_string_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_EbyPushAssociation"};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_ctor_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__182_value),LEAN_SCALAR_PTR_LITERAL(30, 121, 204, 152, 27, 46, 80, 75)}};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_array_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__183_value)}};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_ctor_object l_main___closed__185_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__182_value),LEAN_SCALAR_PTR_LITERAL(30, 121, 204, 152, 27, 46, 80, 75)}};
static const lean_ctor_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__185_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(204, 94, 158, 106, 141, 162, 238, 119)}};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_array_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__185_value)}};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_string_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_DotPush"};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_ctor_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__187_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_array_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__188_value)}};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_string_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "association"};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_ctor_object l_main___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__187_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_ctor_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__191_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(193, 86, 50, 168, 85, 47, 249, 190)}};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_string_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_ctor_object l_main___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__187_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_ctor_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_0),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(87, 15, 102, 122, 72, 12, 223, 26)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_array_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__191_value),((lean_object*)&l_main___closed__193_value)}};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_string_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_QRawAssociation"};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_ctor_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__195_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_array_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__196_value)}};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_string_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "actual"};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_ctor_object l_main___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__195_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_ctor_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__199_value_aux_0),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(179, 5, 253, 32, 231, 1, 89, 102)}};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_string_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cohort"};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_ctor_object l_main___closed__201_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__195_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_ctor_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__201_value_aux_0),((lean_object*)&l_main___closed__200_value),LEAN_SCALAR_PTR_LITERAL(240, 34, 160, 133, 250, 56, 210, 57)}};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_array_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__199_value),((lean_object*)&l_main___closed__201_value)}};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_string_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_QRawAtoms"};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_ctor_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_array_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__204_value)}};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
static const lean_string_object l_main___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modulus"};
static const lean_object* l_main___closed__206 = (const lean_object*)&l_main___closed__206_value;
static const lean_ctor_object l_main___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__207_value_aux_0),((lean_object*)&l_main___closed__206_value),LEAN_SCALAR_PTR_LITERAL(174, 16, 221, 13, 146, 231, 77, 42)}};
static const lean_object* l_main___closed__207 = (const lean_object*)&l_main___closed__207_value;
static const lean_string_object l_main___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_main___closed__208 = (const lean_object*)&l_main___closed__208_value;
static const lean_ctor_object l_main___closed__209_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__209_value_aux_0),((lean_object*)&l_main___closed__208_value),LEAN_SCALAR_PTR_LITERAL(95, 65, 42, 159, 4, 54, 90, 46)}};
static const lean_object* l_main___closed__209 = (const lean_object*)&l_main___closed__209_value;
static const lean_string_object l_main___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read0"};
static const lean_object* l_main___closed__210 = (const lean_object*)&l_main___closed__210_value;
static const lean_ctor_object l_main___closed__211_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__211_value_aux_0),((lean_object*)&l_main___closed__210_value),LEAN_SCALAR_PTR_LITERAL(150, 4, 241, 117, 134, 207, 214, 102)}};
static const lean_object* l_main___closed__211 = (const lean_object*)&l_main___closed__211_value;
static const lean_string_object l_main___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read1"};
static const lean_object* l_main___closed__212 = (const lean_object*)&l_main___closed__212_value;
static const lean_ctor_object l_main___closed__213_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__213_value_aux_0),((lean_object*)&l_main___closed__212_value),LEAN_SCALAR_PTR_LITERAL(197, 204, 220, 97, 122, 205, 145, 204)}};
static const lean_object* l_main___closed__213 = (const lean_object*)&l_main___closed__213_value;
static const lean_string_object l_main___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read2"};
static const lean_object* l_main___closed__214 = (const lean_object*)&l_main___closed__214_value;
static const lean_ctor_object l_main___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__215_value_aux_0),((lean_object*)&l_main___closed__214_value),LEAN_SCALAR_PTR_LITERAL(253, 73, 17, 189, 160, 146, 133, 106)}};
static const lean_object* l_main___closed__215 = (const lean_object*)&l_main___closed__215_value;
static const lean_string_object l_main___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read3"};
static const lean_object* l_main___closed__216 = (const lean_object*)&l_main___closed__216_value;
static const lean_ctor_object l_main___closed__217_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__217_value_aux_0),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(249, 74, 221, 181, 143, 183, 149, 18)}};
static const lean_object* l_main___closed__217 = (const lean_object*)&l_main___closed__217_value;
static const lean_array_object l_main___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_main___closed__207_value),((lean_object*)&l_main___closed__209_value),((lean_object*)&l_main___closed__211_value),((lean_object*)&l_main___closed__213_value),((lean_object*)&l_main___closed__215_value),((lean_object*)&l_main___closed__217_value)}};
static const lean_object* l_main___closed__218 = (const lean_object*)&l_main___closed__218_value;
static const lean_string_object l_main___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_QRawMaps"};
static const lean_object* l_main___closed__219 = (const lean_object*)&l_main___closed__219_value;
static const lean_ctor_object l_main___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_object* l_main___closed__220 = (const lean_object*)&l_main___closed__220_value;
static const lean_array_object l_main___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__220_value)}};
static const lean_object* l_main___closed__221 = (const lean_object*)&l_main___closed__221_value;
static const lean_string_object l_main___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_main___closed__222 = (const lean_object*)&l_main___closed__222_value;
static const lean_ctor_object l_main___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__223_value_aux_0),((lean_object*)&l_main___closed__222_value),LEAN_SCALAR_PTR_LITERAL(28, 131, 142, 180, 105, 66, 202, 67)}};
static const lean_object* l_main___closed__223 = (const lean_object*)&l_main___closed__223_value;
static const lean_string_object l_main___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_main___closed__224 = (const lean_object*)&l_main___closed__224_value;
static const lean_ctor_object l_main___closed__225_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__225_value_aux_0),((lean_object*)&l_main___closed__224_value),LEAN_SCALAR_PTR_LITERAL(194, 7, 196, 18, 12, 252, 237, 93)}};
static const lean_object* l_main___closed__225 = (const lean_object*)&l_main___closed__225_value;
static const lean_string_object l_main___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shift"};
static const lean_object* l_main___closed__226 = (const lean_object*)&l_main___closed__226_value;
static const lean_ctor_object l_main___closed__227_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__227_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(121, 104, 117, 205, 249, 145, 35, 21)}};
static const lean_object* l_main___closed__227 = (const lean_object*)&l_main___closed__227_value;
static const lean_string_object l_main___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fold"};
static const lean_object* l_main___closed__228 = (const lean_object*)&l_main___closed__228_value;
static const lean_ctor_object l_main___closed__229_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__229_value_aux_0),((lean_object*)&l_main___closed__228_value),LEAN_SCALAR_PTR_LITERAL(230, 77, 241, 242, 133, 228, 96, 129)}};
static const lean_object* l_main___closed__229 = (const lean_object*)&l_main___closed__229_value;
static const lean_array_object l_main___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__223_value),((lean_object*)&l_main___closed__225_value),((lean_object*)&l_main___closed__227_value),((lean_object*)&l_main___closed__229_value)}};
static const lean_object* l_main___closed__230 = (const lean_object*)&l_main___closed__230_value;
static const lean_string_object l_main___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_ReachedProgress"};
static const lean_object* l_main___closed__231 = (const lean_object*)&l_main___closed__231_value;
static const lean_ctor_object l_main___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__231_value),LEAN_SCALAR_PTR_LITERAL(11, 92, 122, 162, 60, 194, 185, 166)}};
static const lean_object* l_main___closed__232 = (const lean_object*)&l_main___closed__232_value;
static const lean_array_object l_main___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__232_value)}};
static const lean_object* l_main___closed__233 = (const lean_object*)&l_main___closed__233_value;
static const lean_string_object l_main___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_main___closed__234 = (const lean_object*)&l_main___closed__234_value;
static const lean_ctor_object l_main___closed__235_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__231_value),LEAN_SCALAR_PTR_LITERAL(11, 92, 122, 162, 60, 194, 185, 166)}};
static const lean_ctor_object l_main___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__235_value_aux_0),((lean_object*)&l_main___closed__234_value),LEAN_SCALAR_PTR_LITERAL(17, 77, 46, 99, 160, 246, 61, 74)}};
static const lean_object* l_main___closed__235 = (const lean_object*)&l_main___closed__235_value;
static const lean_array_object l_main___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__235_value)}};
static const lean_object* l_main___closed__236 = (const lean_object*)&l_main___closed__236_value;
static const lean_string_object l_main___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_AccumPacket"};
static const lean_object* l_main___closed__237 = (const lean_object*)&l_main___closed__237_value;
static const lean_ctor_object l_main___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_object* l_main___closed__238 = (const lean_object*)&l_main___closed__238_value;
static const lean_array_object l_main___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__238_value)}};
static const lean_object* l_main___closed__239 = (const lean_object*)&l_main___closed__239_value;
static const lean_string_object l_main___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "raw_length"};
static const lean_object* l_main___closed__240 = (const lean_object*)&l_main___closed__240_value;
static const lean_ctor_object l_main___closed__241_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__241_value_aux_0),((lean_object*)&l_main___closed__240_value),LEAN_SCALAR_PTR_LITERAL(133, 229, 162, 188, 47, 80, 38, 123)}};
static const lean_object* l_main___closed__241 = (const lean_object*)&l_main___closed__241_value;
static const lean_ctor_object l_main___closed__242_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__242_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(139, 171, 207, 144, 75, 124, 175, 142)}};
static const lean_object* l_main___closed__242 = (const lean_object*)&l_main___closed__242_value;
static const lean_string_object l_main___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "no_base_dependency"};
static const lean_object* l_main___closed__243 = (const lean_object*)&l_main___closed__243_value;
static const lean_ctor_object l_main___closed__244_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_0),((lean_object*)&l_main___closed__243_value),LEAN_SCALAR_PTR_LITERAL(0, 21, 157, 234, 11, 239, 213, 163)}};
static const lean_object* l_main___closed__244 = (const lean_object*)&l_main___closed__244_value;
static const lean_array_object l_main___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__241_value),((lean_object*)&l_main___closed__242_value),((lean_object*)&l_main___closed__244_value)}};
static const lean_object* l_main___closed__245 = (const lean_object*)&l_main___closed__245_value;
static const lean_string_object l_main___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_WeightDomains"};
static const lean_object* l_main___closed__246 = (const lean_object*)&l_main___closed__246_value;
static const lean_ctor_object l_main___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(143, 232, 106, 128, 44, 176, 30, 97)}};
static const lean_object* l_main___closed__247 = (const lean_object*)&l_main___closed__247_value;
static const lean_array_object l_main___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__247_value)}};
static const lean_object* l_main___closed__248 = (const lean_object*)&l_main___closed__248_value;
static const lean_string_object l_main___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "read"};
static const lean_object* l_main___closed__249 = (const lean_object*)&l_main___closed__249_value;
static const lean_ctor_object l_main___closed__250_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(143, 232, 106, 128, 44, 176, 30, 97)}};
static const lean_ctor_object l_main___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__250_value_aux_0),((lean_object*)&l_main___closed__249_value),LEAN_SCALAR_PTR_LITERAL(90, 88, 63, 126, 61, 125, 10, 115)}};
static const lean_object* l_main___closed__250 = (const lean_object*)&l_main___closed__250_value;
static const lean_array_object l_main___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__250_value)}};
static const lean_object* l_main___closed__251 = (const lean_object*)&l_main___closed__251_value;
static const lean_string_object l_main___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_BasisCallDomains"};
static const lean_object* l_main___closed__252 = (const lean_object*)&l_main___closed__252_value;
static const lean_ctor_object l_main___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__252_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_object* l_main___closed__253 = (const lean_object*)&l_main___closed__253_value;
static const lean_array_object l_main___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__253_value)}};
static const lean_object* l_main___closed__254 = (const lean_object*)&l_main___closed__254_value;
static const lean_ctor_object l_main___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__252_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_ctor_object l_main___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__255_value_aux_0),((lean_object*)&l_main___closed__129_value),LEAN_SCALAR_PTR_LITERAL(201, 201, 161, 138, 59, 141, 168, 64)}};
static const lean_object* l_main___closed__255 = (const lean_object*)&l_main___closed__255_value;
static const lean_string_object l_main___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "active_level"};
static const lean_object* l_main___closed__256 = (const lean_object*)&l_main___closed__256_value;
static const lean_ctor_object l_main___closed__257_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__252_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_ctor_object l_main___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__257_value_aux_0),((lean_object*)&l_main___closed__256_value),LEAN_SCALAR_PTR_LITERAL(59, 181, 134, 173, 118, 141, 183, 96)}};
static const lean_object* l_main___closed__257 = (const lean_object*)&l_main___closed__257_value;
static const lean_array_object l_main___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__255_value),((lean_object*)&l_main___closed__257_value)}};
static const lean_object* l_main___closed__258 = (const lean_object*)&l_main___closed__258_value;
static const lean_string_object l_main___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PushDomains"};
static const lean_object* l_main___closed__259 = (const lean_object*)&l_main___closed__259_value;
static const lean_ctor_object l_main___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__259_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_object* l_main___closed__260 = (const lean_object*)&l_main___closed__260_value;
static const lean_array_object l_main___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__260_value)}};
static const lean_object* l_main___closed__261 = (const lean_object*)&l_main___closed__261_value;
static const lean_string_object l_main___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "canonical_limb"};
static const lean_object* l_main___closed__262 = (const lean_object*)&l_main___closed__262_value;
static const lean_ctor_object l_main___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__259_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_ctor_object l_main___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_0),((lean_object*)&l_main___closed__262_value),LEAN_SCALAR_PTR_LITERAL(37, 191, 150, 61, 199, 52, 62, 68)}};
static const lean_object* l_main___closed__263 = (const lean_object*)&l_main___closed__263_value;
static const lean_ctor_object l_main___closed__264_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__259_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_ctor_object l_main___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__264_value_aux_0),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(224, 48, 54, 211, 193, 177, 145, 147)}};
static const lean_object* l_main___closed__264 = (const lean_object*)&l_main___closed__264_value;
static const lean_array_object l_main___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__263_value),((lean_object*)&l_main___closed__264_value)}};
static const lean_object* l_main___closed__265 = (const lean_object*)&l_main___closed__265_value;
static const lean_string_object l_main___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_AccumulateComplete"};
static const lean_object* l_main___closed__266 = (const lean_object*)&l_main___closed__266_value;
static const lean_ctor_object l_main___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__266_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_object* l_main___closed__267 = (const lean_object*)&l_main___closed__267_value;
static const lean_array_object l_main___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__267_value)}};
static const lean_object* l_main___closed__268 = (const lean_object*)&l_main___closed__268_value;
static const lean_string_object l_main___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reference_split"};
static const lean_object* l_main___closed__269 = (const lean_object*)&l_main___closed__269_value;
static const lean_ctor_object l_main___closed__270_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__266_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__270_value_aux_0),((lean_object*)&l_main___closed__269_value),LEAN_SCALAR_PTR_LITERAL(53, 78, 70, 0, 122, 104, 106, 162)}};
static const lean_object* l_main___closed__270 = (const lean_object*)&l_main___closed__270_value;
static const lean_string_object l_main___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reference"};
static const lean_object* l_main___closed__271 = (const lean_object*)&l_main___closed__271_value;
static const lean_ctor_object l_main___closed__272_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__266_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__272_value_aux_0),((lean_object*)&l_main___closed__271_value),LEAN_SCALAR_PTR_LITERAL(200, 229, 182, 126, 216, 100, 214, 30)}};
static const lean_object* l_main___closed__272 = (const lean_object*)&l_main___closed__272_value;
static const lean_string_object l_main___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "native"};
static const lean_object* l_main___closed__273 = (const lean_object*)&l_main___closed__273_value;
static const lean_ctor_object l_main___closed__274_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__266_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__274_value_aux_0),((lean_object*)&l_main___closed__273_value),LEAN_SCALAR_PTR_LITERAL(139, 101, 84, 168, 235, 72, 251, 103)}};
static const lean_object* l_main___closed__274 = (const lean_object*)&l_main___closed__274_value;
static const lean_array_object l_main___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__270_value),((lean_object*)&l_main___closed__272_value),((lean_object*)&l_main___closed__274_value)}};
static const lean_object* l_main___closed__275 = (const lean_object*)&l_main___closed__275_value;
static const lean_string_object l_main___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_TailModel"};
static const lean_object* l_main___closed__276 = (const lean_object*)&l_main___closed__276_value;
static const lean_ctor_object l_main___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__276_value),LEAN_SCALAR_PTR_LITERAL(157, 199, 125, 235, 91, 24, 105, 238)}};
static const lean_object* l_main___closed__277 = (const lean_object*)&l_main___closed__277_value;
static const lean_array_object l_main___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__277_value)}};
static const lean_object* l_main___closed__278 = (const lean_object*)&l_main___closed__278_value;
static const lean_ctor_object l_main___closed__279_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__276_value),LEAN_SCALAR_PTR_LITERAL(157, 199, 125, 235, 91, 24, 105, 238)}};
static const lean_ctor_object l_main___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__279_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(228, 202, 46, 22, 38, 12, 190, 47)}};
static const lean_object* l_main___closed__279 = (const lean_object*)&l_main___closed__279_value;
static const lean_array_object l_main___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__279_value)}};
static const lean_object* l_main___closed__280 = (const lean_object*)&l_main___closed__280_value;
static const lean_string_object l_main___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrimitiveTotal"};
static const lean_object* l_main___closed__281 = (const lean_object*)&l_main___closed__281_value;
static const lean_ctor_object l_main___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_object* l_main___closed__282 = (const lean_object*)&l_main___closed__282_value;
static const lean_array_object l_main___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__282_value)}};
static const lean_object* l_main___closed__283 = (const lean_object*)&l_main___closed__283_value;
static const lean_string_object l_main___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_main___closed__284 = (const lean_object*)&l_main___closed__284_value;
static const lean_ctor_object l_main___closed__285_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_ctor_object l_main___closed__285_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__285_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(72, 248, 151, 53, 138, 193, 201, 134)}};
static const lean_object* l_main___closed__285 = (const lean_object*)&l_main___closed__285_value;
static const lean_string_object l_main___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "power"};
static const lean_object* l_main___closed__286 = (const lean_object*)&l_main___closed__286_value;
static const lean_ctor_object l_main___closed__287_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_ctor_object l_main___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__287_value_aux_0),((lean_object*)&l_main___closed__286_value),LEAN_SCALAR_PTR_LITERAL(32, 190, 36, 8, 135, 52, 153, 36)}};
static const lean_object* l_main___closed__287 = (const lean_object*)&l_main___closed__287_value;
static const lean_array_object l_main___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__285_value),((lean_object*)&l_main___closed__287_value)}};
static const lean_object* l_main___closed__288 = (const lean_object*)&l_main___closed__288_value;
static const lean_string_object l_main___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_PrimitiveBindings"};
static const lean_object* l_main___closed__289 = (const lean_object*)&l_main___closed__289_value;
static const lean_ctor_object l_main___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_object* l_main___closed__290 = (const lean_object*)&l_main___closed__290_value;
static const lean_array_object l_main___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__290_value)}};
static const lean_object* l_main___closed__291 = (const lean_object*)&l_main___closed__291_value;
static const lean_ctor_object l_main___closed__292_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_0),((lean_object*)&l_main___closed__286_value),LEAN_SCALAR_PTR_LITERAL(120, 243, 220, 247, 71, 9, 232, 119)}};
static const lean_object* l_main___closed__292 = (const lean_object*)&l_main___closed__292_value;
static const lean_ctor_object l_main___closed__293_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__293_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__293_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(80, 228, 26, 32, 77, 167, 161, 213)}};
static const lean_object* l_main___closed__293 = (const lean_object*)&l_main___closed__293_value;
static const lean_ctor_object l_main___closed__294_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__294_value_aux_0),((lean_object*)&l_main___closed__179_value),LEAN_SCALAR_PTR_LITERAL(127, 182, 89, 139, 22, 116, 154, 185)}};
static const lean_object* l_main___closed__294 = (const lean_object*)&l_main___closed__294_value;
static const lean_string_object l_main___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "product_returns"};
static const lean_object* l_main___closed__295 = (const lean_object*)&l_main___closed__295_value;
static const lean_ctor_object l_main___closed__296_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__296_value_aux_0),((lean_object*)&l_main___closed__295_value),LEAN_SCALAR_PTR_LITERAL(218, 159, 58, 95, 166, 71, 250, 197)}};
static const lean_object* l_main___closed__296 = (const lean_object*)&l_main___closed__296_value;
static const lean_array_object l_main___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__292_value),((lean_object*)&l_main___closed__293_value),((lean_object*)&l_main___closed__294_value),((lean_object*)&l_main___closed__296_value)}};
static const lean_object* l_main___closed__297 = (const lean_object*)&l_main___closed__297_value;
static const lean_string_object l_main___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_StageWideFields"};
static const lean_object* l_main___closed__298 = (const lean_object*)&l_main___closed__298_value;
static const lean_ctor_object l_main___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__298_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_object* l_main___closed__299 = (const lean_object*)&l_main___closed__299_value;
static const lean_array_object l_main___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__299_value)}};
static const lean_object* l_main___closed__300 = (const lean_object*)&l_main___closed__300_value;
static const lean_ctor_object l_main___closed__301_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__298_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_ctor_object l_main___closed__301_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__301_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(126, 134, 8, 36, 14, 64, 232, 5)}};
static const lean_object* l_main___closed__301 = (const lean_object*)&l_main___closed__301_value;
static const lean_ctor_object l_main___closed__302_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__298_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_ctor_object l_main___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__302_value_aux_0),((lean_object*)&l_main___closed__179_value),LEAN_SCALAR_PTR_LITERAL(249, 12, 234, 27, 52, 60, 8, 210)}};
static const lean_object* l_main___closed__302 = (const lean_object*)&l_main___closed__302_value;
static const lean_array_object l_main___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__301_value),((lean_object*)&l_main___closed__302_value)}};
static const lean_object* l_main___closed__303 = (const lean_object*)&l_main___closed__303_value;
static const lean_string_object l_main___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_StageFields"};
static const lean_object* l_main___closed__304 = (const lean_object*)&l_main___closed__304_value;
static const lean_ctor_object l_main___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_object* l_main___closed__305 = (const lean_object*)&l_main___closed__305_value;
static const lean_array_object l_main___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__305_value)}};
static const lean_object* l_main___closed__306 = (const lean_object*)&l_main___closed__306_value;
static const lean_string_object l_main___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "native_q_roundtrip"};
static const lean_object* l_main___closed__307 = (const lean_object*)&l_main___closed__307_value;
static const lean_ctor_object l_main___closed__308_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__308_value_aux_0),((lean_object*)&l_main___closed__307_value),LEAN_SCALAR_PTR_LITERAL(155, 57, 31, 224, 228, 66, 189, 216)}};
static const lean_object* l_main___closed__308 = (const lean_object*)&l_main___closed__308_value;
static const lean_string_object l_main___closed__309_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "stage_q_roundtrip"};
static const lean_object* l_main___closed__309 = (const lean_object*)&l_main___closed__309_value;
static const lean_ctor_object l_main___closed__310_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__310_value_aux_0),((lean_object*)&l_main___closed__309_value),LEAN_SCALAR_PTR_LITERAL(194, 148, 39, 25, 40, 226, 186, 153)}};
static const lean_object* l_main___closed__310 = (const lean_object*)&l_main___closed__310_value;
static const lean_string_object l_main___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "native_e_roundtrip"};
static const lean_object* l_main___closed__311 = (const lean_object*)&l_main___closed__311_value;
static const lean_ctor_object l_main___closed__312_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__312_value_aux_0),((lean_object*)&l_main___closed__311_value),LEAN_SCALAR_PTR_LITERAL(160, 6, 125, 229, 39, 141, 99, 176)}};
static const lean_object* l_main___closed__312 = (const lean_object*)&l_main___closed__312_value;
static const lean_string_object l_main___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "stage_e_roundtrip"};
static const lean_object* l_main___closed__313 = (const lean_object*)&l_main___closed__313_value;
static const lean_ctor_object l_main___closed__314_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__314_value_aux_0),((lean_object*)&l_main___closed__313_value),LEAN_SCALAR_PTR_LITERAL(201, 17, 231, 120, 128, 9, 149, 199)}};
static const lean_object* l_main___closed__314 = (const lean_object*)&l_main___closed__314_value;
static const lean_string_object l_main___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "canonical_q"};
static const lean_object* l_main___closed__315 = (const lean_object*)&l_main___closed__315_value;
static const lean_ctor_object l_main___closed__316_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__316_value_aux_0),((lean_object*)&l_main___closed__315_value),LEAN_SCALAR_PTR_LITERAL(37, 113, 62, 137, 175, 52, 111, 150)}};
static const lean_object* l_main___closed__316 = (const lean_object*)&l_main___closed__316_value;
static const lean_string_object l_main___closed__317_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "canonical_e"};
static const lean_object* l_main___closed__317 = (const lean_object*)&l_main___closed__317_value;
static const lean_ctor_object l_main___closed__318_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__318_value_aux_0),((lean_object*)&l_main___closed__317_value),LEAN_SCALAR_PTR_LITERAL(38, 151, 244, 177, 194, 108, 179, 131)}};
static const lean_object* l_main___closed__318 = (const lean_object*)&l_main___closed__318_value;
static const lean_ctor_object l_main___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_0),((lean_object*)&l_main___closed__286_value),LEAN_SCALAR_PTR_LITERAL(9, 116, 59, 102, 165, 94, 81, 29)}};
static const lean_object* l_main___closed__319 = (const lean_object*)&l_main___closed__319_value;
static const lean_array_object l_main___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__308_value),((lean_object*)&l_main___closed__310_value),((lean_object*)&l_main___closed__312_value),((lean_object*)&l_main___closed__314_value),((lean_object*)&l_main___closed__316_value),((lean_object*)&l_main___closed__318_value),((lean_object*)&l_main___closed__319_value)}};
static const lean_object* l_main___closed__320 = (const lean_object*)&l_main___closed__320_value;
static const lean_string_object l_main___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEV_MaskQM"};
static const lean_object* l_main___closed__321 = (const lean_object*)&l_main___closed__321_value;
static const lean_ctor_object l_main___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__321_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_object* l_main___closed__322 = (const lean_object*)&l_main___closed__322_value;
static const lean_array_object l_main___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__322_value)}};
static const lean_object* l_main___closed__323 = (const lean_object*)&l_main___closed__323_value;
static const lean_ctor_object l_main___closed__324_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__321_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__324_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__324_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(141, 36, 98, 8, 240, 255, 221, 104)}};
static const lean_object* l_main___closed__324 = (const lean_object*)&l_main___closed__324_value;
static const lean_string_object l_main___closed__325_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "multiply"};
static const lean_object* l_main___closed__325 = (const lean_object*)&l_main___closed__325_value;
static const lean_ctor_object l_main___closed__326_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__321_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__326_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__326_value_aux_0),((lean_object*)&l_main___closed__325_value),LEAN_SCALAR_PTR_LITERAL(28, 6, 163, 46, 26, 47, 206, 125)}};
static const lean_object* l_main___closed__326 = (const lean_object*)&l_main___closed__326_value;
static const lean_string_object l_main___closed__327_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normalization"};
static const lean_object* l_main___closed__327 = (const lean_object*)&l_main___closed__327_value;
static const lean_ctor_object l_main___closed__328_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__321_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__328_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__328_value_aux_0),((lean_object*)&l_main___closed__327_value),LEAN_SCALAR_PTR_LITERAL(77, 137, 85, 187, 103, 93, 201, 122)}};
static const lean_object* l_main___closed__328 = (const lean_object*)&l_main___closed__328_value;
static const lean_array_object l_main___closed__329_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__324_value),((lean_object*)&l_main___closed__326_value),((lean_object*)&l_main___closed__328_value)}};
static const lean_object* l_main___closed__329 = (const lean_object*)&l_main___closed__329_value;
static const lean_string_object l_main___closed__330_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_MaskCarriers"};
static const lean_object* l_main___closed__330 = (const lean_object*)&l_main___closed__330_value;
static const lean_ctor_object l_main___closed__331_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_object* l_main___closed__331 = (const lean_object*)&l_main___closed__331_value;
static const lean_array_object l_main___closed__332_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__331_value)}};
static const lean_object* l_main___closed__332 = (const lean_object*)&l_main___closed__332_value;
static const lean_string_object l_main___closed__333_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_roundtrip"};
static const lean_object* l_main___closed__333 = (const lean_object*)&l_main___closed__333_value;
static const lean_ctor_object l_main___closed__334_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__334_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__334_value_aux_0),((lean_object*)&l_main___closed__333_value),LEAN_SCALAR_PTR_LITERAL(130, 208, 151, 109, 83, 177, 121, 20)}};
static const lean_object* l_main___closed__334 = (const lean_object*)&l_main___closed__334_value;
static const lean_string_object l_main___closed__335_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mask_roundtrip"};
static const lean_object* l_main___closed__335 = (const lean_object*)&l_main___closed__335_value;
static const lean_ctor_object l_main___closed__336_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__336_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__336_value_aux_0),((lean_object*)&l_main___closed__335_value),LEAN_SCALAR_PTR_LITERAL(218, 110, 195, 93, 161, 110, 200, 7)}};
static const lean_object* l_main___closed__336 = (const lean_object*)&l_main___closed__336_value;
static const lean_string_object l_main___closed__337_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_main___closed__337 = (const lean_object*)&l_main___closed__337_value;
static const lean_ctor_object l_main___closed__338_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__338_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__338_value_aux_0),((lean_object*)&l_main___closed__337_value),LEAN_SCALAR_PTR_LITERAL(82, 165, 145, 213, 132, 246, 41, 37)}};
static const lean_object* l_main___closed__338 = (const lean_object*)&l_main___closed__338_value;
static const lean_string_object l_main___closed__339_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "words"};
static const lean_object* l_main___closed__339 = (const lean_object*)&l_main___closed__339_value;
static const lean_ctor_object l_main___closed__340_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__340_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__340_value_aux_0),((lean_object*)&l_main___closed__339_value),LEAN_SCALAR_PTR_LITERAL(214, 85, 166, 61, 123, 195, 168, 158)}};
static const lean_object* l_main___closed__340 = (const lean_object*)&l_main___closed__340_value;
static const lean_string_object l_main___closed__341_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "product_words"};
static const lean_object* l_main___closed__341 = (const lean_object*)&l_main___closed__341_value;
static const lean_ctor_object l_main___closed__342_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__342_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__342_value_aux_0),((lean_object*)&l_main___closed__341_value),LEAN_SCALAR_PTR_LITERAL(158, 236, 12, 137, 49, 66, 11, 253)}};
static const lean_object* l_main___closed__342 = (const lean_object*)&l_main___closed__342_value;
static const lean_string_object l_main___closed__343_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "words_injective"};
static const lean_object* l_main___closed__343 = (const lean_object*)&l_main___closed__343_value;
static const lean_ctor_object l_main___closed__344_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__344_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__344_value_aux_0),((lean_object*)&l_main___closed__343_value),LEAN_SCALAR_PTR_LITERAL(239, 150, 211, 222, 99, 186, 75, 180)}};
static const lean_object* l_main___closed__344 = (const lean_object*)&l_main___closed__344_value;
static const lean_string_object l_main___closed__345_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_injective"};
static const lean_object* l_main___closed__345 = (const lean_object*)&l_main___closed__345_value;
static const lean_ctor_object l_main___closed__346_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__346_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__346_value_aux_0),((lean_object*)&l_main___closed__345_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 46, 135, 21, 92, 221, 217)}};
static const lean_object* l_main___closed__346 = (const lean_object*)&l_main___closed__346_value;
static const lean_array_object l_main___closed__347_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__334_value),((lean_object*)&l_main___closed__336_value),((lean_object*)&l_main___closed__338_value),((lean_object*)&l_main___closed__340_value),((lean_object*)&l_main___closed__342_value),((lean_object*)&l_main___closed__344_value),((lean_object*)&l_main___closed__346_value)}};
static const lean_object* l_main___closed__347 = (const lean_object*)&l_main___closed__347_value;
static const lean_string_object l_main___closed__348_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_AccumulatePrefix"};
static const lean_object* l_main___closed__348 = (const lean_object*)&l_main___closed__348_value;
static const lean_ctor_object l_main___closed__349_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_object* l_main___closed__349 = (const lean_object*)&l_main___closed__349_value;
static const lean_array_object l_main___closed__350_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__349_value)}};
static const lean_object* l_main___closed__350 = (const lean_object*)&l_main___closed__350_value;
static const lean_string_object l_main___closed__351_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "installs_commute"};
static const lean_object* l_main___closed__351 = (const lean_object*)&l_main___closed__351_value;
static const lean_ctor_object l_main___closed__352_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_ctor_object l_main___closed__352_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_0),((lean_object*)&l_main___closed__351_value),LEAN_SCALAR_PTR_LITERAL(136, 29, 12, 148, 180, 157, 133, 45)}};
static const lean_object* l_main___closed__352 = (const lean_object*)&l_main___closed__352_value;
static const lean_ctor_object l_main___closed__353_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_ctor_object l_main___closed__353_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__353_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(17, 175, 112, 178, 6, 235, 52, 141)}};
static const lean_object* l_main___closed__353 = (const lean_object*)&l_main___closed__353_value;
static const lean_array_object l_main___closed__354_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__352_value),((lean_object*)&l_main___closed__353_value)}};
static const lean_object* l_main___closed__354 = (const lean_object*)&l_main___closed__354_value;
static const lean_string_object l_main___closed__355_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_RowLoop"};
static const lean_object* l_main___closed__355 = (const lean_object*)&l_main___closed__355_value;
static const lean_ctor_object l_main___closed__356_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__355_value),LEAN_SCALAR_PTR_LITERAL(92, 115, 240, 36, 51, 211, 171, 148)}};
static const lean_object* l_main___closed__356 = (const lean_object*)&l_main___closed__356_value;
static const lean_array_object l_main___closed__357_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__356_value)}};
static const lean_object* l_main___closed__357 = (const lean_object*)&l_main___closed__357_value;
static const lean_ctor_object l_main___closed__358_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__355_value),LEAN_SCALAR_PTR_LITERAL(92, 115, 240, 36, 51, 211, 171, 148)}};
static const lean_ctor_object l_main___closed__358_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__358_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(185, 53, 44, 172, 134, 189, 245, 103)}};
static const lean_object* l_main___closed__358 = (const lean_object*)&l_main___closed__358_value;
static const lean_array_object l_main___closed__359_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__358_value)}};
static const lean_object* l_main___closed__359 = (const lean_object*)&l_main___closed__359_value;
static const lean_string_object l_main___closed__360_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_RowStep"};
static const lean_object* l_main___closed__360 = (const lean_object*)&l_main___closed__360_value;
static const lean_ctor_object l_main___closed__361_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__360_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_object* l_main___closed__361 = (const lean_object*)&l_main___closed__361_value;
static const lean_array_object l_main___closed__362_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__361_value)}};
static const lean_object* l_main___closed__362 = (const lean_object*)&l_main___closed__362_value;
static const lean_string_object l_main___closed__363_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* l_main___closed__363 = (const lean_object*)&l_main___closed__363_value;
static const lean_ctor_object l_main___closed__364_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__360_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_ctor_object l_main___closed__364_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__364_value_aux_0),((lean_object*)&l_main___closed__363_value),LEAN_SCALAR_PTR_LITERAL(98, 105, 31, 115, 79, 219, 35, 90)}};
static const lean_object* l_main___closed__364 = (const lean_object*)&l_main___closed__364_value;
static const lean_string_object l_main___closed__365_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_main___closed__365 = (const lean_object*)&l_main___closed__365_value;
static const lean_ctor_object l_main___closed__366_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__360_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_ctor_object l_main___closed__366_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__366_value_aux_0),((lean_object*)&l_main___closed__365_value),LEAN_SCALAR_PTR_LITERAL(122, 232, 220, 11, 52, 202, 2, 209)}};
static const lean_object* l_main___closed__366 = (const lean_object*)&l_main___closed__366_value;
static const lean_array_object l_main___closed__367_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__364_value),((lean_object*)&l_main___closed__366_value)}};
static const lean_object* l_main___closed__367 = (const lean_object*)&l_main___closed__367_value;
static const lean_string_object l_main___closed__368_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_CtorResults"};
static const lean_object* l_main___closed__368 = (const lean_object*)&l_main___closed__368_value;
static const lean_ctor_object l_main___closed__369_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__368_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_object* l_main___closed__369 = (const lean_object*)&l_main___closed__369_value;
static const lean_array_object l_main___closed__370_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__369_value)}};
static const lean_object* l_main___closed__370 = (const lean_object*)&l_main___closed__370_value;
static const lean_string_object l_main___closed__371_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "m31"};
static const lean_object* l_main___closed__371 = (const lean_object*)&l_main___closed__371_value;
static const lean_ctor_object l_main___closed__372_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__368_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_ctor_object l_main___closed__372_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__372_value_aux_0),((lean_object*)&l_main___closed__371_value),LEAN_SCALAR_PTR_LITERAL(210, 198, 21, 66, 212, 234, 99, 160)}};
static const lean_object* l_main___closed__372 = (const lean_object*)&l_main___closed__372_value;
static const lean_string_object l_main___closed__373_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "qm"};
static const lean_object* l_main___closed__373 = (const lean_object*)&l_main___closed__373_value;
static const lean_ctor_object l_main___closed__374_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__368_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_ctor_object l_main___closed__374_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__374_value_aux_0),((lean_object*)&l_main___closed__373_value),LEAN_SCALAR_PTR_LITERAL(196, 70, 227, 155, 170, 89, 140, 236)}};
static const lean_object* l_main___closed__374 = (const lean_object*)&l_main___closed__374_value;
static const lean_array_object l_main___closed__375_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__372_value),((lean_object*)&l_main___closed__374_value)}};
static const lean_object* l_main___closed__375 = (const lean_object*)&l_main___closed__375_value;
static const lean_string_object l_main___closed__376_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_BasisProducer"};
static const lean_object* l_main___closed__376 = (const lean_object*)&l_main___closed__376_value;
static const lean_ctor_object l_main___closed__377_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__376_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_object* l_main___closed__377 = (const lean_object*)&l_main___closed__377_value;
static const lean_array_object l_main___closed__378_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__377_value)}};
static const lean_object* l_main___closed__378 = (const lean_object*)&l_main___closed__378_value;
static const lean_ctor_object l_main___closed__379_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__376_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__379_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__379_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(138, 20, 62, 99, 136, 142, 96, 108)}};
static const lean_object* l_main___closed__379 = (const lean_object*)&l_main___closed__379_value;
static const lean_ctor_object l_main___closed__380_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__376_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__380_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__380_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(153, 167, 129, 212, 4, 171, 142, 82)}};
static const lean_object* l_main___closed__380 = (const lean_object*)&l_main___closed__380_value;
static const lean_string_object l_main___closed__381_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "read_canonical"};
static const lean_object* l_main___closed__381 = (const lean_object*)&l_main___closed__381_value;
static const lean_ctor_object l_main___closed__382_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__376_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__382_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__382_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(101, 8, 57, 218, 103, 141, 234, 38)}};
static const lean_object* l_main___closed__382 = (const lean_object*)&l_main___closed__382_value;
static const lean_array_object l_main___closed__383_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__379_value),((lean_object*)&l_main___closed__380_value),((lean_object*)&l_main___closed__382_value)}};
static const lean_object* l_main___closed__383 = (const lean_object*)&l_main___closed__383_value;
static const lean_string_object l_main___closed__384_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_CtorNormalization"};
static const lean_object* l_main___closed__384 = (const lean_object*)&l_main___closed__384_value;
static const lean_ctor_object l_main___closed__385_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_object* l_main___closed__385 = (const lean_object*)&l_main___closed__385_value;
static const lean_array_object l_main___closed__386_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__385_value)}};
static const lean_object* l_main___closed__386 = (const lean_object*)&l_main___closed__386_value;
static const lean_ctor_object l_main___closed__387_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__387_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__387_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(142, 136, 155, 22, 158, 201, 157, 10)}};
static const lean_object* l_main___closed__387 = (const lean_object*)&l_main___closed__387_value;
static const lean_string_object l_main___closed__388_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduce_identity"};
static const lean_object* l_main___closed__388 = (const lean_object*)&l_main___closed__388_value;
static const lean_ctor_object l_main___closed__389_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__389_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__389_value_aux_0),((lean_object*)&l_main___closed__388_value),LEAN_SCALAR_PTR_LITERAL(61, 252, 131, 126, 159, 182, 16, 255)}};
static const lean_object* l_main___closed__389 = (const lean_object*)&l_main___closed__389_value;
static const lean_string_object l_main___closed__390_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "identity"};
static const lean_object* l_main___closed__390 = (const lean_object*)&l_main___closed__390_value;
static const lean_ctor_object l_main___closed__391_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__391_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__391_value_aux_0),((lean_object*)&l_main___closed__390_value),LEAN_SCALAR_PTR_LITERAL(210, 71, 87, 226, 127, 90, 131, 111)}};
static const lean_object* l_main___closed__391 = (const lean_object*)&l_main___closed__391_value;
static const lean_ctor_object l_main___closed__392_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__392_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__392_value_aux_0),((lean_object*)&l_main___closed__200_value),LEAN_SCALAR_PTR_LITERAL(221, 105, 11, 156, 18, 104, 45, 153)}};
static const lean_object* l_main___closed__392 = (const lean_object*)&l_main___closed__392_value;
static const lean_array_object l_main___closed__393_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__387_value),((lean_object*)&l_main___closed__389_value),((lean_object*)&l_main___closed__391_value),((lean_object*)&l_main___closed__392_value)}};
static const lean_object* l_main___closed__393 = (const lean_object*)&l_main___closed__393_value;
static const lean_string_object l_main___closed__394_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NEV_BorrowMaps"};
static const lean_object* l_main___closed__394 = (const lean_object*)&l_main___closed__394_value;
static const lean_ctor_object l_main___closed__395_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__394_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_object* l_main___closed__395 = (const lean_object*)&l_main___closed__395_value;
static const lean_array_object l_main___closed__396_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__395_value)}};
static const lean_object* l_main___closed__396 = (const lean_object*)&l_main___closed__396_value;
static const lean_string_object l_main___closed__397_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "vector_read"};
static const lean_object* l_main___closed__397 = (const lean_object*)&l_main___closed__397_value;
static const lean_ctor_object l_main___closed__398_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__394_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_ctor_object l_main___closed__398_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__398_value_aux_0),((lean_object*)&l_main___closed__397_value),LEAN_SCALAR_PTR_LITERAL(107, 114, 4, 119, 10, 205, 72, 20)}};
static const lean_object* l_main___closed__398 = (const lean_object*)&l_main___closed__398_value;
static const lean_string_object l_main___closed__399_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "weight_read"};
static const lean_object* l_main___closed__399 = (const lean_object*)&l_main___closed__399_value;
static const lean_ctor_object l_main___closed__400_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__394_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_ctor_object l_main___closed__400_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__400_value_aux_0),((lean_object*)&l_main___closed__399_value),LEAN_SCALAR_PTR_LITERAL(66, 215, 171, 160, 143, 191, 27, 224)}};
static const lean_object* l_main___closed__400 = (const lean_object*)&l_main___closed__400_value;
static const lean_array_object l_main___closed__401_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__398_value),((lean_object*)&l_main___closed__400_value)}};
static const lean_object* l_main___closed__401 = (const lean_object*)&l_main___closed__401_value;
static const lean_string_object l_main___closed__402_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_PushUse"};
static const lean_object* l_main___closed__402 = (const lean_object*)&l_main___closed__402_value;
static const lean_ctor_object l_main___closed__403_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__402_value),LEAN_SCALAR_PTR_LITERAL(97, 126, 68, 27, 4, 34, 116, 169)}};
static const lean_object* l_main___closed__403 = (const lean_object*)&l_main___closed__403_value;
static const lean_array_object l_main___closed__404_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__403_value)}};
static const lean_object* l_main___closed__404 = (const lean_object*)&l_main___closed__404_value;
static const lean_ctor_object l_main___closed__405_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__402_value),LEAN_SCALAR_PTR_LITERAL(97, 126, 68, 27, 4, 34, 116, 169)}};
static const lean_ctor_object l_main___closed__405_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__405_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(200, 204, 223, 157, 21, 151, 112, 97)}};
static const lean_object* l_main___closed__405 = (const lean_object*)&l_main___closed__405_value;
static const lean_array_object l_main___closed__406_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__405_value)}};
static const lean_object* l_main___closed__406 = (const lean_object*)&l_main___closed__406_value;
static const lean_string_object l_main___closed__407_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_AccumulateTail"};
static const lean_object* l_main___closed__407 = (const lean_object*)&l_main___closed__407_value;
static const lean_ctor_object l_main___closed__408_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__407_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_object* l_main___closed__408 = (const lean_object*)&l_main___closed__408_value;
static const lean_array_object l_main___closed__409_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__408_value)}};
static const lean_object* l_main___closed__409 = (const lean_object*)&l_main___closed__409_value;
static const lean_string_object l_main___closed__410_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "source_cut"};
static const lean_object* l_main___closed__410 = (const lean_object*)&l_main___closed__410_value;
static const lean_ctor_object l_main___closed__411_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__407_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_ctor_object l_main___closed__411_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__411_value_aux_0),((lean_object*)&l_main___closed__410_value),LEAN_SCALAR_PTR_LITERAL(62, 124, 8, 201, 51, 162, 133, 218)}};
static const lean_object* l_main___closed__411 = (const lean_object*)&l_main___closed__411_value;
static const lean_string_object l_main___closed__412_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "successful_frame"};
static const lean_object* l_main___closed__412 = (const lean_object*)&l_main___closed__412_value;
static const lean_ctor_object l_main___closed__413_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__407_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_ctor_object l_main___closed__413_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__413_value_aux_0),((lean_object*)&l_main___closed__412_value),LEAN_SCALAR_PTR_LITERAL(243, 39, 41, 106, 151, 45, 123, 153)}};
static const lean_object* l_main___closed__413 = (const lean_object*)&l_main___closed__413_value;
static const lean_array_object l_main___closed__414_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__411_value),((lean_object*)&l_main___closed__413_value)}};
static const lean_object* l_main___closed__414 = (const lean_object*)&l_main___closed__414_value;
static const lean_string_object l_main___closed__415_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_BasisOuterRaw"};
static const lean_object* l_main___closed__415 = (const lean_object*)&l_main___closed__415_value;
static const lean_ctor_object l_main___closed__416_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__415_value),LEAN_SCALAR_PTR_LITERAL(147, 92, 74, 164, 13, 225, 12, 235)}};
static const lean_object* l_main___closed__416 = (const lean_object*)&l_main___closed__416_value;
static const lean_array_object l_main___closed__417_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__416_value)}};
static const lean_object* l_main___closed__417 = (const lean_object*)&l_main___closed__417_value;
static const lean_string_object l_main___closed__418_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "levels_eq"};
static const lean_object* l_main___closed__418 = (const lean_object*)&l_main___closed__418_value;
static const lean_ctor_object l_main___closed__419_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__415_value),LEAN_SCALAR_PTR_LITERAL(147, 92, 74, 164, 13, 225, 12, 235)}};
static const lean_ctor_object l_main___closed__419_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__419_value_aux_0),((lean_object*)&l_main___closed__418_value),LEAN_SCALAR_PTR_LITERAL(162, 74, 55, 75, 104, 78, 184, 204)}};
static const lean_object* l_main___closed__419 = (const lean_object*)&l_main___closed__419_value;
static const lean_array_object l_main___closed__420_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__419_value)}};
static const lean_object* l_main___closed__420 = (const lean_object*)&l_main___closed__420_value;
static const lean_string_object l_main___closed__421_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_AccumulateCallees"};
static const lean_object* l_main___closed__421 = (const lean_object*)&l_main___closed__421_value;
static const lean_ctor_object l_main___closed__422_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_object* l_main___closed__422 = (const lean_object*)&l_main___closed__422_value;
static const lean_array_object l_main___closed__423_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__422_value)}};
static const lean_object* l_main___closed__423 = (const lean_object*)&l_main___closed__423_value;
static const lean_string_object l_main___closed__424_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_e_reverse"};
static const lean_object* l_main___closed__424 = (const lean_object*)&l_main___closed__424_value;
static const lean_ctor_object l_main___closed__425_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__425_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__425_value_aux_0),((lean_object*)&l_main___closed__424_value),LEAN_SCALAR_PTR_LITERAL(150, 164, 67, 183, 104, 114, 78, 163)}};
static const lean_object* l_main___closed__425 = (const lean_object*)&l_main___closed__425_value;
static const lean_string_object l_main___closed__426_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_q_reverse"};
static const lean_object* l_main___closed__426 = (const lean_object*)&l_main___closed__426_value;
static const lean_ctor_object l_main___closed__427_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__427_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__427_value_aux_0),((lean_object*)&l_main___closed__426_value),LEAN_SCALAR_PTR_LITERAL(215, 194, 151, 125, 2, 44, 166, 206)}};
static const lean_object* l_main___closed__427 = (const lean_object*)&l_main___closed__427_value;
static const lean_string_object l_main___closed__428_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ctor_e_reverse"};
static const lean_object* l_main___closed__428 = (const lean_object*)&l_main___closed__428_value;
static const lean_ctor_object l_main___closed__429_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__429_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__429_value_aux_0),((lean_object*)&l_main___closed__428_value),LEAN_SCALAR_PTR_LITERAL(16, 39, 51, 58, 214, 200, 60, 171)}};
static const lean_object* l_main___closed__429 = (const lean_object*)&l_main___closed__429_value;
static const lean_string_object l_main___closed__430_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "wide_add"};
static const lean_object* l_main___closed__430 = (const lean_object*)&l_main___closed__430_value;
static const lean_ctor_object l_main___closed__431_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__431_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__431_value_aux_0),((lean_object*)&l_main___closed__430_value),LEAN_SCALAR_PTR_LITERAL(34, 218, 202, 210, 8, 39, 79, 50)}};
static const lean_object* l_main___closed__431 = (const lean_object*)&l_main___closed__431_value;
static const lean_string_object l_main___closed__432_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wide_product"};
static const lean_object* l_main___closed__432 = (const lean_object*)&l_main___closed__432_value;
static const lean_ctor_object l_main___closed__433_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__433_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__433_value_aux_0),((lean_object*)&l_main___closed__432_value),LEAN_SCALAR_PTR_LITERAL(252, 210, 17, 228, 78, 86, 70, 134)}};
static const lean_object* l_main___closed__433 = (const lean_object*)&l_main___closed__433_value;
static const lean_string_object l_main___closed__434_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "qm_product"};
static const lean_object* l_main___closed__434 = (const lean_object*)&l_main___closed__434_value;
static const lean_ctor_object l_main___closed__435_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__435_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__435_value_aux_0),((lean_object*)&l_main___closed__434_value),LEAN_SCALAR_PTR_LITERAL(159, 66, 150, 93, 38, 46, 111, 155)}};
static const lean_object* l_main___closed__435 = (const lean_object*)&l_main___closed__435_value;
static const lean_string_object l_main___closed__436_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "from_qm"};
static const lean_object* l_main___closed__436 = (const lean_object*)&l_main___closed__436_value;
static const lean_ctor_object l_main___closed__437_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__437_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__437_value_aux_0),((lean_object*)&l_main___closed__436_value),LEAN_SCALAR_PTR_LITERAL(238, 242, 106, 160, 170, 194, 103, 116)}};
static const lean_object* l_main___closed__437 = (const lean_object*)&l_main___closed__437_value;
static const lean_string_object l_main___closed__438_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l_main___closed__438 = (const lean_object*)&l_main___closed__438_value;
static const lean_ctor_object l_main___closed__439_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__439_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__439_value_aux_0),((lean_object*)&l_main___closed__438_value),LEAN_SCALAR_PTR_LITERAL(125, 149, 78, 24, 134, 220, 102, 223)}};
static const lean_object* l_main___closed__439 = (const lean_object*)&l_main___closed__439_value;
static const lean_string_object l_main___closed__440_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "from_m31"};
static const lean_object* l_main___closed__440 = (const lean_object*)&l_main___closed__440_value;
static const lean_ctor_object l_main___closed__441_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__421_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__441_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__441_value_aux_0),((lean_object*)&l_main___closed__440_value),LEAN_SCALAR_PTR_LITERAL(111, 0, 155, 214, 86, 43, 159, 215)}};
static const lean_object* l_main___closed__441 = (const lean_object*)&l_main___closed__441_value;
static const lean_array_object l_main___closed__442_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l_main___closed__425_value),((lean_object*)&l_main___closed__427_value),((lean_object*)&l_main___closed__429_value),((lean_object*)&l_main___closed__431_value),((lean_object*)&l_main___closed__433_value),((lean_object*)&l_main___closed__435_value),((lean_object*)&l_main___closed__437_value),((lean_object*)&l_main___closed__439_value),((lean_object*)&l_main___closed__441_value)}};
static const lean_object* l_main___closed__442 = (const lean_object*)&l_main___closed__442_value;
static const lean_string_object l_main___closed__443_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_BasisOuterStep"};
static const lean_object* l_main___closed__443 = (const lean_object*)&l_main___closed__443_value;
static const lean_ctor_object l_main___closed__444_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_object* l_main___closed__444 = (const lean_object*)&l_main___closed__444_value;
static const lean_array_object l_main___closed__445_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__444_value)}};
static const lean_object* l_main___closed__445 = (const lean_object*)&l_main___closed__445_value;
static const lean_ctor_object l_main___closed__446_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__446_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__446_value_aux_0),((lean_object*)&l_main___closed__325_value),LEAN_SCALAR_PTR_LITERAL(98, 165, 37, 87, 65, 230, 59, 175)}};
static const lean_object* l_main___closed__446 = (const lean_object*)&l_main___closed__446_value;
static const lean_string_object l_main___closed__447_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subtract"};
static const lean_object* l_main___closed__447 = (const lean_object*)&l_main___closed__447_value;
static const lean_ctor_object l_main___closed__448_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__448_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__448_value_aux_0),((lean_object*)&l_main___closed__447_value),LEAN_SCALAR_PTR_LITERAL(199, 124, 5, 37, 203, 213, 59, 77)}};
static const lean_object* l_main___closed__448 = (const lean_object*)&l_main___closed__448_value;
static const lean_string_object l_main___closed__449_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "double"};
static const lean_object* l_main___closed__449 = (const lean_object*)&l_main___closed__449_value;
static const lean_ctor_object l_main___closed__450_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__450_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__450_value_aux_0),((lean_object*)&l_main___closed__449_value),LEAN_SCALAR_PTR_LITERAL(118, 233, 175, 147, 231, 166, 48, 20)}};
static const lean_object* l_main___closed__450 = (const lean_object*)&l_main___closed__450_value;
static const lean_ctor_object l_main___closed__451_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__451_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__451_value_aux_0),((lean_object*)&l_main___closed__166_value),LEAN_SCALAR_PTR_LITERAL(31, 7, 225, 155, 133, 215, 182, 68)}};
static const lean_object* l_main___closed__451 = (const lean_object*)&l_main___closed__451_value;
static const lean_array_object l_main___closed__452_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__446_value),((lean_object*)&l_main___closed__448_value),((lean_object*)&l_main___closed__450_value),((lean_object*)&l_main___closed__451_value)}};
static const lean_object* l_main___closed__452 = (const lean_object*)&l_main___closed__452_value;
static const lean_string_object l_main___closed__453_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_BasisRaw"};
static const lean_object* l_main___closed__453 = (const lean_object*)&l_main___closed__453_value;
static const lean_ctor_object l_main___closed__454_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__453_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_object* l_main___closed__454 = (const lean_object*)&l_main___closed__454_value;
static const lean_array_object l_main___closed__455_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__454_value)}};
static const lean_object* l_main___closed__455 = (const lean_object*)&l_main___closed__455_value;
static const lean_string_object l_main___closed__456_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_step"};
static const lean_object* l_main___closed__456 = (const lean_object*)&l_main___closed__456_value;
static const lean_ctor_object l_main___closed__457_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__453_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__457_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__457_value_aux_0),((lean_object*)&l_main___closed__456_value),LEAN_SCALAR_PTR_LITERAL(244, 61, 64, 151, 73, 1, 23, 137)}};
static const lean_object* l_main___closed__457 = (const lean_object*)&l_main___closed__457_value;
static const lean_string_object l_main___closed__458_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_stop"};
static const lean_object* l_main___closed__458 = (const lean_object*)&l_main___closed__458_value;
static const lean_ctor_object l_main___closed__459_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__453_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__459_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__459_value_aux_0),((lean_object*)&l_main___closed__458_value),LEAN_SCALAR_PTR_LITERAL(126, 141, 50, 248, 149, 52, 169, 107)}};
static const lean_object* l_main___closed__459 = (const lean_object*)&l_main___closed__459_value;
static const lean_string_object l_main___closed__460_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_loop"};
static const lean_object* l_main___closed__460 = (const lean_object*)&l_main___closed__460_value;
static const lean_ctor_object l_main___closed__461_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__453_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__461_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__461_value_aux_0),((lean_object*)&l_main___closed__460_value),LEAN_SCALAR_PTR_LITERAL(31, 141, 210, 117, 243, 125, 50, 25)}};
static const lean_object* l_main___closed__461 = (const lean_object*)&l_main___closed__461_value;
static const lean_array_object l_main___closed__462_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__457_value),((lean_object*)&l_main___closed__459_value),((lean_object*)&l_main___closed__461_value)}};
static const lean_object* l_main___closed__462 = (const lean_object*)&l_main___closed__462_value;
static const lean_string_object l_main___closed__463_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_AccumulateCarriers"};
static const lean_object* l_main___closed__463 = (const lean_object*)&l_main___closed__463_value;
static const lean_ctor_object l_main___closed__464_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_object* l_main___closed__464 = (const lean_object*)&l_main___closed__464_value;
static const lean_array_object l_main___closed__465_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__464_value)}};
static const lean_object* l_main___closed__465 = (const lean_object*)&l_main___closed__465_value;
static const lean_string_object l_main___closed__466_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "array_inverse"};
static const lean_object* l_main___closed__466 = (const lean_object*)&l_main___closed__466_value;
static const lean_ctor_object l_main___closed__467_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__467_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__467_value_aux_0),((lean_object*)&l_main___closed__466_value),LEAN_SCALAR_PTR_LITERAL(116, 18, 4, 130, 54, 4, 74, 137)}};
static const lean_object* l_main___closed__467 = (const lean_object*)&l_main___closed__467_value;
static const lean_string_object l_main___closed__468_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "vector_inverse"};
static const lean_object* l_main___closed__468 = (const lean_object*)&l_main___closed__468_value;
static const lean_ctor_object l_main___closed__469_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__469_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__469_value_aux_0),((lean_object*)&l_main___closed__468_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 162, 49, 179, 145, 153, 129)}};
static const lean_object* l_main___closed__469 = (const lean_object*)&l_main___closed__469_value;
static const lean_string_object l_main___closed__470_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "point_roundtrip"};
static const lean_object* l_main___closed__470 = (const lean_object*)&l_main___closed__470_value;
static const lean_ctor_object l_main___closed__471_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__471_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__471_value_aux_0),((lean_object*)&l_main___closed__470_value),LEAN_SCALAR_PTR_LITERAL(156, 44, 95, 100, 26, 227, 248, 33)}};
static const lean_object* l_main___closed__471 = (const lean_object*)&l_main___closed__471_value;
static const lean_string_object l_main___closed__472_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "point_reverse"};
static const lean_object* l_main___closed__472 = (const lean_object*)&l_main___closed__472_value;
static const lean_ctor_object l_main___closed__473_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__473_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__473_value_aux_0),((lean_object*)&l_main___closed__472_value),LEAN_SCALAR_PTR_LITERAL(147, 0, 191, 151, 250, 168, 201, 203)}};
static const lean_object* l_main___closed__473 = (const lean_object*)&l_main___closed__473_value;
static const lean_string_object l_main___closed__474_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "prepared_roundtrip"};
static const lean_object* l_main___closed__474 = (const lean_object*)&l_main___closed__474_value;
static const lean_ctor_object l_main___closed__475_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__475_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__475_value_aux_0),((lean_object*)&l_main___closed__474_value),LEAN_SCALAR_PTR_LITERAL(108, 3, 93, 23, 40, 223, 201, 143)}};
static const lean_object* l_main___closed__475 = (const lean_object*)&l_main___closed__475_value;
static const lean_string_object l_main___closed__476_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "prepared_reverse"};
static const lean_object* l_main___closed__476 = (const lean_object*)&l_main___closed__476_value;
static const lean_ctor_object l_main___closed__477_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__477_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__477_value_aux_0),((lean_object*)&l_main___closed__476_value),LEAN_SCALAR_PTR_LITERAL(244, 161, 224, 53, 40, 133, 17, 91)}};
static const lean_object* l_main___closed__477 = (const lean_object*)&l_main___closed__477_value;
static const lean_string_object l_main___closed__478_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "accumulator_roundtrip"};
static const lean_object* l_main___closed__478 = (const lean_object*)&l_main___closed__478_value;
static const lean_ctor_object l_main___closed__479_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__479_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__479_value_aux_0),((lean_object*)&l_main___closed__478_value),LEAN_SCALAR_PTR_LITERAL(99, 188, 194, 12, 235, 54, 231, 243)}};
static const lean_object* l_main___closed__479 = (const lean_object*)&l_main___closed__479_value;
static const lean_string_object l_main___closed__480_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "accumulator_reverse"};
static const lean_object* l_main___closed__480 = (const lean_object*)&l_main___closed__480_value;
static const lean_ctor_object l_main___closed__481_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__481_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__481_value_aux_0),((lean_object*)&l_main___closed__480_value),LEAN_SCALAR_PTR_LITERAL(233, 93, 105, 102, 124, 88, 172, 21)}};
static const lean_object* l_main___closed__481 = (const lean_object*)&l_main___closed__481_value;
static const lean_string_object l_main___closed__482_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "q_roundtrip"};
static const lean_object* l_main___closed__482 = (const lean_object*)&l_main___closed__482_value;
static const lean_ctor_object l_main___closed__483_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__483_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__483_value_aux_0),((lean_object*)&l_main___closed__482_value),LEAN_SCALAR_PTR_LITERAL(28, 122, 124, 100, 70, 1, 123, 150)}};
static const lean_object* l_main___closed__483 = (const lean_object*)&l_main___closed__483_value;
static const lean_string_object l_main___closed__484_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "q_reverse"};
static const lean_object* l_main___closed__484 = (const lean_object*)&l_main___closed__484_value;
static const lean_ctor_object l_main___closed__485_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__485_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__485_value_aux_0),((lean_object*)&l_main___closed__484_value),LEAN_SCALAR_PTR_LITERAL(203, 219, 157, 74, 1, 154, 226, 99)}};
static const lean_object* l_main___closed__485 = (const lean_object*)&l_main___closed__485_value;
static const lean_string_object l_main___closed__486_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "e_roundtrip"};
static const lean_object* l_main___closed__486 = (const lean_object*)&l_main___closed__486_value;
static const lean_ctor_object l_main___closed__487_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__487_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__487_value_aux_0),((lean_object*)&l_main___closed__486_value),LEAN_SCALAR_PTR_LITERAL(85, 168, 88, 76, 152, 160, 40, 86)}};
static const lean_object* l_main___closed__487 = (const lean_object*)&l_main___closed__487_value;
static const lean_string_object l_main___closed__488_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "e_reverse"};
static const lean_object* l_main___closed__488 = (const lean_object*)&l_main___closed__488_value;
static const lean_ctor_object l_main___closed__489_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__489_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__489_value_aux_0),((lean_object*)&l_main___closed__488_value),LEAN_SCALAR_PTR_LITERAL(71, 132, 254, 11, 5, 157, 151, 188)}};
static const lean_object* l_main___closed__489 = (const lean_object*)&l_main___closed__489_value;
static const lean_string_object l_main___closed__490_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "weights_roundtrip"};
static const lean_object* l_main___closed__490 = (const lean_object*)&l_main___closed__490_value;
static const lean_ctor_object l_main___closed__491_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__491_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__491_value_aux_0),((lean_object*)&l_main___closed__490_value),LEAN_SCALAR_PTR_LITERAL(39, 65, 236, 205, 34, 139, 36, 42)}};
static const lean_object* l_main___closed__491 = (const lean_object*)&l_main___closed__491_value;
static const lean_string_object l_main___closed__492_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "weights_reverse"};
static const lean_object* l_main___closed__492 = (const lean_object*)&l_main___closed__492_value;
static const lean_ctor_object l_main___closed__493_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__493_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__493_value_aux_0),((lean_object*)&l_main___closed__492_value),LEAN_SCALAR_PTR_LITERAL(192, 184, 91, 14, 201, 45, 240, 101)}};
static const lean_object* l_main___closed__493 = (const lean_object*)&l_main___closed__493_value;
static const lean_array_object l_main___closed__494_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l_main___closed__467_value),((lean_object*)&l_main___closed__469_value),((lean_object*)&l_main___closed__471_value),((lean_object*)&l_main___closed__473_value),((lean_object*)&l_main___closed__475_value),((lean_object*)&l_main___closed__477_value),((lean_object*)&l_main___closed__479_value),((lean_object*)&l_main___closed__481_value),((lean_object*)&l_main___closed__483_value),((lean_object*)&l_main___closed__485_value),((lean_object*)&l_main___closed__487_value),((lean_object*)&l_main___closed__489_value),((lean_object*)&l_main___closed__491_value),((lean_object*)&l_main___closed__493_value)}};
static const lean_object* l_main___closed__494 = (const lean_object*)&l_main___closed__494_value;
static const lean_string_object l_main___closed__495_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_CodeFieldPacket"};
static const lean_object* l_main___closed__495 = (const lean_object*)&l_main___closed__495_value;
static const lean_ctor_object l_main___closed__496_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__495_value),LEAN_SCALAR_PTR_LITERAL(207, 133, 218, 246, 17, 125, 252, 232)}};
static const lean_object* l_main___closed__496 = (const lean_object*)&l_main___closed__496_value;
static const lean_array_object l_main___closed__497_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__496_value)}};
static const lean_object* l_main___closed__497 = (const lean_object*)&l_main___closed__497_value;
static const lean_string_object l_main___closed__498_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "extracted_root"};
static const lean_object* l_main___closed__498 = (const lean_object*)&l_main___closed__498_value;
static const lean_ctor_object l_main___closed__499_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__495_value),LEAN_SCALAR_PTR_LITERAL(207, 133, 218, 246, 17, 125, 252, 232)}};
static const lean_ctor_object l_main___closed__499_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__499_value_aux_0),((lean_object*)&l_main___closed__498_value),LEAN_SCALAR_PTR_LITERAL(106, 128, 200, 87, 18, 72, 183, 118)}};
static const lean_object* l_main___closed__499 = (const lean_object*)&l_main___closed__499_value;
static const lean_string_object l_main___closed__500_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_CodeFieldUse"};
static const lean_object* l_main___closed__500 = (const lean_object*)&l_main___closed__500_value;
static const lean_string_object l_main___closed__501_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "basis_call"};
static const lean_object* l_main___closed__501 = (const lean_object*)&l_main___closed__501_value;
static const lean_ctor_object l_main___closed__502_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__500_value),LEAN_SCALAR_PTR_LITERAL(134, 68, 239, 157, 216, 146, 3, 131)}};
static const lean_ctor_object l_main___closed__502_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__502_value_aux_0),((lean_object*)&l_main___closed__501_value),LEAN_SCALAR_PTR_LITERAL(141, 91, 210, 39, 196, 240, 180, 152)}};
static const lean_object* l_main___closed__502 = (const lean_object*)&l_main___closed__502_value;
static const lean_array_object l_main___closed__503_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__499_value),((lean_object*)&l_main___closed__502_value)}};
static const lean_object* l_main___closed__503 = (const lean_object*)&l_main___closed__503_value;
static const lean_ctor_object l_main___closed__504_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__500_value),LEAN_SCALAR_PTR_LITERAL(134, 68, 239, 157, 216, 146, 3, 131)}};
static const lean_object* l_main___closed__504 = (const lean_object*)&l_main___closed__504_value;
static const lean_array_object l_main___closed__505_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__504_value)}};
static const lean_object* l_main___closed__505 = (const lean_object*)&l_main___closed__505_value;
static const lean_array_object l_main___closed__506_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__502_value)}};
static const lean_object* l_main___closed__506 = (const lean_object*)&l_main___closed__506_value;
static const lean_string_object l_main___closed__507_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_CodeFieldBridge"};
static const lean_object* l_main___closed__507 = (const lean_object*)&l_main___closed__507_value;
static const lean_ctor_object l_main___closed__508_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_object* l_main___closed__508 = (const lean_object*)&l_main___closed__508_value;
static const lean_array_object l_main___closed__509_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__508_value)}};
static const lean_object* l_main___closed__509 = (const lean_object*)&l_main___closed__509_value;
static const lean_string_object l_main___closed__510_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "raw_roundtrip"};
static const lean_object* l_main___closed__510 = (const lean_object*)&l_main___closed__510_value;
static const lean_ctor_object l_main___closed__511_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__511_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__511_value_aux_0),((lean_object*)&l_main___closed__510_value),LEAN_SCALAR_PTR_LITERAL(60, 253, 249, 220, 217, 236, 38, 246)}};
static const lean_object* l_main___closed__511 = (const lean_object*)&l_main___closed__511_value;
static const lean_string_object l_main___closed__512_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stage_roundtrip"};
static const lean_object* l_main___closed__512 = (const lean_object*)&l_main___closed__512_value;
static const lean_ctor_object l_main___closed__513_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__513_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__513_value_aux_0),((lean_object*)&l_main___closed__512_value),LEAN_SCALAR_PTR_LITERAL(152, 12, 56, 67, 80, 225, 220, 25)}};
static const lean_object* l_main___closed__513 = (const lean_object*)&l_main___closed__513_value;
static const lean_string_object l_main___closed__514_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rem"};
static const lean_object* l_main___closed__514 = (const lean_object*)&l_main___closed__514_value;
static const lean_ctor_object l_main___closed__515_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__515_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__515_value_aux_0),((lean_object*)&l_main___closed__514_value),LEAN_SCALAR_PTR_LITERAL(241, 188, 77, 34, 32, 194, 245, 40)}};
static const lean_object* l_main___closed__515 = (const lean_object*)&l_main___closed__515_value;
static const lean_ctor_object l_main___closed__516_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__516_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__516_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(220, 0, 167, 28, 35, 101, 34, 57)}};
static const lean_object* l_main___closed__516 = (const lean_object*)&l_main___closed__516_value;
static const lean_ctor_object l_main___closed__517_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__517_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__517_value_aux_0),((lean_object*)&l_main___closed__200_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 89, 184, 18, 128, 138, 188)}};
static const lean_object* l_main___closed__517 = (const lean_object*)&l_main___closed__517_value;
static const lean_array_object l_main___closed__518_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l_main___closed__511_value),((lean_object*)&l_main___closed__513_value),((lean_object*)&l_main___closed__515_value),((lean_object*)&l_main___closed__516_value),((lean_object*)&l_main___closed__517_value)}};
static const lean_object* l_main___closed__518 = (const lean_object*)&l_main___closed__518_value;
static const lean_string_object l_main___closed__519_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_PrefixPacket"};
static const lean_object* l_main___closed__519 = (const lean_object*)&l_main___closed__519_value;
static const lean_ctor_object l_main___closed__520_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__519_value),LEAN_SCALAR_PTR_LITERAL(190, 35, 47, 34, 121, 137, 20, 202)}};
static const lean_object* l_main___closed__520 = (const lean_object*)&l_main___closed__520_value;
static const lean_array_object l_main___closed__521_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__520_value)}};
static const lean_object* l_main___closed__521 = (const lean_object*)&l_main___closed__521_value;
static const lean_ctor_object l_main___closed__522_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__519_value),LEAN_SCALAR_PTR_LITERAL(190, 35, 47, 34, 121, 137, 20, 202)}};
static const lean_ctor_object l_main___closed__522_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__522_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(40, 185, 223, 173, 239, 123, 175, 247)}};
static const lean_object* l_main___closed__522 = (const lean_object*)&l_main___closed__522_value;
static const lean_array_object l_main___closed__523_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__522_value)}};
static const lean_object* l_main___closed__523 = (const lean_object*)&l_main___closed__523_value;
static const lean_string_object l_main___closed__524_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_PrefixFinalAudit"};
static const lean_object* l_main___closed__524 = (const lean_object*)&l_main___closed__524_value;
static const lean_ctor_object l_main___closed__525_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__524_value),LEAN_SCALAR_PTR_LITERAL(147, 22, 159, 116, 125, 64, 167, 66)}};
static const lean_object* l_main___closed__525 = (const lean_object*)&l_main___closed__525_value;
static const lean_array_object l_main___closed__526_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__525_value)}};
static const lean_object* l_main___closed__526 = (const lean_object*)&l_main___closed__526_value;
static const lean_string_object l_main___closed__527_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_PrefixCallerDomain"};
static const lean_object* l_main___closed__527 = (const lean_object*)&l_main___closed__527_value;
static const lean_string_object l_main___closed__528_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "gathered"};
static const lean_object* l_main___closed__528 = (const lean_object*)&l_main___closed__528_value;
static const lean_ctor_object l_main___closed__529_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__527_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_ctor_object l_main___closed__529_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__529_value_aux_0),((lean_object*)&l_main___closed__528_value),LEAN_SCALAR_PTR_LITERAL(65, 20, 44, 251, 229, 16, 29, 168)}};
static const lean_object* l_main___closed__529 = (const lean_object*)&l_main___closed__529_value;
static const lean_string_object l_main___closed__530_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "capacities"};
static const lean_object* l_main___closed__530 = (const lean_object*)&l_main___closed__530_value;
static const lean_ctor_object l_main___closed__531_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__527_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_ctor_object l_main___closed__531_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__531_value_aux_0),((lean_object*)&l_main___closed__530_value),LEAN_SCALAR_PTR_LITERAL(242, 253, 42, 188, 73, 44, 131, 24)}};
static const lean_object* l_main___closed__531 = (const lean_object*)&l_main___closed__531_value;
static const lean_string_object l_main___closed__532_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrefixAssembly"};
static const lean_object* l_main___closed__532 = (const lean_object*)&l_main___closed__532_value;
static const lean_string_object l_main___closed__533_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "windows"};
static const lean_object* l_main___closed__533 = (const lean_object*)&l_main___closed__533_value;
static const lean_ctor_object l_main___closed__534_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__532_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_ctor_object l_main___closed__534_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__534_value_aux_0),((lean_object*)&l_main___closed__533_value),LEAN_SCALAR_PTR_LITERAL(153, 29, 140, 184, 94, 179, 171, 167)}};
static const lean_object* l_main___closed__534 = (const lean_object*)&l_main___closed__534_value;
static const lean_ctor_object l_main___closed__535_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__532_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_ctor_object l_main___closed__535_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__535_value_aux_0),((lean_object*)&l_main___closed__363_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 154, 103, 148, 35, 157, 103)}};
static const lean_object* l_main___closed__535 = (const lean_object*)&l_main___closed__535_value;
static const lean_string_object l_main___closed__536_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrefixCapacity"};
static const lean_object* l_main___closed__536 = (const lean_object*)&l_main___closed__536_value;
static const lean_string_object l_main___closed__537_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "representative"};
static const lean_object* l_main___closed__537 = (const lean_object*)&l_main___closed__537_value;
static const lean_ctor_object l_main___closed__538_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__536_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_ctor_object l_main___closed__538_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__538_value_aux_0),((lean_object*)&l_main___closed__537_value),LEAN_SCALAR_PTR_LITERAL(39, 20, 211, 119, 55, 242, 117, 241)}};
static const lean_object* l_main___closed__538 = (const lean_object*)&l_main___closed__538_value;
static const lean_string_object l_main___closed__539_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "partition"};
static const lean_object* l_main___closed__539 = (const lean_object*)&l_main___closed__539_value;
static const lean_ctor_object l_main___closed__540_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__536_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_ctor_object l_main___closed__540_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__540_value_aux_0),((lean_object*)&l_main___closed__539_value),LEAN_SCALAR_PTR_LITERAL(183, 174, 250, 94, 178, 96, 193, 200)}};
static const lean_object* l_main___closed__540 = (const lean_object*)&l_main___closed__540_value;
static const lean_string_object l_main___closed__541_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PrefixCalls"};
static const lean_object* l_main___closed__541 = (const lean_object*)&l_main___closed__541_value;
static const lean_string_object l_main___closed__542_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "m31_site"};
static const lean_object* l_main___closed__542 = (const lean_object*)&l_main___closed__542_value;
static const lean_ctor_object l_main___closed__543_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__543_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__543_value_aux_0),((lean_object*)&l_main___closed__542_value),LEAN_SCALAR_PTR_LITERAL(188, 87, 241, 76, 23, 156, 243, 140)}};
static const lean_object* l_main___closed__543 = (const lean_object*)&l_main___closed__543_value;
static const lean_string_object l_main___closed__544_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "member"};
static const lean_object* l_main___closed__544 = (const lean_object*)&l_main___closed__544_value;
static const lean_ctor_object l_main___closed__545_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__545_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__545_value_aux_0),((lean_object*)&l_main___closed__544_value),LEAN_SCALAR_PTR_LITERAL(230, 96, 109, 118, 155, 225, 9, 50)}};
static const lean_object* l_main___closed__545 = (const lean_object*)&l_main___closed__545_value;
static const lean_string_object l_main___closed__546_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_main___closed__546 = (const lean_object*)&l_main___closed__546_value;
static const lean_ctor_object l_main___closed__547_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__547_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__547_value_aux_0),((lean_object*)&l_main___closed__546_value),LEAN_SCALAR_PTR_LITERAL(53, 167, 82, 129, 250, 27, 30, 174)}};
static const lean_object* l_main___closed__547 = (const lean_object*)&l_main___closed__547_value;
static const lean_array_object l_main___closed__548_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l_main___closed__529_value),((lean_object*)&l_main___closed__531_value),((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__535_value),((lean_object*)&l_main___closed__538_value),((lean_object*)&l_main___closed__540_value),((lean_object*)&l_main___closed__543_value),((lean_object*)&l_main___closed__545_value),((lean_object*)&l_main___closed__547_value)}};
static const lean_object* l_main___closed__548 = (const lean_object*)&l_main___closed__548_value;
static const lean_ctor_object l_main___closed__549_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_object* l_main___closed__549 = (const lean_object*)&l_main___closed__549_value;
static const lean_array_object l_main___closed__550_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__549_value)}};
static const lean_object* l_main___closed__550 = (const lean_object*)&l_main___closed__550_value;
static const lean_array_object l_main___closed__551_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__543_value),((lean_object*)&l_main___closed__545_value),((lean_object*)&l_main___closed__547_value)}};
static const lean_object* l_main___closed__551 = (const lean_object*)&l_main___closed__551_value;
static const lean_string_object l_main___closed__552_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PrefixAudit"};
static const lean_object* l_main___closed__552 = (const lean_object*)&l_main___closed__552_value;
static const lean_ctor_object l_main___closed__553_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__552_value),LEAN_SCALAR_PTR_LITERAL(206, 122, 37, 162, 153, 117, 162, 16)}};
static const lean_object* l_main___closed__553 = (const lean_object*)&l_main___closed__553_value;
static const lean_array_object l_main___closed__554_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__553_value)}};
static const lean_object* l_main___closed__554 = (const lean_object*)&l_main___closed__554_value;
static const lean_array_object l_main___closed__555_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_main___closed__529_value),((lean_object*)&l_main___closed__531_value),((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__535_value),((lean_object*)&l_main___closed__538_value),((lean_object*)&l_main___closed__540_value)}};
static const lean_object* l_main___closed__555 = (const lean_object*)&l_main___closed__555_value;
static const lean_ctor_object l_main___closed__556_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__527_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_object* l_main___closed__556 = (const lean_object*)&l_main___closed__556_value;
static const lean_array_object l_main___closed__557_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__556_value)}};
static const lean_object* l_main___closed__557 = (const lean_object*)&l_main___closed__557_value;
static const lean_array_object l_main___closed__558_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__529_value),((lean_object*)&l_main___closed__531_value)}};
static const lean_object* l_main___closed__558 = (const lean_object*)&l_main___closed__558_value;
static const lean_ctor_object l_main___closed__559_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__536_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_object* l_main___closed__559 = (const lean_object*)&l_main___closed__559_value;
static const lean_array_object l_main___closed__560_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__559_value)}};
static const lean_object* l_main___closed__560 = (const lean_object*)&l_main___closed__560_value;
static const lean_array_object l_main___closed__561_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__538_value),((lean_object*)&l_main___closed__540_value)}};
static const lean_object* l_main___closed__561 = (const lean_object*)&l_main___closed__561_value;
static const lean_ctor_object l_main___closed__562_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__532_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_object* l_main___closed__562 = (const lean_object*)&l_main___closed__562_value;
static const lean_array_object l_main___closed__563_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__562_value)}};
static const lean_object* l_main___closed__563 = (const lean_object*)&l_main___closed__563_value;
static const lean_array_object l_main___closed__564_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__535_value)}};
static const lean_object* l_main___closed__564 = (const lean_object*)&l_main___closed__564_value;
static const lean_string_object l_main___closed__565_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__565 = (const lean_object*)&l_main___closed__565_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* l_main___boxed__const__3;
LEAN_EXPORT lean_object* l_main___boxed__const__4;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v___x_14_, lean_object* v___y_15_, lean_object* v_as_16_, size_t v_sz_17_, size_t v_i_18_, uint8_t v_b_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_snd_24_; uint8_t v___x_29_; lean_object* v_a_31_; 
v___x_29_ = lean_usize_dec_lt(v_i_18_, v_sz_17_);
if (v___x_29_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_box(v_b_19_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Command_getRef___redArg(v___y_20_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_47_, 1);
v___x_49_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_20_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_quotContext_x3f_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec_ref_known(v___x_49_, 1);
v_quotContext_x3f_50_ = lean_ctor_get(v___y_20_, 5);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_nat_dec_eq(v___x_14_, v___x_51_);
v_a_53_ = lean_array_uget_borrowed(v_as_16_, v_i_18_);
v___x_54_ = l_Lean_SourceInfo_fromRef(v_a_48_, v___x_52_);
lean_dec(v_a_48_);
if (lean_obj_tag(v_quotContext_x3f_50_) == 0)
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_21_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_dec_ref_known(v___x_74_, 1);
goto v___jp_55_;
}
else
{
lean_object* v_a_75_; 
lean_dec(v___x_54_);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v_a_31_ = v_a_75_;
goto v___jp_30_;
}
}
else
{
goto v___jp_55_;
}
v___jp_55_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_56_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4));
v___x_57_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5));
lean_inc_n(v___x_54_, 2);
v___x_58_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_54_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6));
v___x_60_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_54_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_inc(v_a_53_);
v___x_61_ = lean_mk_syntax_ident(v_a_53_);
v___x_62_ = l_Lean_Syntax_node3(v___x_54_, v___x_56_, v___x_58_, v___x_60_, v___x_61_);
v___x_63_ = l_Lean_Elab_Command_elabCommand(v___x_62_, v___y_20_, v___y_21_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec_ref_known(v___x_63_, 1);
v___x_64_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7));
v___x_65_ = lean_string_append(v___x_64_, v___y_15_);
v___x_66_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8));
v___x_67_ = lean_string_append(v___x_65_, v___x_66_);
lean_inc_n(v_a_53_, 2);
v___x_68_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_53_, v___x_29_);
v___x_69_ = lean_string_append(v___x_67_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = l_NEP_audit(v_a_53_, v___x_69_, v___y_20_, v___y_21_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v___x_71_; 
lean_dec_ref_known(v___x_70_, 1);
v___x_71_ = lean_box(v_b_19_);
v_snd_24_ = v___x_71_;
goto v___jp_23_;
}
else
{
lean_object* v_a_72_; 
v_a_72_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v___x_70_, 1);
v_a_31_ = v_a_72_;
goto v___jp_30_;
}
}
else
{
lean_object* v_a_73_; 
v_a_73_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_63_, 1);
v_a_31_ = v_a_73_;
goto v___jp_30_;
}
}
}
else
{
lean_object* v_a_76_; 
lean_dec(v_a_48_);
v_a_76_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_49_, 1);
v_a_31_ = v_a_76_;
goto v___jp_30_;
}
}
else
{
lean_object* v_a_77_; 
v_a_77_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_47_, 1);
v_a_31_ = v_a_77_;
goto v___jp_30_;
}
}
v___jp_23_:
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((size_t)1ULL);
v___x_26_ = lean_usize_add(v_i_18_, v___x_25_);
v___x_27_ = lean_unbox(v_snd_24_);
lean_dec(v_snd_24_);
v_i_18_ = v___x_26_;
v_b_19_ = v___x_27_;
goto _start;
}
v___jp_30_:
{
uint8_t v___x_32_; 
v___x_32_ = l_Lean_Exception_isInterrupt(v_a_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = l_Lean_Exception_toMessageData(v_a_31_);
v___x_34_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_33_, v___y_20_, v___y_21_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; 
lean_dec_ref_known(v___x_34_, 1);
v___x_35_ = lean_box(v___x_29_);
v_snd_24_ = v___x_35_;
goto v___jp_23_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v___x_44_; 
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v_a_31_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v___x_78_, lean_object* v___y_79_, lean_object* v_as_80_, lean_object* v_sz_81_, lean_object* v_i_82_, lean_object* v_b_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
size_t v_sz_boxed_87_; size_t v_i_boxed_88_; uint8_t v_b_boxed_89_; lean_object* v_res_90_; 
v_sz_boxed_87_ = lean_unbox_usize(v_sz_81_);
lean_dec(v_sz_81_);
v_i_boxed_88_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_b_boxed_89_ = lean_unbox(v_b_83_);
v_res_90_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_78_, v___y_79_, v_as_80_, v_sz_boxed_87_, v_i_boxed_88_, v_b_boxed_89_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec_ref(v_as_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___x_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(lean_object* v___x_91_, size_t v_sz_92_, size_t v_i_93_, lean_object* v_bs_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_usize_dec_lt(v_i_93_, v_sz_92_);
if (v___x_95_ == 0)
{
return v_bs_94_;
}
else
{
lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v_v_98_; lean_object* v_bs_x27_99_; lean_object* v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_dec_eq(v___x_91_, v___x_96_);
v_v_98_ = lean_array_uget(v_bs_94_, v_i_93_);
v_bs_x27_99_ = lean_array_uset(v_bs_94_, v_i_93_, v___x_96_);
v___x_100_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_100_, 0, v_v_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_95_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1 + 1, v___x_95_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1 + 2, v___x_97_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_93_, v___x_101_);
v___x_103_ = lean_array_uset(v_bs_x27_99_, v_i_93_, v___x_100_);
v_i_93_ = v___x_102_;
v_bs_94_ = v___x_103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v___x_105_, lean_object* v_sz_106_, lean_object* v_i_107_, lean_object* v_bs_108_){
_start:
{
size_t v_sz_boxed_109_; size_t v_i_boxed_110_; lean_object* v_res_111_; 
v_sz_boxed_109_ = lean_unbox_usize(v_sz_106_);
lean_dec(v_sz_106_);
v_i_boxed_110_ = lean_unbox_usize(v_i_107_);
lean_dec(v_i_107_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v___x_105_, v_sz_boxed_109_, v_i_boxed_110_, v_bs_108_);
lean_dec(v___x_105_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_as_x27_112_, lean_object* v_b_113_){
_start:
{
if (lean_obj_tag(v_as_x27_112_) == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v_b_113_);
return v___x_115_;
}
else
{
lean_object* v_head_116_; lean_object* v_tail_117_; lean_object* v_data_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_head_116_ = lean_ctor_get(v_as_x27_112_, 0);
v_tail_117_ = lean_ctor_get(v_as_x27_112_, 1);
v_data_118_ = lean_ctor_get(v_head_116_, 4);
lean_inc(v_data_118_);
v___x_119_ = l_Lean_MessageData_toString(v_data_118_);
v___x_120_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_119_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; 
lean_dec_ref_known(v___x_120_, 1);
v___x_121_ = lean_box(0);
v_as_x27_112_ = v_tail_117_;
v_b_113_ = v___x_121_;
goto _start;
}
else
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_as_x27_123_, lean_object* v_b_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_123_, v_b_124_);
lean_dec(v_as_x27_123_);
return v_res_126_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_main___closed__3));
v___x_133_ = l_Lean_FileMap_ofString(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_unsigned_to_nat(32u);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_134_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_137_ = ((size_t)5ULL);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_unsigned_to_nat(32u);
v___x_140_ = lean_mk_empty_array_with_capacity(v___x_139_);
v___x_141_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_142_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
lean_ctor_set(v___x_142_, 2, v___x_138_);
lean_ctor_set(v___x_142_, 3, v___x_138_);
lean_ctor_set_usize(v___x_142_, 4, v___x_137_);
return v___x_142_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_box(1);
v___x_144_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_ctor_set(v___x_145_, 2, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = 0;
v___x_1631_ = lean_box_uint32(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = 1;
v___x_1633_ = lean_box_uint32(v___x_1632_);
return v___x_1633_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = 2;
v___x_1635_ = lean_box_uint32(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_main___boxed__const__4(void){
_start:
{
uint32_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = 3;
v___x_1637_ = lean_box_uint32(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = l_NFA__MemoryLimit_set();
v___x_1641_ = ((lean_object*)(l_main___closed__0));
v___x_1642_ = l_Lean_findSysroot(v___x_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_initSearchPath(v_a_1643_, v___x_1644_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref_known(v___x_1645_, 1);
v___x_1646_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___y_1648_; lean_object* v_fst_1649_; lean_object* v_snd_1650_; lean_object* v___y_1753_; 
lean_dec_ref_known(v___x_1646_, 1);
if (lean_obj_tag(v_args_1638_) == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = ((lean_object*)(l_main___closed__565));
v___y_1753_ = v___x_1987_;
goto v___jp_1752_;
}
else
{
lean_object* v_head_1988_; 
v_head_1988_ = lean_ctor_get(v_args_1638_, 0);
lean_inc(v_head_1988_);
lean_dec_ref_known(v_args_1638_, 2);
v___y_1753_ = v_head_1988_;
goto v___jp_1752_;
}
v___jp_1647_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_array_get_size(v_fst_1649_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_nat_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
uint8_t v___x_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint32_t v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1654_ = 1;
v_sz_1655_ = lean_array_size(v_fst_1649_);
v___x_1656_ = ((size_t)0ULL);
lean_inc_ref(v_fst_1649_);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v___x_1651_, v_sz_1655_, v___x_1656_, v_fst_1649_);
v___x_1658_ = l_Lean_Options_empty;
v___x_1659_ = 0;
v___x_1660_ = ((lean_object*)(l_main___closed__1));
v___x_1661_ = 2;
v___x_1662_ = lean_box(1);
v___x_1663_ = l_Lean_importModules(v___x_1657_, v___x_1658_, v___x_1659_, v___x_1660_, v___x_1653_, v___x_1654_, v___x_1661_, v___x_1662_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; size_t v_sz_1674_; lean_object* v___x_1675_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = ((lean_object*)(l_main___closed__2));
v___x_1666_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1670_, 0, v___x_1665_);
lean_ctor_set(v___x_1670_, 1, v___x_1666_);
lean_ctor_set(v___x_1670_, 2, v___x_1652_);
lean_ctor_set(v___x_1670_, 3, v___x_1652_);
lean_ctor_set(v___x_1670_, 4, v___x_1644_);
lean_ctor_set(v___x_1670_, 5, v___x_1667_);
lean_ctor_set(v___x_1670_, 6, v___x_1668_);
lean_ctor_set(v___x_1670_, 7, v___x_1669_);
lean_ctor_set(v___x_1670_, 8, v___x_1667_);
lean_ctor_set(v___x_1670_, 9, v___x_1667_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*10, v___x_1653_);
v___x_1671_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_1672_ = l_Lean_Elab_Command_mkState(v_a_1664_, v___x_1671_, v___x_1658_);
v___x_1673_ = lean_st_mk_ref(v___x_1672_);
v_sz_1674_ = lean_array_size(v_snd_1650_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_1651_, v___y_1648_, v_snd_1650_, v_sz_1674_, v___x_1656_, v___x_1653_, v___x_1670_, v___x_1673_);
lean_dec_ref_known(v___x_1670_, 10);
lean_dec_ref(v___y_1648_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v_messages_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = lean_st_ref_get(v___x_1673_);
lean_dec(v___x_1673_);
v_messages_1678_ = lean_ctor_get(v___x_1677_, 1);
lean_inc_ref(v_messages_1678_);
lean_dec(v___x_1677_);
v___x_1679_ = l_Lean_MessageLog_toList(v_messages_1678_);
lean_dec_ref(v_messages_1678_);
v___x_1680_ = lean_box(0);
v___x_1681_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_1679_, v___x_1680_);
lean_dec(v___x_1679_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1681_, 0);
lean_dec(v_unused_1695_);
v___x_1683_ = v___x_1681_;
v_isShared_1684_ = v_isSharedCheck_1694_;
goto v_resetjp_1682_;
}
else
{
lean_dec(v___x_1681_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1694_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_main___boxed__const__1;
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_main___boxed__const__2;
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1690_);
v___x_1692_ = v___x_1683_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_a_1676_);
v_a_1696_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1681_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1681_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v___x_1673_);
v_a_1704_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1705_ = l_Lean_Exception_toMessageData(v_a_1704_);
v___x_1706_ = l_Lean_MessageData_toString(v___x_1705_);
v___x_1707_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1716_);
v___x_1709_ = v___x_1707_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v___x_1707_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = l_main___boxed__const__3;
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1707_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1707_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___y_1648_);
v_a_1725_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1663_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1663_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_dec_ref(v___y_1648_);
v___x_1733_ = ((lean_object*)(l_main___closed__8));
v___x_1734_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1743_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_main___boxed__const__4;
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_a_1744_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1734_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1734_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
v___jp_1752_:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_main___closed__9));
v___x_1755_ = lean_string_dec_eq(v___y_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = ((lean_object*)(l_main___closed__10));
v___x_1757_ = lean_string_dec_eq(v___y_1753_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = ((lean_object*)(l_main___closed__11));
v___x_1759_ = lean_string_dec_eq(v___y_1753_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_main___closed__12));
v___x_1761_ = lean_string_dec_eq(v___y_1753_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = ((lean_object*)(l_main___closed__13));
v___x_1763_ = lean_string_dec_eq(v___y_1753_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_main___closed__14));
v___x_1765_ = lean_string_dec_eq(v___y_1753_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_main___closed__15));
v___x_1767_ = lean_string_dec_eq(v___y_1753_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_main___closed__16));
v___x_1769_ = lean_string_dec_eq(v___y_1753_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_main___closed__17));
v___x_1771_ = lean_string_dec_eq(v___y_1753_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_main___closed__18));
v___x_1773_ = lean_string_dec_eq(v___y_1753_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_main___closed__19));
v___x_1775_ = lean_string_dec_eq(v___y_1753_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_main___closed__20));
v___x_1777_ = lean_string_dec_eq(v___y_1753_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_main___closed__21));
v___x_1779_ = lean_string_dec_eq(v___y_1753_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_main___closed__22));
v___x_1781_ = lean_string_dec_eq(v___y_1753_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_main___closed__23));
v___x_1783_ = lean_string_dec_eq(v___y_1753_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_main___closed__24));
v___x_1785_ = lean_string_dec_eq(v___y_1753_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_main___closed__25));
v___x_1787_ = lean_string_dec_eq(v___y_1753_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_main___closed__26));
v___x_1789_ = lean_string_dec_eq(v___y_1753_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_main___closed__27));
v___x_1791_ = lean_string_dec_eq(v___y_1753_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_main___closed__28));
v___x_1793_ = lean_string_dec_eq(v___y_1753_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_main___closed__29));
v___x_1795_ = lean_string_dec_eq(v___y_1753_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = ((lean_object*)(l_main___closed__30));
v___x_1797_ = lean_string_dec_eq(v___y_1753_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_main___closed__31));
v___x_1799_ = lean_string_dec_eq(v___y_1753_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_main___closed__32));
v___x_1801_ = lean_string_dec_eq(v___y_1753_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_main___closed__33));
v___x_1803_ = lean_string_dec_eq(v___y_1753_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_main___closed__34));
v___x_1805_ = lean_string_dec_eq(v___y_1753_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_main___closed__35));
v___x_1807_ = lean_string_dec_eq(v___y_1753_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_main___closed__36));
v___x_1809_ = lean_string_dec_eq(v___y_1753_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_main___closed__37));
v___x_1811_ = lean_string_dec_eq(v___y_1753_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_main___closed__38));
v___x_1813_ = lean_string_dec_eq(v___y_1753_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_main___closed__39));
v___x_1815_ = lean_string_dec_eq(v___y_1753_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_main___closed__40));
v___x_1817_ = lean_string_dec_eq(v___y_1753_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_main___closed__41));
v___x_1819_ = lean_string_dec_eq(v___y_1753_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_main___closed__42));
v___x_1821_ = lean_string_dec_eq(v___y_1753_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_main___closed__43));
v___x_1823_ = lean_string_dec_eq(v___y_1753_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_main___closed__44));
v___x_1825_ = lean_string_dec_eq(v___y_1753_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_main___closed__45));
v___x_1827_ = lean_string_dec_eq(v___y_1753_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = ((lean_object*)(l_main___closed__46));
v___x_1829_ = lean_string_dec_eq(v___y_1753_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_main___closed__47));
v___x_1831_ = lean_string_dec_eq(v___y_1753_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_main___closed__48));
v___x_1833_ = lean_string_dec_eq(v___y_1753_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_main___closed__49));
v___x_1835_ = lean_string_dec_eq(v___y_1753_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_main___closed__50));
v___x_1837_ = lean_string_dec_eq(v___y_1753_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_main___closed__51));
v___x_1839_ = lean_string_dec_eq(v___y_1753_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_main___closed__52));
v___x_1841_ = lean_string_dec_eq(v___y_1753_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_main___closed__53));
v___x_1843_ = lean_string_dec_eq(v___y_1753_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_main___closed__54));
v___x_1845_ = lean_string_dec_eq(v___y_1753_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_main___closed__55));
v___x_1847_ = lean_string_dec_eq(v___y_1753_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_main___closed__56));
v___x_1849_ = lean_string_dec_eq(v___y_1753_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_main___closed__57));
v___x_1851_ = lean_string_dec_eq(v___y_1753_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_main___closed__58));
v___x_1853_ = lean_string_dec_eq(v___y_1753_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_main___closed__59));
v___x_1855_ = lean_string_dec_eq(v___y_1753_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_main___closed__60));
v___x_1857_ = lean_string_dec_eq(v___y_1753_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_main___closed__61));
v___x_1859_ = lean_string_dec_eq(v___y_1753_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_main___closed__62));
v___x_1861_ = lean_string_dec_eq(v___y_1753_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_main___closed__63));
v___x_1863_ = lean_string_dec_eq(v___y_1753_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_main___closed__64));
v___x_1865_ = lean_string_dec_eq(v___y_1753_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_main___closed__65));
v___x_1867_ = lean_string_dec_eq(v___y_1753_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_main___closed__66));
v___x_1869_ = lean_string_dec_eq(v___y_1753_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = ((lean_object*)(l_main___closed__67));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1870_;
v_snd_1650_ = v___x_1870_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l_main___closed__70));
v___x_1872_ = ((lean_object*)(l_main___closed__73));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1871_;
v_snd_1650_ = v___x_1872_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_main___closed__70));
v___x_1874_ = ((lean_object*)(l_main___closed__76));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1873_;
v_snd_1650_ = v___x_1874_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_main___closed__70));
v___x_1876_ = ((lean_object*)(l_main___closed__79));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1875_;
v_snd_1650_ = v___x_1876_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_main___closed__82));
v___x_1878_ = ((lean_object*)(l_main___closed__87));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1877_;
v_snd_1650_ = v___x_1878_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = ((lean_object*)(l_main___closed__90));
v___x_1880_ = ((lean_object*)(l_main___closed__105));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1879_;
v_snd_1650_ = v___x_1880_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l_main___closed__108));
v___x_1882_ = ((lean_object*)(l_main___closed__115));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1881_;
v_snd_1650_ = v___x_1882_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_main___closed__118));
v___x_1884_ = ((lean_object*)(l_main___closed__125));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1883_;
v_snd_1650_ = v___x_1884_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_main___closed__128));
v___x_1886_ = ((lean_object*)(l_main___closed__132));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1885_;
v_snd_1650_ = v___x_1886_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((lean_object*)(l_main___closed__135));
v___x_1888_ = ((lean_object*)(l_main___closed__140));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1887_;
v_snd_1650_ = v___x_1888_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_main___closed__143));
v___x_1890_ = ((lean_object*)(l_main___closed__150));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1889_;
v_snd_1650_ = v___x_1890_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_main___closed__153));
v___x_1892_ = ((lean_object*)(l_main___closed__155));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1891_;
v_snd_1650_ = v___x_1892_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_main___closed__158));
v___x_1894_ = ((lean_object*)(l_main___closed__161));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1893_;
v_snd_1650_ = v___x_1894_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_main___closed__164));
v___x_1896_ = ((lean_object*)(l_main___closed__168));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1895_;
v_snd_1650_ = v___x_1896_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l_main___closed__171));
v___x_1898_ = ((lean_object*)(l_main___closed__174));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1897_;
v_snd_1650_ = v___x_1898_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_main___closed__70));
v___x_1900_ = ((lean_object*)(l_main___closed__175));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1899_;
v_snd_1650_ = v___x_1900_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l_main___closed__178));
v___x_1902_ = ((lean_object*)(l_main___closed__181));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1901_;
v_snd_1650_ = v___x_1902_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_main___closed__184));
v___x_1904_ = ((lean_object*)(l_main___closed__186));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1903_;
v_snd_1650_ = v___x_1904_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_main___closed__189));
v___x_1906_ = ((lean_object*)(l_main___closed__194));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1905_;
v_snd_1650_ = v___x_1906_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_main___closed__197));
v___x_1908_ = ((lean_object*)(l_main___closed__202));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1907_;
v_snd_1650_ = v___x_1908_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_main___closed__205));
v___x_1910_ = ((lean_object*)(l_main___closed__218));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1909_;
v_snd_1650_ = v___x_1910_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_main___closed__221));
v___x_1912_ = ((lean_object*)(l_main___closed__230));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1911_;
v_snd_1650_ = v___x_1912_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_main___closed__233));
v___x_1914_ = ((lean_object*)(l_main___closed__236));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1913_;
v_snd_1650_ = v___x_1914_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = ((lean_object*)(l_main___closed__239));
v___x_1916_ = ((lean_object*)(l_main___closed__245));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1915_;
v_snd_1650_ = v___x_1916_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = ((lean_object*)(l_main___closed__248));
v___x_1918_ = ((lean_object*)(l_main___closed__251));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1917_;
v_snd_1650_ = v___x_1918_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l_main___closed__254));
v___x_1920_ = ((lean_object*)(l_main___closed__258));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1919_;
v_snd_1650_ = v___x_1920_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_main___closed__261));
v___x_1922_ = ((lean_object*)(l_main___closed__265));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1921_;
v_snd_1650_ = v___x_1922_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_main___closed__268));
v___x_1924_ = ((lean_object*)(l_main___closed__275));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1923_;
v_snd_1650_ = v___x_1924_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l_main___closed__278));
v___x_1926_ = ((lean_object*)(l_main___closed__280));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1925_;
v_snd_1650_ = v___x_1926_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l_main___closed__283));
v___x_1928_ = ((lean_object*)(l_main___closed__288));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1927_;
v_snd_1650_ = v___x_1928_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l_main___closed__291));
v___x_1930_ = ((lean_object*)(l_main___closed__297));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1929_;
v_snd_1650_ = v___x_1930_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_main___closed__300));
v___x_1932_ = ((lean_object*)(l_main___closed__303));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1931_;
v_snd_1650_ = v___x_1932_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_main___closed__306));
v___x_1934_ = ((lean_object*)(l_main___closed__320));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1933_;
v_snd_1650_ = v___x_1934_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_main___closed__323));
v___x_1936_ = ((lean_object*)(l_main___closed__329));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1935_;
v_snd_1650_ = v___x_1936_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_main___closed__332));
v___x_1938_ = ((lean_object*)(l_main___closed__347));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1937_;
v_snd_1650_ = v___x_1938_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_main___closed__350));
v___x_1940_ = ((lean_object*)(l_main___closed__354));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1939_;
v_snd_1650_ = v___x_1940_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_main___closed__357));
v___x_1942_ = ((lean_object*)(l_main___closed__359));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1941_;
v_snd_1650_ = v___x_1942_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_main___closed__362));
v___x_1944_ = ((lean_object*)(l_main___closed__367));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1943_;
v_snd_1650_ = v___x_1944_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_main___closed__370));
v___x_1946_ = ((lean_object*)(l_main___closed__375));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1945_;
v_snd_1650_ = v___x_1946_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_main___closed__378));
v___x_1948_ = ((lean_object*)(l_main___closed__383));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1947_;
v_snd_1650_ = v___x_1948_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_main___closed__386));
v___x_1950_ = ((lean_object*)(l_main___closed__393));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1949_;
v_snd_1650_ = v___x_1950_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_main___closed__396));
v___x_1952_ = ((lean_object*)(l_main___closed__401));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1951_;
v_snd_1650_ = v___x_1952_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l_main___closed__404));
v___x_1954_ = ((lean_object*)(l_main___closed__406));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1953_;
v_snd_1650_ = v___x_1954_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l_main___closed__409));
v___x_1956_ = ((lean_object*)(l_main___closed__414));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1955_;
v_snd_1650_ = v___x_1956_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_main___closed__417));
v___x_1958_ = ((lean_object*)(l_main___closed__420));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1957_;
v_snd_1650_ = v___x_1958_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_main___closed__423));
v___x_1960_ = ((lean_object*)(l_main___closed__442));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1959_;
v_snd_1650_ = v___x_1960_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_main___closed__445));
v___x_1962_ = ((lean_object*)(l_main___closed__452));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1961_;
v_snd_1650_ = v___x_1962_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_main___closed__455));
v___x_1964_ = ((lean_object*)(l_main___closed__462));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1963_;
v_snd_1650_ = v___x_1964_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_main___closed__465));
v___x_1966_ = ((lean_object*)(l_main___closed__494));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1965_;
v_snd_1650_ = v___x_1966_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_main___closed__497));
v___x_1968_ = ((lean_object*)(l_main___closed__503));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1967_;
v_snd_1650_ = v___x_1968_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_main___closed__505));
v___x_1970_ = ((lean_object*)(l_main___closed__506));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1969_;
v_snd_1650_ = v___x_1970_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_main___closed__509));
v___x_1972_ = ((lean_object*)(l_main___closed__518));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1971_;
v_snd_1650_ = v___x_1972_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_main___closed__521));
v___x_1974_ = ((lean_object*)(l_main___closed__523));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1973_;
v_snd_1650_ = v___x_1974_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_main___closed__526));
v___x_1976_ = ((lean_object*)(l_main___closed__548));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1975_;
v_snd_1650_ = v___x_1976_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_main___closed__550));
v___x_1978_ = ((lean_object*)(l_main___closed__551));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1977_;
v_snd_1650_ = v___x_1978_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_main___closed__554));
v___x_1980_ = ((lean_object*)(l_main___closed__555));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1979_;
v_snd_1650_ = v___x_1980_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_main___closed__557));
v___x_1982_ = ((lean_object*)(l_main___closed__558));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1981_;
v_snd_1650_ = v___x_1982_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l_main___closed__560));
v___x_1984_ = ((lean_object*)(l_main___closed__561));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1983_;
v_snd_1650_ = v___x_1984_;
goto v___jp_1647_;
}
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_main___closed__563));
v___x_1986_ = ((lean_object*)(l_main___closed__564));
v___y_1648_ = v___y_1753_;
v_fst_1649_ = v___x_1985_;
v_snd_1650_ = v___x_1986_;
goto v___jp_1647_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_args_1638_);
v_a_1989_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1646_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1646_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_args_1638_);
v_a_1997_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1645_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1645_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_args_1638_);
v_a_2005_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1642_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1642_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = _lean_main(v_args_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_2016_, lean_object* v_as_x27_2017_, lean_object* v_b_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_2017_, v_b_2018_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_2022_, lean_object* v_as_x27_2023_, lean_object* v_b_2024_, lean_object* v_a_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_2022_, v_as_x27_2023_, v_b_2024_, v_a_2025_);
lean_dec(v_as_x27_2023_);
lean_dec(v_as_2022_);
return v_res_2027_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFA__Driver(uint8_t builtin) {
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
res = initialize_NFA__MemoryLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NFA__WALKER(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
l_main___boxed__const__3 = _init_l_main___boxed__const__3();
lean_mark_persistent(l_main___boxed__const__3);
l_main___boxed__const__4 = _init_l_main___boxed__const__4();
lean_mark_persistent(l_main___boxed__const__4);
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
  res = initialize_NFA__Driver(1 /* builtin */);
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
