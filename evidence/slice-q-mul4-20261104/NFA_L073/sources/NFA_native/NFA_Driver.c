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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_array_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEP_Driver"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static lean_once_cell_t l_main___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__3;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static lean_once_cell_t l_main___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__5;
static lean_once_cell_t l_main___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__6;
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Unknown NFA audit mode"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "4"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "5"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "6"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "7"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "8"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "9"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "10"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "11"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "12"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "13"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "14"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "15"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "16"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "17"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "18"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "19"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "20"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "21"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "22"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "23"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "24"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "25"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "26"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "27"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "28"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_string_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "29"};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "30"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_string_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "31"};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "32"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_string_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "33"};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "34"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_string_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "35"};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "36"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_string_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "37"};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "38"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "39"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_string_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "40"};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "41"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_string_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "42"};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "43"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_string_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "44"};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_string_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "45"};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "46"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_string_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "47"};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "48"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_string_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "49"};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_string_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "50"};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "51"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "52"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_string_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "53"};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "54"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "55"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "56"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_string_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "57"};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_array_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_string_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotResult"};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_ctor_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_array_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__68_value)}};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_string_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "result_state_effects"};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_ctor_object l_main___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__71_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(255, 171, 112, 111, 120, 231, 138, 95)}};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_array_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__71_value)}};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_string_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_ctor_object l_main___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__74_value_aux_0),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(195, 240, 240, 108, 178, 127, 156, 191)}};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_array_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__74_value)}};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_string_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "inner"};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_ctor_object l_main___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(117, 91, 8, 189, 93, 206, 87, 148)}};
static const lean_ctor_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__77_value_aux_0),((lean_object*)&l_main___closed__76_value),LEAN_SCALAR_PTR_LITERAL(161, 170, 171, 99, 193, 166, 197, 59)}};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_array_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__77_value)}};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_string_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NEV_FourResult"};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_ctor_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_array_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__80_value)}};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_ctor_object l_main___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_0),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(151, 203, 215, 138, 71, 20, 48, 159)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_ctor_object l_main___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__83_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(123, 104, 208, 19, 220, 163, 239, 112)}};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_string_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "calls"};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_ctor_object l_main___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(249, 156, 221, 124, 41, 7, 72, 122)}};
static const lean_ctor_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__85_value_aux_0),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(193, 207, 189, 100, 203, 16, 185, 164)}};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_array_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__82_value),((lean_object*)&l_main___closed__83_value),((lean_object*)&l_main___closed__85_value)}};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_string_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_DotSchedule"};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_ctor_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_array_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__88_value)}};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_string_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_ctor_object l_main___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__91_value_aux_0),((lean_object*)&l_main___closed__90_value),LEAN_SCALAR_PTR_LITERAL(240, 211, 148, 244, 207, 192, 41, 128)}};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_string_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reached"};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_ctor_object l_main___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__93_value_aux_0),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(70, 94, 174, 195, 203, 213, 144, 3)}};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_string_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unique_block"};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_ctor_object l_main___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__95_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(86, 132, 221, 90, 64, 246, 63, 124)}};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_string_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "remaining"};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_ctor_object l_main___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_0),((lean_object*)&l_main___closed__96_value),LEAN_SCALAR_PTR_LITERAL(170, 9, 154, 167, 238, 10, 71, 17)}};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_string_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "adjacent"};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_ctor_object l_main___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__99_value_aux_0),((lean_object*)&l_main___closed__98_value),LEAN_SCALAR_PTR_LITERAL(229, 63, 141, 233, 164, 171, 60, 134)}};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_string_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "advance_mathematics"};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_ctor_object l_main___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__101_value_aux_0),((lean_object*)&l_main___closed__100_value),LEAN_SCALAR_PTR_LITERAL(148, 241, 222, 46, 68, 213, 221, 236)}};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "finished"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_ctor_object l_main___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(148, 132, 63, 139, 141, 87, 107, 54)}};
static const lean_ctor_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 29, 113, 210, 204, 137, 166)}};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_array_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__91_value),((lean_object*)&l_main___closed__93_value),((lean_object*)&l_main___closed__95_value),((lean_object*)&l_main___closed__97_value),((lean_object*)&l_main___closed__99_value),((lean_object*)&l_main___closed__101_value),((lean_object*)&l_main___closed__103_value)}};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_string_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_DotEightTotal"};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_ctor_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_array_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__106_value)}};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_string_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "eight"};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_ctor_object l_main___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__109_value_aux_0),((lean_object*)&l_main___closed__108_value),LEAN_SCALAR_PTR_LITERAL(90, 236, 255, 136, 0, 51, 66, 247)}};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(143, 85, 213, 68, 34, 10, 56, 130)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_ctor_object l_main___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(175, 17, 206, 173, 128, 139, 46, 126)}};
static const lean_ctor_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__113_value_aux_0),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(230, 53, 58, 48, 123, 160, 9, 205)}};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_array_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__109_value),((lean_object*)&l_main___closed__111_value),((lean_object*)&l_main___closed__113_value)}};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_string_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotInputs"};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_ctor_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_array_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__116_value)}};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "selected"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_ctor_object l_main___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_0),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(106, 252, 122, 59, 66, 92, 86, 52)}};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_string_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "limbs"};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_ctor_object l_main___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_0),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(237, 127, 116, 172, 196, 61, 112, 98)}};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_string_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tail_index"};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_ctor_object l_main___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(84, 171, 73, 176, 107, 85, 35, 54)}};
static const lean_ctor_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__123_value_aux_0),((lean_object*)&l_main___closed__122_value),LEAN_SCALAR_PTR_LITERAL(248, 177, 197, 79, 199, 100, 61, 119)}};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_array_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__119_value),((lean_object*)&l_main___closed__121_value),((lean_object*)&l_main___closed__123_value)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_DotReadDomain"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_ctor_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_array_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__126_value)}};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_string_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_ctor_object l_main___closed__129_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_ctor_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__129_value_aux_0),((lean_object*)&l_main___closed__128_value),LEAN_SCALAR_PTR_LITERAL(29, 4, 124, 132, 240, 221, 12, 207)}};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_ctor_object l_main___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(106, 189, 231, 132, 237, 216, 54, 137)}};
static const lean_ctor_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_0),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(144, 12, 99, 54, 96, 127, 86, 153)}};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_array_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__129_value),((lean_object*)&l_main___closed__130_value)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_string_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_DotSweepStep"};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_ctor_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_array_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__133_value)}};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_string_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_ctor_object l_main___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_ctor_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__136_value_aux_0),((lean_object*)&l_main___closed__135_value),LEAN_SCALAR_PTR_LITERAL(174, 234, 216, 181, 233, 82, 134, 235)}};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_string_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "next_term"};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_ctor_object l_main___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(78, 68, 254, 194, 41, 170, 37, 243)}};
static const lean_ctor_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__138_value_aux_0),((lean_object*)&l_main___closed__137_value),LEAN_SCALAR_PTR_LITERAL(21, 163, 171, 29, 11, 228, 207, 27)}};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_array_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__136_value),((lean_object*)&l_main___closed__138_value)}};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_string_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_DotSweep"};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_ctor_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__140_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_array_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__141_value)}};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_string_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "write"};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_ctor_object l_main___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__140_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_0),((lean_object*)&l_main___closed__143_value),LEAN_SCALAR_PTR_LITERAL(193, 3, 185, 49, 2, 13, 7, 119)}};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_string_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "current"};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_ctor_object l_main___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__140_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_0),((lean_object*)&l_main___closed__145_value),LEAN_SCALAR_PTR_LITERAL(209, 91, 27, 114, 109, 124, 152, 109)}};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_string_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "native_domain"};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_ctor_object l_main___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__140_value),LEAN_SCALAR_PTR_LITERAL(175, 50, 238, 149, 154, 205, 199, 219)}};
static const lean_ctor_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_0),((lean_object*)&l_main___closed__147_value),LEAN_SCALAR_PTR_LITERAL(174, 135, 218, 80, 92, 132, 48, 146)}};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_array_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__144_value),((lean_object*)&l_main___closed__146_value),((lean_object*)&l_main___closed__148_value)}};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_string_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_DotEight"};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_ctor_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(34, 249, 36, 212, 240, 45, 165, 138)}};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_array_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__151_value)}};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_ctor_object l_main___closed__153_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(34, 249, 36, 212, 240, 45, 165, 138)}};
static const lean_ctor_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__153_value_aux_0),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(255, 233, 242, 139, 40, 197, 114, 85)}};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_array_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__153_value)}};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_string_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_DotCell"};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_ctor_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__155_value),LEAN_SCALAR_PTR_LITERAL(198, 50, 110, 209, 126, 234, 105, 249)}};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_array_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__156_value)}};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_string_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "total"};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_ctor_object l_main___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__155_value),LEAN_SCALAR_PTR_LITERAL(198, 50, 110, 209, 126, 234, 105, 249)}};
static const lean_ctor_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__159_value_aux_0),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(248, 233, 237, 73, 250, 64, 147, 227)}};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_array_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__159_value)}};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_string_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_ActualDotStep"};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_ctor_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(78, 134, 44, 53, 228, 48, 171, 153)}};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_array_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__162_value)}};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_string_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_string_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_ctor_object l_main___closed__166_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__164_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__166_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_0),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(115, 165, 125, 248, 87, 69, 218, 154)}};
static const lean_ctor_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_1),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(134, 18, 18, 238, 31, 172, 208, 61)}};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_array_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__166_value)}};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_string_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_DotFoldInvariant"};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_ctor_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__168_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_array_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__169_value)}};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_ctor_object l_main___closed__171_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__168_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_ctor_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__171_value_aux_0),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(167, 235, 53, 90, 114, 46, 26, 133)}};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_ctor_object l_main___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__168_value),LEAN_SCALAR_PTR_LITERAL(149, 143, 39, 110, 192, 241, 240, 211)}};
static const lean_ctor_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__172_value_aux_0),((lean_object*)&l_main___closed__147_value),LEAN_SCALAR_PTR_LITERAL(60, 124, 136, 250, 102, 13, 219, 200)}};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_array_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__171_value),((lean_object*)&l_main___closed__172_value)}};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_array_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__77_value),((lean_object*)&l_main___closed__74_value),((lean_object*)&l_main___closed__71_value)}};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_string_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_DotScalar"};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_ctor_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__175_value),LEAN_SCALAR_PTR_LITERAL(49, 33, 255, 251, 16, 115, 6, 25)}};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_array_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__176_value)}};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_string_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "product"};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_ctor_object l_main___closed__179_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__175_value),LEAN_SCALAR_PTR_LITERAL(49, 33, 255, 251, 16, 115, 6, 25)}};
static const lean_ctor_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__179_value_aux_0),((lean_object*)&l_main___closed__178_value),LEAN_SCALAR_PTR_LITERAL(239, 160, 141, 159, 250, 145, 86, 23)}};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_array_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__179_value)}};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_string_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_EbyPushAssociation"};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_ctor_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(30, 121, 204, 152, 27, 46, 80, 75)}};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_array_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__182_value)}};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_ctor_object l_main___closed__184_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(30, 121, 204, 152, 27, 46, 80, 75)}};
static const lean_ctor_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__184_value_aux_0),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(204, 94, 158, 106, 141, 162, 238, 119)}};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_array_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__184_value)}};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_string_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_DotPush"};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_ctor_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__186_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_array_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__187_value)}};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_string_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "association"};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_ctor_object l_main___closed__190_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__186_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_ctor_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(193, 86, 50, 168, 85, 47, 249, 190)}};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_string_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_ctor_object l_main___closed__192_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__186_value),LEAN_SCALAR_PTR_LITERAL(180, 44, 104, 22, 42, 135, 189, 109)}};
static const lean_ctor_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__192_value_aux_0),((lean_object*)&l_main___closed__191_value),LEAN_SCALAR_PTR_LITERAL(87, 15, 102, 122, 72, 12, 223, 26)}};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_array_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__190_value),((lean_object*)&l_main___closed__192_value)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_string_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_QRawAssociation"};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_ctor_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_array_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__195_value)}};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_string_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "actual"};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_ctor_object l_main___closed__198_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_ctor_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__198_value_aux_0),((lean_object*)&l_main___closed__197_value),LEAN_SCALAR_PTR_LITERAL(179, 5, 253, 32, 231, 1, 89, 102)}};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_string_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cohort"};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_ctor_object l_main___closed__200_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(17, 238, 138, 47, 184, 204, 153, 58)}};
static const lean_ctor_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__200_value_aux_0),((lean_object*)&l_main___closed__199_value),LEAN_SCALAR_PTR_LITERAL(240, 34, 160, 133, 250, 56, 210, 57)}};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_array_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__198_value),((lean_object*)&l_main___closed__200_value)}};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_string_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_QRawAtoms"};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_ctor_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_array_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__203_value)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_string_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modulus"};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
static const lean_ctor_object l_main___closed__206_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__206_value_aux_0),((lean_object*)&l_main___closed__205_value),LEAN_SCALAR_PTR_LITERAL(174, 16, 221, 13, 146, 231, 77, 42)}};
static const lean_object* l_main___closed__206 = (const lean_object*)&l_main___closed__206_value;
static const lean_string_object l_main___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_main___closed__207 = (const lean_object*)&l_main___closed__207_value;
static const lean_ctor_object l_main___closed__208_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__208_value_aux_0),((lean_object*)&l_main___closed__207_value),LEAN_SCALAR_PTR_LITERAL(95, 65, 42, 159, 4, 54, 90, 46)}};
static const lean_object* l_main___closed__208 = (const lean_object*)&l_main___closed__208_value;
static const lean_string_object l_main___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read0"};
static const lean_object* l_main___closed__209 = (const lean_object*)&l_main___closed__209_value;
static const lean_ctor_object l_main___closed__210_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__210_value_aux_0),((lean_object*)&l_main___closed__209_value),LEAN_SCALAR_PTR_LITERAL(150, 4, 241, 117, 134, 207, 214, 102)}};
static const lean_object* l_main___closed__210 = (const lean_object*)&l_main___closed__210_value;
static const lean_string_object l_main___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read1"};
static const lean_object* l_main___closed__211 = (const lean_object*)&l_main___closed__211_value;
static const lean_ctor_object l_main___closed__212_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__212_value_aux_0),((lean_object*)&l_main___closed__211_value),LEAN_SCALAR_PTR_LITERAL(197, 204, 220, 97, 122, 205, 145, 204)}};
static const lean_object* l_main___closed__212 = (const lean_object*)&l_main___closed__212_value;
static const lean_string_object l_main___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read2"};
static const lean_object* l_main___closed__213 = (const lean_object*)&l_main___closed__213_value;
static const lean_ctor_object l_main___closed__214_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__214_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(253, 73, 17, 189, 160, 146, 133, 106)}};
static const lean_object* l_main___closed__214 = (const lean_object*)&l_main___closed__214_value;
static const lean_string_object l_main___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "read3"};
static const lean_object* l_main___closed__215 = (const lean_object*)&l_main___closed__215_value;
static const lean_ctor_object l_main___closed__216_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(77, 35, 165, 126, 214, 6, 194, 114)}};
static const lean_ctor_object l_main___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__216_value_aux_0),((lean_object*)&l_main___closed__215_value),LEAN_SCALAR_PTR_LITERAL(249, 74, 221, 181, 143, 183, 149, 18)}};
static const lean_object* l_main___closed__216 = (const lean_object*)&l_main___closed__216_value;
static const lean_array_object l_main___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_main___closed__206_value),((lean_object*)&l_main___closed__208_value),((lean_object*)&l_main___closed__210_value),((lean_object*)&l_main___closed__212_value),((lean_object*)&l_main___closed__214_value),((lean_object*)&l_main___closed__216_value)}};
static const lean_object* l_main___closed__217 = (const lean_object*)&l_main___closed__217_value;
static const lean_string_object l_main___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_QRawMaps"};
static const lean_object* l_main___closed__218 = (const lean_object*)&l_main___closed__218_value;
static const lean_ctor_object l_main___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_object* l_main___closed__219 = (const lean_object*)&l_main___closed__219_value;
static const lean_array_object l_main___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__219_value)}};
static const lean_object* l_main___closed__220 = (const lean_object*)&l_main___closed__220_value;
static const lean_string_object l_main___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_main___closed__221 = (const lean_object*)&l_main___closed__221_value;
static const lean_ctor_object l_main___closed__222_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__222_value_aux_0),((lean_object*)&l_main___closed__221_value),LEAN_SCALAR_PTR_LITERAL(28, 131, 142, 180, 105, 66, 202, 67)}};
static const lean_object* l_main___closed__222 = (const lean_object*)&l_main___closed__222_value;
static const lean_string_object l_main___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_main___closed__223 = (const lean_object*)&l_main___closed__223_value;
static const lean_ctor_object l_main___closed__224_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_0),((lean_object*)&l_main___closed__223_value),LEAN_SCALAR_PTR_LITERAL(194, 7, 196, 18, 12, 252, 237, 93)}};
static const lean_object* l_main___closed__224 = (const lean_object*)&l_main___closed__224_value;
static const lean_string_object l_main___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shift"};
static const lean_object* l_main___closed__225 = (const lean_object*)&l_main___closed__225_value;
static const lean_ctor_object l_main___closed__226_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__226_value_aux_0),((lean_object*)&l_main___closed__225_value),LEAN_SCALAR_PTR_LITERAL(121, 104, 117, 205, 249, 145, 35, 21)}};
static const lean_object* l_main___closed__226 = (const lean_object*)&l_main___closed__226_value;
static const lean_string_object l_main___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fold"};
static const lean_object* l_main___closed__227 = (const lean_object*)&l_main___closed__227_value;
static const lean_ctor_object l_main___closed__228_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(65, 27, 30, 179, 64, 164, 19, 217)}};
static const lean_ctor_object l_main___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_0),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(230, 77, 241, 242, 133, 228, 96, 129)}};
static const lean_object* l_main___closed__228 = (const lean_object*)&l_main___closed__228_value;
static const lean_array_object l_main___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__222_value),((lean_object*)&l_main___closed__224_value),((lean_object*)&l_main___closed__226_value),((lean_object*)&l_main___closed__228_value)}};
static const lean_object* l_main___closed__229 = (const lean_object*)&l_main___closed__229_value;
static const lean_string_object l_main___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_ReachedProgress"};
static const lean_object* l_main___closed__230 = (const lean_object*)&l_main___closed__230_value;
static const lean_ctor_object l_main___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__230_value),LEAN_SCALAR_PTR_LITERAL(11, 92, 122, 162, 60, 194, 185, 166)}};
static const lean_object* l_main___closed__231 = (const lean_object*)&l_main___closed__231_value;
static const lean_array_object l_main___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__231_value)}};
static const lean_object* l_main___closed__232 = (const lean_object*)&l_main___closed__232_value;
static const lean_string_object l_main___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_main___closed__233 = (const lean_object*)&l_main___closed__233_value;
static const lean_ctor_object l_main___closed__234_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__230_value),LEAN_SCALAR_PTR_LITERAL(11, 92, 122, 162, 60, 194, 185, 166)}};
static const lean_ctor_object l_main___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__234_value_aux_0),((lean_object*)&l_main___closed__233_value),LEAN_SCALAR_PTR_LITERAL(17, 77, 46, 99, 160, 246, 61, 74)}};
static const lean_object* l_main___closed__234 = (const lean_object*)&l_main___closed__234_value;
static const lean_array_object l_main___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__234_value)}};
static const lean_object* l_main___closed__235 = (const lean_object*)&l_main___closed__235_value;
static const lean_string_object l_main___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_AccumPacket"};
static const lean_object* l_main___closed__236 = (const lean_object*)&l_main___closed__236_value;
static const lean_ctor_object l_main___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_object* l_main___closed__237 = (const lean_object*)&l_main___closed__237_value;
static const lean_array_object l_main___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__237_value)}};
static const lean_object* l_main___closed__238 = (const lean_object*)&l_main___closed__238_value;
static const lean_string_object l_main___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "raw_length"};
static const lean_object* l_main___closed__239 = (const lean_object*)&l_main___closed__239_value;
static const lean_ctor_object l_main___closed__240_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__240_value_aux_0),((lean_object*)&l_main___closed__239_value),LEAN_SCALAR_PTR_LITERAL(133, 229, 162, 188, 47, 80, 38, 123)}};
static const lean_object* l_main___closed__240 = (const lean_object*)&l_main___closed__240_value;
static const lean_ctor_object l_main___closed__241_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__241_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(139, 171, 207, 144, 75, 124, 175, 142)}};
static const lean_object* l_main___closed__241 = (const lean_object*)&l_main___closed__241_value;
static const lean_string_object l_main___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "no_base_dependency"};
static const lean_object* l_main___closed__242 = (const lean_object*)&l_main___closed__242_value;
static const lean_ctor_object l_main___closed__243_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 108, 93, 174, 217, 115, 153)}};
static const lean_ctor_object l_main___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__243_value_aux_0),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(0, 21, 157, 234, 11, 239, 213, 163)}};
static const lean_object* l_main___closed__243 = (const lean_object*)&l_main___closed__243_value;
static const lean_array_object l_main___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__240_value),((lean_object*)&l_main___closed__241_value),((lean_object*)&l_main___closed__243_value)}};
static const lean_object* l_main___closed__244 = (const lean_object*)&l_main___closed__244_value;
static const lean_string_object l_main___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_WeightDomains"};
static const lean_object* l_main___closed__245 = (const lean_object*)&l_main___closed__245_value;
static const lean_ctor_object l_main___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__245_value),LEAN_SCALAR_PTR_LITERAL(143, 232, 106, 128, 44, 176, 30, 97)}};
static const lean_object* l_main___closed__246 = (const lean_object*)&l_main___closed__246_value;
static const lean_array_object l_main___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__246_value)}};
static const lean_object* l_main___closed__247 = (const lean_object*)&l_main___closed__247_value;
static const lean_string_object l_main___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "read"};
static const lean_object* l_main___closed__248 = (const lean_object*)&l_main___closed__248_value;
static const lean_ctor_object l_main___closed__249_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__245_value),LEAN_SCALAR_PTR_LITERAL(143, 232, 106, 128, 44, 176, 30, 97)}};
static const lean_ctor_object l_main___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__249_value_aux_0),((lean_object*)&l_main___closed__248_value),LEAN_SCALAR_PTR_LITERAL(90, 88, 63, 126, 61, 125, 10, 115)}};
static const lean_object* l_main___closed__249 = (const lean_object*)&l_main___closed__249_value;
static const lean_array_object l_main___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__249_value)}};
static const lean_object* l_main___closed__250 = (const lean_object*)&l_main___closed__250_value;
static const lean_string_object l_main___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_BasisCallDomains"};
static const lean_object* l_main___closed__251 = (const lean_object*)&l_main___closed__251_value;
static const lean_ctor_object l_main___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__251_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_object* l_main___closed__252 = (const lean_object*)&l_main___closed__252_value;
static const lean_array_object l_main___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__252_value)}};
static const lean_object* l_main___closed__253 = (const lean_object*)&l_main___closed__253_value;
static const lean_ctor_object l_main___closed__254_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__251_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_ctor_object l_main___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__254_value_aux_0),((lean_object*)&l_main___closed__128_value),LEAN_SCALAR_PTR_LITERAL(201, 201, 161, 138, 59, 141, 168, 64)}};
static const lean_object* l_main___closed__254 = (const lean_object*)&l_main___closed__254_value;
static const lean_string_object l_main___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "active_level"};
static const lean_object* l_main___closed__255 = (const lean_object*)&l_main___closed__255_value;
static const lean_ctor_object l_main___closed__256_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__251_value),LEAN_SCALAR_PTR_LITERAL(102, 249, 186, 193, 200, 68, 223, 27)}};
static const lean_ctor_object l_main___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__256_value_aux_0),((lean_object*)&l_main___closed__255_value),LEAN_SCALAR_PTR_LITERAL(59, 181, 134, 173, 118, 141, 183, 96)}};
static const lean_object* l_main___closed__256 = (const lean_object*)&l_main___closed__256_value;
static const lean_array_object l_main___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__254_value),((lean_object*)&l_main___closed__256_value)}};
static const lean_object* l_main___closed__257 = (const lean_object*)&l_main___closed__257_value;
static const lean_string_object l_main___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PushDomains"};
static const lean_object* l_main___closed__258 = (const lean_object*)&l_main___closed__258_value;
static const lean_ctor_object l_main___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_object* l_main___closed__259 = (const lean_object*)&l_main___closed__259_value;
static const lean_array_object l_main___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__259_value)}};
static const lean_object* l_main___closed__260 = (const lean_object*)&l_main___closed__260_value;
static const lean_string_object l_main___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "canonical_limb"};
static const lean_object* l_main___closed__261 = (const lean_object*)&l_main___closed__261_value;
static const lean_ctor_object l_main___closed__262_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_ctor_object l_main___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__262_value_aux_0),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(37, 191, 150, 61, 199, 52, 62, 68)}};
static const lean_object* l_main___closed__262 = (const lean_object*)&l_main___closed__262_value;
static const lean_ctor_object l_main___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(90, 30, 10, 139, 241, 118, 235, 248)}};
static const lean_ctor_object l_main___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_0),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(224, 48, 54, 211, 193, 177, 145, 147)}};
static const lean_object* l_main___closed__263 = (const lean_object*)&l_main___closed__263_value;
static const lean_array_object l_main___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__262_value),((lean_object*)&l_main___closed__263_value)}};
static const lean_object* l_main___closed__264 = (const lean_object*)&l_main___closed__264_value;
static const lean_string_object l_main___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_AccumulateComplete"};
static const lean_object* l_main___closed__265 = (const lean_object*)&l_main___closed__265_value;
static const lean_ctor_object l_main___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_object* l_main___closed__266 = (const lean_object*)&l_main___closed__266_value;
static const lean_array_object l_main___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__266_value)}};
static const lean_object* l_main___closed__267 = (const lean_object*)&l_main___closed__267_value;
static const lean_string_object l_main___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reference_split"};
static const lean_object* l_main___closed__268 = (const lean_object*)&l_main___closed__268_value;
static const lean_ctor_object l_main___closed__269_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__269_value_aux_0),((lean_object*)&l_main___closed__268_value),LEAN_SCALAR_PTR_LITERAL(53, 78, 70, 0, 122, 104, 106, 162)}};
static const lean_object* l_main___closed__269 = (const lean_object*)&l_main___closed__269_value;
static const lean_string_object l_main___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reference"};
static const lean_object* l_main___closed__270 = (const lean_object*)&l_main___closed__270_value;
static const lean_ctor_object l_main___closed__271_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__271_value_aux_0),((lean_object*)&l_main___closed__270_value),LEAN_SCALAR_PTR_LITERAL(200, 229, 182, 126, 216, 100, 214, 30)}};
static const lean_object* l_main___closed__271 = (const lean_object*)&l_main___closed__271_value;
static const lean_string_object l_main___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "native"};
static const lean_object* l_main___closed__272 = (const lean_object*)&l_main___closed__272_value;
static const lean_ctor_object l_main___closed__273_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(212, 150, 47, 82, 137, 170, 25, 118)}};
static const lean_ctor_object l_main___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__273_value_aux_0),((lean_object*)&l_main___closed__272_value),LEAN_SCALAR_PTR_LITERAL(139, 101, 84, 168, 235, 72, 251, 103)}};
static const lean_object* l_main___closed__273 = (const lean_object*)&l_main___closed__273_value;
static const lean_array_object l_main___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__269_value),((lean_object*)&l_main___closed__271_value),((lean_object*)&l_main___closed__273_value)}};
static const lean_object* l_main___closed__274 = (const lean_object*)&l_main___closed__274_value;
static const lean_string_object l_main___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEV_TailModel"};
static const lean_object* l_main___closed__275 = (const lean_object*)&l_main___closed__275_value;
static const lean_ctor_object l_main___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(157, 199, 125, 235, 91, 24, 105, 238)}};
static const lean_object* l_main___closed__276 = (const lean_object*)&l_main___closed__276_value;
static const lean_array_object l_main___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__276_value)}};
static const lean_object* l_main___closed__277 = (const lean_object*)&l_main___closed__277_value;
static const lean_ctor_object l_main___closed__278_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(157, 199, 125, 235, 91, 24, 105, 238)}};
static const lean_ctor_object l_main___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(228, 202, 46, 22, 38, 12, 190, 47)}};
static const lean_object* l_main___closed__278 = (const lean_object*)&l_main___closed__278_value;
static const lean_array_object l_main___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__278_value)}};
static const lean_object* l_main___closed__279 = (const lean_object*)&l_main___closed__279_value;
static const lean_string_object l_main___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrimitiveTotal"};
static const lean_object* l_main___closed__280 = (const lean_object*)&l_main___closed__280_value;
static const lean_ctor_object l_main___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_object* l_main___closed__281 = (const lean_object*)&l_main___closed__281_value;
static const lean_array_object l_main___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__281_value)}};
static const lean_object* l_main___closed__282 = (const lean_object*)&l_main___closed__282_value;
static const lean_string_object l_main___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_main___closed__283 = (const lean_object*)&l_main___closed__283_value;
static const lean_ctor_object l_main___closed__284_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_ctor_object l_main___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__284_value_aux_0),((lean_object*)&l_main___closed__283_value),LEAN_SCALAR_PTR_LITERAL(72, 248, 151, 53, 138, 193, 201, 134)}};
static const lean_object* l_main___closed__284 = (const lean_object*)&l_main___closed__284_value;
static const lean_string_object l_main___closed__285_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "power"};
static const lean_object* l_main___closed__285 = (const lean_object*)&l_main___closed__285_value;
static const lean_ctor_object l_main___closed__286_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(185, 46, 111, 153, 31, 27, 206, 253)}};
static const lean_ctor_object l_main___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__286_value_aux_0),((lean_object*)&l_main___closed__285_value),LEAN_SCALAR_PTR_LITERAL(32, 190, 36, 8, 135, 52, 153, 36)}};
static const lean_object* l_main___closed__286 = (const lean_object*)&l_main___closed__286_value;
static const lean_array_object l_main___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__284_value),((lean_object*)&l_main___closed__286_value)}};
static const lean_object* l_main___closed__287 = (const lean_object*)&l_main___closed__287_value;
static const lean_string_object l_main___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_PrimitiveBindings"};
static const lean_object* l_main___closed__288 = (const lean_object*)&l_main___closed__288_value;
static const lean_ctor_object l_main___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__288_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_object* l_main___closed__289 = (const lean_object*)&l_main___closed__289_value;
static const lean_array_object l_main___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__289_value)}};
static const lean_object* l_main___closed__290 = (const lean_object*)&l_main___closed__290_value;
static const lean_ctor_object l_main___closed__291_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__288_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__291_value_aux_0),((lean_object*)&l_main___closed__285_value),LEAN_SCALAR_PTR_LITERAL(120, 243, 220, 247, 71, 9, 232, 119)}};
static const lean_object* l_main___closed__291 = (const lean_object*)&l_main___closed__291_value;
static const lean_ctor_object l_main___closed__292_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__288_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_0),((lean_object*)&l_main___closed__283_value),LEAN_SCALAR_PTR_LITERAL(80, 228, 26, 32, 77, 167, 161, 213)}};
static const lean_object* l_main___closed__292 = (const lean_object*)&l_main___closed__292_value;
static const lean_ctor_object l_main___closed__293_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__288_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__293_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__293_value_aux_0),((lean_object*)&l_main___closed__178_value),LEAN_SCALAR_PTR_LITERAL(127, 182, 89, 139, 22, 116, 154, 185)}};
static const lean_object* l_main___closed__293 = (const lean_object*)&l_main___closed__293_value;
static const lean_string_object l_main___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "product_returns"};
static const lean_object* l_main___closed__294 = (const lean_object*)&l_main___closed__294_value;
static const lean_ctor_object l_main___closed__295_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__288_value),LEAN_SCALAR_PTR_LITERAL(129, 36, 240, 157, 129, 108, 14, 25)}};
static const lean_ctor_object l_main___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__295_value_aux_0),((lean_object*)&l_main___closed__294_value),LEAN_SCALAR_PTR_LITERAL(218, 159, 58, 95, 166, 71, 250, 197)}};
static const lean_object* l_main___closed__295 = (const lean_object*)&l_main___closed__295_value;
static const lean_array_object l_main___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__291_value),((lean_object*)&l_main___closed__292_value),((lean_object*)&l_main___closed__293_value),((lean_object*)&l_main___closed__295_value)}};
static const lean_object* l_main___closed__296 = (const lean_object*)&l_main___closed__296_value;
static const lean_string_object l_main___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_StageWideFields"};
static const lean_object* l_main___closed__297 = (const lean_object*)&l_main___closed__297_value;
static const lean_ctor_object l_main___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_object* l_main___closed__298 = (const lean_object*)&l_main___closed__298_value;
static const lean_array_object l_main___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__298_value)}};
static const lean_object* l_main___closed__299 = (const lean_object*)&l_main___closed__299_value;
static const lean_ctor_object l_main___closed__300_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_ctor_object l_main___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__300_value_aux_0),((lean_object*)&l_main___closed__283_value),LEAN_SCALAR_PTR_LITERAL(126, 134, 8, 36, 14, 64, 232, 5)}};
static const lean_object* l_main___closed__300 = (const lean_object*)&l_main___closed__300_value;
static const lean_ctor_object l_main___closed__301_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(151, 226, 209, 46, 217, 11, 52, 230)}};
static const lean_ctor_object l_main___closed__301_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__301_value_aux_0),((lean_object*)&l_main___closed__178_value),LEAN_SCALAR_PTR_LITERAL(249, 12, 234, 27, 52, 60, 8, 210)}};
static const lean_object* l_main___closed__301 = (const lean_object*)&l_main___closed__301_value;
static const lean_array_object l_main___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__300_value),((lean_object*)&l_main___closed__301_value)}};
static const lean_object* l_main___closed__302 = (const lean_object*)&l_main___closed__302_value;
static const lean_string_object l_main___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_StageFields"};
static const lean_object* l_main___closed__303 = (const lean_object*)&l_main___closed__303_value;
static const lean_ctor_object l_main___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_object* l_main___closed__304 = (const lean_object*)&l_main___closed__304_value;
static const lean_array_object l_main___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__304_value)}};
static const lean_object* l_main___closed__305 = (const lean_object*)&l_main___closed__305_value;
static const lean_string_object l_main___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "native_q_roundtrip"};
static const lean_object* l_main___closed__306 = (const lean_object*)&l_main___closed__306_value;
static const lean_ctor_object l_main___closed__307_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_0),((lean_object*)&l_main___closed__306_value),LEAN_SCALAR_PTR_LITERAL(155, 57, 31, 224, 228, 66, 189, 216)}};
static const lean_object* l_main___closed__307 = (const lean_object*)&l_main___closed__307_value;
static const lean_string_object l_main___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "stage_q_roundtrip"};
static const lean_object* l_main___closed__308 = (const lean_object*)&l_main___closed__308_value;
static const lean_ctor_object l_main___closed__309_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__309_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__309_value_aux_0),((lean_object*)&l_main___closed__308_value),LEAN_SCALAR_PTR_LITERAL(194, 148, 39, 25, 40, 226, 186, 153)}};
static const lean_object* l_main___closed__309 = (const lean_object*)&l_main___closed__309_value;
static const lean_string_object l_main___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "native_e_roundtrip"};
static const lean_object* l_main___closed__310 = (const lean_object*)&l_main___closed__310_value;
static const lean_ctor_object l_main___closed__311_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__311_value_aux_0),((lean_object*)&l_main___closed__310_value),LEAN_SCALAR_PTR_LITERAL(160, 6, 125, 229, 39, 141, 99, 176)}};
static const lean_object* l_main___closed__311 = (const lean_object*)&l_main___closed__311_value;
static const lean_string_object l_main___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "stage_e_roundtrip"};
static const lean_object* l_main___closed__312 = (const lean_object*)&l_main___closed__312_value;
static const lean_ctor_object l_main___closed__313_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__313_value_aux_0),((lean_object*)&l_main___closed__312_value),LEAN_SCALAR_PTR_LITERAL(201, 17, 231, 120, 128, 9, 149, 199)}};
static const lean_object* l_main___closed__313 = (const lean_object*)&l_main___closed__313_value;
static const lean_string_object l_main___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "canonical_q"};
static const lean_object* l_main___closed__314 = (const lean_object*)&l_main___closed__314_value;
static const lean_ctor_object l_main___closed__315_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__315_value_aux_0),((lean_object*)&l_main___closed__314_value),LEAN_SCALAR_PTR_LITERAL(37, 113, 62, 137, 175, 52, 111, 150)}};
static const lean_object* l_main___closed__315 = (const lean_object*)&l_main___closed__315_value;
static const lean_string_object l_main___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "canonical_e"};
static const lean_object* l_main___closed__316 = (const lean_object*)&l_main___closed__316_value;
static const lean_ctor_object l_main___closed__317_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__317_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__317_value_aux_0),((lean_object*)&l_main___closed__316_value),LEAN_SCALAR_PTR_LITERAL(38, 151, 244, 177, 194, 108, 179, 131)}};
static const lean_object* l_main___closed__317 = (const lean_object*)&l_main___closed__317_value;
static const lean_ctor_object l_main___closed__318_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 210, 88, 115, 218, 127, 243)}};
static const lean_ctor_object l_main___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__318_value_aux_0),((lean_object*)&l_main___closed__285_value),LEAN_SCALAR_PTR_LITERAL(9, 116, 59, 102, 165, 94, 81, 29)}};
static const lean_object* l_main___closed__318 = (const lean_object*)&l_main___closed__318_value;
static const lean_array_object l_main___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__307_value),((lean_object*)&l_main___closed__309_value),((lean_object*)&l_main___closed__311_value),((lean_object*)&l_main___closed__313_value),((lean_object*)&l_main___closed__315_value),((lean_object*)&l_main___closed__317_value),((lean_object*)&l_main___closed__318_value)}};
static const lean_object* l_main___closed__319 = (const lean_object*)&l_main___closed__319_value;
static const lean_string_object l_main___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEV_MaskQM"};
static const lean_object* l_main___closed__320 = (const lean_object*)&l_main___closed__320_value;
static const lean_ctor_object l_main___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_object* l_main___closed__321 = (const lean_object*)&l_main___closed__321_value;
static const lean_array_object l_main___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__321_value)}};
static const lean_object* l_main___closed__322 = (const lean_object*)&l_main___closed__322_value;
static const lean_ctor_object l_main___closed__323_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__323_value_aux_0),((lean_object*)&l_main___closed__283_value),LEAN_SCALAR_PTR_LITERAL(141, 36, 98, 8, 240, 255, 221, 104)}};
static const lean_object* l_main___closed__323 = (const lean_object*)&l_main___closed__323_value;
static const lean_string_object l_main___closed__324_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "multiply"};
static const lean_object* l_main___closed__324 = (const lean_object*)&l_main___closed__324_value;
static const lean_ctor_object l_main___closed__325_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__325_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__325_value_aux_0),((lean_object*)&l_main___closed__324_value),LEAN_SCALAR_PTR_LITERAL(28, 6, 163, 46, 26, 47, 206, 125)}};
static const lean_object* l_main___closed__325 = (const lean_object*)&l_main___closed__325_value;
static const lean_string_object l_main___closed__326_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "normalization"};
static const lean_object* l_main___closed__326 = (const lean_object*)&l_main___closed__326_value;
static const lean_ctor_object l_main___closed__327_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(136, 186, 3, 181, 103, 103, 190, 241)}};
static const lean_ctor_object l_main___closed__327_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__327_value_aux_0),((lean_object*)&l_main___closed__326_value),LEAN_SCALAR_PTR_LITERAL(77, 137, 85, 187, 103, 93, 201, 122)}};
static const lean_object* l_main___closed__327 = (const lean_object*)&l_main___closed__327_value;
static const lean_array_object l_main___closed__328_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__323_value),((lean_object*)&l_main___closed__325_value),((lean_object*)&l_main___closed__327_value)}};
static const lean_object* l_main___closed__328 = (const lean_object*)&l_main___closed__328_value;
static const lean_string_object l_main___closed__329_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_MaskCarriers"};
static const lean_object* l_main___closed__329 = (const lean_object*)&l_main___closed__329_value;
static const lean_ctor_object l_main___closed__330_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_object* l_main___closed__330 = (const lean_object*)&l_main___closed__330_value;
static const lean_array_object l_main___closed__331_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__330_value)}};
static const lean_object* l_main___closed__331 = (const lean_object*)&l_main___closed__331_value;
static const lean_string_object l_main___closed__332_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_roundtrip"};
static const lean_object* l_main___closed__332 = (const lean_object*)&l_main___closed__332_value;
static const lean_ctor_object l_main___closed__333_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__333_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__333_value_aux_0),((lean_object*)&l_main___closed__332_value),LEAN_SCALAR_PTR_LITERAL(130, 208, 151, 109, 83, 177, 121, 20)}};
static const lean_object* l_main___closed__333 = (const lean_object*)&l_main___closed__333_value;
static const lean_string_object l_main___closed__334_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mask_roundtrip"};
static const lean_object* l_main___closed__334 = (const lean_object*)&l_main___closed__334_value;
static const lean_ctor_object l_main___closed__335_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__335_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__335_value_aux_0),((lean_object*)&l_main___closed__334_value),LEAN_SCALAR_PTR_LITERAL(218, 110, 195, 93, 161, 110, 200, 7)}};
static const lean_object* l_main___closed__335 = (const lean_object*)&l_main___closed__335_value;
static const lean_string_object l_main___closed__336_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_main___closed__336 = (const lean_object*)&l_main___closed__336_value;
static const lean_ctor_object l_main___closed__337_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__337_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__337_value_aux_0),((lean_object*)&l_main___closed__336_value),LEAN_SCALAR_PTR_LITERAL(82, 165, 145, 213, 132, 246, 41, 37)}};
static const lean_object* l_main___closed__337 = (const lean_object*)&l_main___closed__337_value;
static const lean_string_object l_main___closed__338_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "words"};
static const lean_object* l_main___closed__338 = (const lean_object*)&l_main___closed__338_value;
static const lean_ctor_object l_main___closed__339_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__339_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__339_value_aux_0),((lean_object*)&l_main___closed__338_value),LEAN_SCALAR_PTR_LITERAL(214, 85, 166, 61, 123, 195, 168, 158)}};
static const lean_object* l_main___closed__339 = (const lean_object*)&l_main___closed__339_value;
static const lean_string_object l_main___closed__340_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "product_words"};
static const lean_object* l_main___closed__340 = (const lean_object*)&l_main___closed__340_value;
static const lean_ctor_object l_main___closed__341_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__341_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__341_value_aux_0),((lean_object*)&l_main___closed__340_value),LEAN_SCALAR_PTR_LITERAL(158, 236, 12, 137, 49, 66, 11, 253)}};
static const lean_object* l_main___closed__341 = (const lean_object*)&l_main___closed__341_value;
static const lean_string_object l_main___closed__342_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "words_injective"};
static const lean_object* l_main___closed__342 = (const lean_object*)&l_main___closed__342_value;
static const lean_ctor_object l_main___closed__343_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__343_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__343_value_aux_0),((lean_object*)&l_main___closed__342_value),LEAN_SCALAR_PTR_LITERAL(239, 150, 211, 222, 99, 186, 75, 180)}};
static const lean_object* l_main___closed__343 = (const lean_object*)&l_main___closed__343_value;
static const lean_string_object l_main___closed__344_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_injective"};
static const lean_object* l_main___closed__344 = (const lean_object*)&l_main___closed__344_value;
static const lean_ctor_object l_main___closed__345_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(163, 246, 43, 207, 35, 169, 88, 91)}};
static const lean_ctor_object l_main___closed__345_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__345_value_aux_0),((lean_object*)&l_main___closed__344_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 46, 135, 21, 92, 221, 217)}};
static const lean_object* l_main___closed__345 = (const lean_object*)&l_main___closed__345_value;
static const lean_array_object l_main___closed__346_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__333_value),((lean_object*)&l_main___closed__335_value),((lean_object*)&l_main___closed__337_value),((lean_object*)&l_main___closed__339_value),((lean_object*)&l_main___closed__341_value),((lean_object*)&l_main___closed__343_value),((lean_object*)&l_main___closed__345_value)}};
static const lean_object* l_main___closed__346 = (const lean_object*)&l_main___closed__346_value;
static const lean_string_object l_main___closed__347_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_AccumulatePrefix"};
static const lean_object* l_main___closed__347 = (const lean_object*)&l_main___closed__347_value;
static const lean_ctor_object l_main___closed__348_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__347_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_object* l_main___closed__348 = (const lean_object*)&l_main___closed__348_value;
static const lean_array_object l_main___closed__349_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__348_value)}};
static const lean_object* l_main___closed__349 = (const lean_object*)&l_main___closed__349_value;
static const lean_string_object l_main___closed__350_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "installs_commute"};
static const lean_object* l_main___closed__350 = (const lean_object*)&l_main___closed__350_value;
static const lean_ctor_object l_main___closed__351_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__347_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_ctor_object l_main___closed__351_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__351_value_aux_0),((lean_object*)&l_main___closed__350_value),LEAN_SCALAR_PTR_LITERAL(136, 29, 12, 148, 180, 157, 133, 45)}};
static const lean_object* l_main___closed__351 = (const lean_object*)&l_main___closed__351_value;
static const lean_ctor_object l_main___closed__352_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__347_value),LEAN_SCALAR_PTR_LITERAL(68, 33, 129, 167, 197, 240, 36, 98)}};
static const lean_ctor_object l_main___closed__352_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(17, 175, 112, 178, 6, 235, 52, 141)}};
static const lean_object* l_main___closed__352 = (const lean_object*)&l_main___closed__352_value;
static const lean_array_object l_main___closed__353_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__351_value),((lean_object*)&l_main___closed__352_value)}};
static const lean_object* l_main___closed__353 = (const lean_object*)&l_main___closed__353_value;
static const lean_string_object l_main___closed__354_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_RowLoop"};
static const lean_object* l_main___closed__354 = (const lean_object*)&l_main___closed__354_value;
static const lean_ctor_object l_main___closed__355_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__354_value),LEAN_SCALAR_PTR_LITERAL(92, 115, 240, 36, 51, 211, 171, 148)}};
static const lean_object* l_main___closed__355 = (const lean_object*)&l_main___closed__355_value;
static const lean_array_object l_main___closed__356_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__355_value)}};
static const lean_object* l_main___closed__356 = (const lean_object*)&l_main___closed__356_value;
static const lean_ctor_object l_main___closed__357_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__354_value),LEAN_SCALAR_PTR_LITERAL(92, 115, 240, 36, 51, 211, 171, 148)}};
static const lean_ctor_object l_main___closed__357_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__357_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(185, 53, 44, 172, 134, 189, 245, 103)}};
static const lean_object* l_main___closed__357 = (const lean_object*)&l_main___closed__357_value;
static const lean_array_object l_main___closed__358_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__357_value)}};
static const lean_object* l_main___closed__358 = (const lean_object*)&l_main___closed__358_value;
static const lean_string_object l_main___closed__359_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_RowStep"};
static const lean_object* l_main___closed__359 = (const lean_object*)&l_main___closed__359_value;
static const lean_ctor_object l_main___closed__360_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__359_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_object* l_main___closed__360 = (const lean_object*)&l_main___closed__360_value;
static const lean_array_object l_main___closed__361_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__360_value)}};
static const lean_object* l_main___closed__361 = (const lean_object*)&l_main___closed__361_value;
static const lean_string_object l_main___closed__362_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* l_main___closed__362 = (const lean_object*)&l_main___closed__362_value;
static const lean_ctor_object l_main___closed__363_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__359_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_ctor_object l_main___closed__363_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__363_value_aux_0),((lean_object*)&l_main___closed__362_value),LEAN_SCALAR_PTR_LITERAL(98, 105, 31, 115, 79, 219, 35, 90)}};
static const lean_object* l_main___closed__363 = (const lean_object*)&l_main___closed__363_value;
static const lean_string_object l_main___closed__364_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_main___closed__364 = (const lean_object*)&l_main___closed__364_value;
static const lean_ctor_object l_main___closed__365_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__359_value),LEAN_SCALAR_PTR_LITERAL(76, 129, 94, 237, 86, 155, 91, 163)}};
static const lean_ctor_object l_main___closed__365_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__365_value_aux_0),((lean_object*)&l_main___closed__364_value),LEAN_SCALAR_PTR_LITERAL(122, 232, 220, 11, 52, 202, 2, 209)}};
static const lean_object* l_main___closed__365 = (const lean_object*)&l_main___closed__365_value;
static const lean_array_object l_main___closed__366_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__363_value),((lean_object*)&l_main___closed__365_value)}};
static const lean_object* l_main___closed__366 = (const lean_object*)&l_main___closed__366_value;
static const lean_string_object l_main___closed__367_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_CtorResults"};
static const lean_object* l_main___closed__367 = (const lean_object*)&l_main___closed__367_value;
static const lean_ctor_object l_main___closed__368_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__367_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_object* l_main___closed__368 = (const lean_object*)&l_main___closed__368_value;
static const lean_array_object l_main___closed__369_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__368_value)}};
static const lean_object* l_main___closed__369 = (const lean_object*)&l_main___closed__369_value;
static const lean_string_object l_main___closed__370_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "m31"};
static const lean_object* l_main___closed__370 = (const lean_object*)&l_main___closed__370_value;
static const lean_ctor_object l_main___closed__371_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__367_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_ctor_object l_main___closed__371_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__371_value_aux_0),((lean_object*)&l_main___closed__370_value),LEAN_SCALAR_PTR_LITERAL(210, 198, 21, 66, 212, 234, 99, 160)}};
static const lean_object* l_main___closed__371 = (const lean_object*)&l_main___closed__371_value;
static const lean_string_object l_main___closed__372_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "qm"};
static const lean_object* l_main___closed__372 = (const lean_object*)&l_main___closed__372_value;
static const lean_ctor_object l_main___closed__373_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__367_value),LEAN_SCALAR_PTR_LITERAL(6, 27, 104, 250, 2, 0, 254, 12)}};
static const lean_ctor_object l_main___closed__373_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__373_value_aux_0),((lean_object*)&l_main___closed__372_value),LEAN_SCALAR_PTR_LITERAL(196, 70, 227, 155, 170, 89, 140, 236)}};
static const lean_object* l_main___closed__373 = (const lean_object*)&l_main___closed__373_value;
static const lean_array_object l_main___closed__374_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__371_value),((lean_object*)&l_main___closed__373_value)}};
static const lean_object* l_main___closed__374 = (const lean_object*)&l_main___closed__374_value;
static const lean_string_object l_main___closed__375_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_BasisProducer"};
static const lean_object* l_main___closed__375 = (const lean_object*)&l_main___closed__375_value;
static const lean_ctor_object l_main___closed__376_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_object* l_main___closed__376 = (const lean_object*)&l_main___closed__376_value;
static const lean_array_object l_main___closed__377_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__376_value)}};
static const lean_object* l_main___closed__377 = (const lean_object*)&l_main___closed__377_value;
static const lean_ctor_object l_main___closed__378_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__378_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__378_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(138, 20, 62, 99, 136, 142, 96, 108)}};
static const lean_object* l_main___closed__378 = (const lean_object*)&l_main___closed__378_value;
static const lean_ctor_object l_main___closed__379_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__379_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__379_value_aux_0),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(153, 167, 129, 212, 4, 171, 142, 82)}};
static const lean_object* l_main___closed__379 = (const lean_object*)&l_main___closed__379_value;
static const lean_string_object l_main___closed__380_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "read_canonical"};
static const lean_object* l_main___closed__380 = (const lean_object*)&l_main___closed__380_value;
static const lean_ctor_object l_main___closed__381_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(43, 106, 113, 99, 210, 201, 55, 129)}};
static const lean_ctor_object l_main___closed__381_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__381_value_aux_0),((lean_object*)&l_main___closed__380_value),LEAN_SCALAR_PTR_LITERAL(101, 8, 57, 218, 103, 141, 234, 38)}};
static const lean_object* l_main___closed__381 = (const lean_object*)&l_main___closed__381_value;
static const lean_array_object l_main___closed__382_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__378_value),((lean_object*)&l_main___closed__379_value),((lean_object*)&l_main___closed__381_value)}};
static const lean_object* l_main___closed__382 = (const lean_object*)&l_main___closed__382_value;
static const lean_string_object l_main___closed__383_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_CtorNormalization"};
static const lean_object* l_main___closed__383 = (const lean_object*)&l_main___closed__383_value;
static const lean_ctor_object l_main___closed__384_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__383_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_object* l_main___closed__384 = (const lean_object*)&l_main___closed__384_value;
static const lean_array_object l_main___closed__385_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__384_value)}};
static const lean_object* l_main___closed__385 = (const lean_object*)&l_main___closed__385_value;
static const lean_ctor_object l_main___closed__386_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__383_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__386_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__386_value_aux_0),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(142, 136, 155, 22, 158, 201, 157, 10)}};
static const lean_object* l_main___closed__386 = (const lean_object*)&l_main___closed__386_value;
static const lean_string_object l_main___closed__387_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reduce_identity"};
static const lean_object* l_main___closed__387 = (const lean_object*)&l_main___closed__387_value;
static const lean_ctor_object l_main___closed__388_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__383_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__388_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__388_value_aux_0),((lean_object*)&l_main___closed__387_value),LEAN_SCALAR_PTR_LITERAL(61, 252, 131, 126, 159, 182, 16, 255)}};
static const lean_object* l_main___closed__388 = (const lean_object*)&l_main___closed__388_value;
static const lean_string_object l_main___closed__389_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "identity"};
static const lean_object* l_main___closed__389 = (const lean_object*)&l_main___closed__389_value;
static const lean_ctor_object l_main___closed__390_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__383_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__390_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__390_value_aux_0),((lean_object*)&l_main___closed__389_value),LEAN_SCALAR_PTR_LITERAL(210, 71, 87, 226, 127, 90, 131, 111)}};
static const lean_object* l_main___closed__390 = (const lean_object*)&l_main___closed__390_value;
static const lean_ctor_object l_main___closed__391_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__383_value),LEAN_SCALAR_PTR_LITERAL(8, 104, 235, 21, 190, 41, 58, 94)}};
static const lean_ctor_object l_main___closed__391_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__391_value_aux_0),((lean_object*)&l_main___closed__199_value),LEAN_SCALAR_PTR_LITERAL(221, 105, 11, 156, 18, 104, 45, 153)}};
static const lean_object* l_main___closed__391 = (const lean_object*)&l_main___closed__391_value;
static const lean_array_object l_main___closed__392_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__386_value),((lean_object*)&l_main___closed__388_value),((lean_object*)&l_main___closed__390_value),((lean_object*)&l_main___closed__391_value)}};
static const lean_object* l_main___closed__392 = (const lean_object*)&l_main___closed__392_value;
static const lean_string_object l_main___closed__393_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NEV_BorrowMaps"};
static const lean_object* l_main___closed__393 = (const lean_object*)&l_main___closed__393_value;
static const lean_ctor_object l_main___closed__394_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__393_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_object* l_main___closed__394 = (const lean_object*)&l_main___closed__394_value;
static const lean_array_object l_main___closed__395_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__394_value)}};
static const lean_object* l_main___closed__395 = (const lean_object*)&l_main___closed__395_value;
static const lean_string_object l_main___closed__396_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "vector_read"};
static const lean_object* l_main___closed__396 = (const lean_object*)&l_main___closed__396_value;
static const lean_ctor_object l_main___closed__397_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__393_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_ctor_object l_main___closed__397_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__397_value_aux_0),((lean_object*)&l_main___closed__396_value),LEAN_SCALAR_PTR_LITERAL(107, 114, 4, 119, 10, 205, 72, 20)}};
static const lean_object* l_main___closed__397 = (const lean_object*)&l_main___closed__397_value;
static const lean_string_object l_main___closed__398_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "weight_read"};
static const lean_object* l_main___closed__398 = (const lean_object*)&l_main___closed__398_value;
static const lean_ctor_object l_main___closed__399_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__393_value),LEAN_SCALAR_PTR_LITERAL(84, 131, 215, 133, 164, 5, 204, 78)}};
static const lean_ctor_object l_main___closed__399_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__399_value_aux_0),((lean_object*)&l_main___closed__398_value),LEAN_SCALAR_PTR_LITERAL(66, 215, 171, 160, 143, 191, 27, 224)}};
static const lean_object* l_main___closed__399 = (const lean_object*)&l_main___closed__399_value;
static const lean_array_object l_main___closed__400_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__397_value),((lean_object*)&l_main___closed__399_value)}};
static const lean_object* l_main___closed__400 = (const lean_object*)&l_main___closed__400_value;
static const lean_string_object l_main___closed__401_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEV_PushUse"};
static const lean_object* l_main___closed__401 = (const lean_object*)&l_main___closed__401_value;
static const lean_ctor_object l_main___closed__402_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__401_value),LEAN_SCALAR_PTR_LITERAL(97, 126, 68, 27, 4, 34, 116, 169)}};
static const lean_object* l_main___closed__402 = (const lean_object*)&l_main___closed__402_value;
static const lean_array_object l_main___closed__403_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__402_value)}};
static const lean_object* l_main___closed__403 = (const lean_object*)&l_main___closed__403_value;
static const lean_ctor_object l_main___closed__404_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__401_value),LEAN_SCALAR_PTR_LITERAL(97, 126, 68, 27, 4, 34, 116, 169)}};
static const lean_ctor_object l_main___closed__404_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__404_value_aux_0),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(200, 204, 223, 157, 21, 151, 112, 97)}};
static const lean_object* l_main___closed__404 = (const lean_object*)&l_main___closed__404_value;
static const lean_array_object l_main___closed__405_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__404_value)}};
static const lean_object* l_main___closed__405 = (const lean_object*)&l_main___closed__405_value;
static const lean_string_object l_main___closed__406_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_AccumulateTail"};
static const lean_object* l_main___closed__406 = (const lean_object*)&l_main___closed__406_value;
static const lean_ctor_object l_main___closed__407_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_object* l_main___closed__407 = (const lean_object*)&l_main___closed__407_value;
static const lean_array_object l_main___closed__408_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__407_value)}};
static const lean_object* l_main___closed__408 = (const lean_object*)&l_main___closed__408_value;
static const lean_string_object l_main___closed__409_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "source_cut"};
static const lean_object* l_main___closed__409 = (const lean_object*)&l_main___closed__409_value;
static const lean_ctor_object l_main___closed__410_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_ctor_object l_main___closed__410_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__410_value_aux_0),((lean_object*)&l_main___closed__409_value),LEAN_SCALAR_PTR_LITERAL(62, 124, 8, 201, 51, 162, 133, 218)}};
static const lean_object* l_main___closed__410 = (const lean_object*)&l_main___closed__410_value;
static const lean_string_object l_main___closed__411_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "successful_frame"};
static const lean_object* l_main___closed__411 = (const lean_object*)&l_main___closed__411_value;
static const lean_ctor_object l_main___closed__412_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(161, 9, 118, 95, 14, 193, 4, 47)}};
static const lean_ctor_object l_main___closed__412_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__412_value_aux_0),((lean_object*)&l_main___closed__411_value),LEAN_SCALAR_PTR_LITERAL(243, 39, 41, 106, 151, 45, 123, 153)}};
static const lean_object* l_main___closed__412 = (const lean_object*)&l_main___closed__412_value;
static const lean_array_object l_main___closed__413_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__410_value),((lean_object*)&l_main___closed__412_value)}};
static const lean_object* l_main___closed__413 = (const lean_object*)&l_main___closed__413_value;
static const lean_string_object l_main___closed__414_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEV_BasisOuterRaw"};
static const lean_object* l_main___closed__414 = (const lean_object*)&l_main___closed__414_value;
static const lean_ctor_object l_main___closed__415_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__414_value),LEAN_SCALAR_PTR_LITERAL(147, 92, 74, 164, 13, 225, 12, 235)}};
static const lean_object* l_main___closed__415 = (const lean_object*)&l_main___closed__415_value;
static const lean_array_object l_main___closed__416_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__415_value)}};
static const lean_object* l_main___closed__416 = (const lean_object*)&l_main___closed__416_value;
static const lean_string_object l_main___closed__417_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "levels_eq"};
static const lean_object* l_main___closed__417 = (const lean_object*)&l_main___closed__417_value;
static const lean_ctor_object l_main___closed__418_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__414_value),LEAN_SCALAR_PTR_LITERAL(147, 92, 74, 164, 13, 225, 12, 235)}};
static const lean_ctor_object l_main___closed__418_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__418_value_aux_0),((lean_object*)&l_main___closed__417_value),LEAN_SCALAR_PTR_LITERAL(162, 74, 55, 75, 104, 78, 184, 204)}};
static const lean_object* l_main___closed__418 = (const lean_object*)&l_main___closed__418_value;
static const lean_array_object l_main___closed__419_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__418_value)}};
static const lean_object* l_main___closed__419 = (const lean_object*)&l_main___closed__419_value;
static const lean_string_object l_main___closed__420_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NEV_AccumulateCallees"};
static const lean_object* l_main___closed__420 = (const lean_object*)&l_main___closed__420_value;
static const lean_ctor_object l_main___closed__421_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_object* l_main___closed__421 = (const lean_object*)&l_main___closed__421_value;
static const lean_array_object l_main___closed__422_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__421_value)}};
static const lean_object* l_main___closed__422 = (const lean_object*)&l_main___closed__422_value;
static const lean_string_object l_main___closed__423_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_e_reverse"};
static const lean_object* l_main___closed__423 = (const lean_object*)&l_main___closed__423_value;
static const lean_ctor_object l_main___closed__424_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__424_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__424_value_aux_0),((lean_object*)&l_main___closed__423_value),LEAN_SCALAR_PTR_LITERAL(150, 164, 67, 183, 104, 114, 78, 163)}};
static const lean_object* l_main___closed__424 = (const lean_object*)&l_main___closed__424_value;
static const lean_string_object l_main___closed__425_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "native_q_reverse"};
static const lean_object* l_main___closed__425 = (const lean_object*)&l_main___closed__425_value;
static const lean_ctor_object l_main___closed__426_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__426_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__426_value_aux_0),((lean_object*)&l_main___closed__425_value),LEAN_SCALAR_PTR_LITERAL(215, 194, 151, 125, 2, 44, 166, 206)}};
static const lean_object* l_main___closed__426 = (const lean_object*)&l_main___closed__426_value;
static const lean_string_object l_main___closed__427_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ctor_e_reverse"};
static const lean_object* l_main___closed__427 = (const lean_object*)&l_main___closed__427_value;
static const lean_ctor_object l_main___closed__428_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__428_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__428_value_aux_0),((lean_object*)&l_main___closed__427_value),LEAN_SCALAR_PTR_LITERAL(16, 39, 51, 58, 214, 200, 60, 171)}};
static const lean_object* l_main___closed__428 = (const lean_object*)&l_main___closed__428_value;
static const lean_string_object l_main___closed__429_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "wide_add"};
static const lean_object* l_main___closed__429 = (const lean_object*)&l_main___closed__429_value;
static const lean_ctor_object l_main___closed__430_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__430_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__430_value_aux_0),((lean_object*)&l_main___closed__429_value),LEAN_SCALAR_PTR_LITERAL(34, 218, 202, 210, 8, 39, 79, 50)}};
static const lean_object* l_main___closed__430 = (const lean_object*)&l_main___closed__430_value;
static const lean_string_object l_main___closed__431_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wide_product"};
static const lean_object* l_main___closed__431 = (const lean_object*)&l_main___closed__431_value;
static const lean_ctor_object l_main___closed__432_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__432_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__432_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(252, 210, 17, 228, 78, 86, 70, 134)}};
static const lean_object* l_main___closed__432 = (const lean_object*)&l_main___closed__432_value;
static const lean_string_object l_main___closed__433_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "qm_product"};
static const lean_object* l_main___closed__433 = (const lean_object*)&l_main___closed__433_value;
static const lean_ctor_object l_main___closed__434_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__434_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__434_value_aux_0),((lean_object*)&l_main___closed__433_value),LEAN_SCALAR_PTR_LITERAL(159, 66, 150, 93, 38, 46, 111, 155)}};
static const lean_object* l_main___closed__434 = (const lean_object*)&l_main___closed__434_value;
static const lean_string_object l_main___closed__435_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "from_qm"};
static const lean_object* l_main___closed__435 = (const lean_object*)&l_main___closed__435_value;
static const lean_ctor_object l_main___closed__436_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__436_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__436_value_aux_0),((lean_object*)&l_main___closed__435_value),LEAN_SCALAR_PTR_LITERAL(238, 242, 106, 160, 170, 194, 103, 116)}};
static const lean_object* l_main___closed__436 = (const lean_object*)&l_main___closed__436_value;
static const lean_string_object l_main___closed__437_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l_main___closed__437 = (const lean_object*)&l_main___closed__437_value;
static const lean_ctor_object l_main___closed__438_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__438_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__438_value_aux_0),((lean_object*)&l_main___closed__437_value),LEAN_SCALAR_PTR_LITERAL(125, 149, 78, 24, 134, 220, 102, 223)}};
static const lean_object* l_main___closed__438 = (const lean_object*)&l_main___closed__438_value;
static const lean_string_object l_main___closed__439_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "from_m31"};
static const lean_object* l_main___closed__439 = (const lean_object*)&l_main___closed__439_value;
static const lean_ctor_object l_main___closed__440_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__420_value),LEAN_SCALAR_PTR_LITERAL(48, 142, 148, 97, 3, 214, 41, 61)}};
static const lean_ctor_object l_main___closed__440_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__440_value_aux_0),((lean_object*)&l_main___closed__439_value),LEAN_SCALAR_PTR_LITERAL(111, 0, 155, 214, 86, 43, 159, 215)}};
static const lean_object* l_main___closed__440 = (const lean_object*)&l_main___closed__440_value;
static const lean_array_object l_main___closed__441_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l_main___closed__424_value),((lean_object*)&l_main___closed__426_value),((lean_object*)&l_main___closed__428_value),((lean_object*)&l_main___closed__430_value),((lean_object*)&l_main___closed__432_value),((lean_object*)&l_main___closed__434_value),((lean_object*)&l_main___closed__436_value),((lean_object*)&l_main___closed__438_value),((lean_object*)&l_main___closed__440_value)}};
static const lean_object* l_main___closed__441 = (const lean_object*)&l_main___closed__441_value;
static const lean_string_object l_main___closed__442_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_BasisOuterStep"};
static const lean_object* l_main___closed__442 = (const lean_object*)&l_main___closed__442_value;
static const lean_ctor_object l_main___closed__443_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__442_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_object* l_main___closed__443 = (const lean_object*)&l_main___closed__443_value;
static const lean_array_object l_main___closed__444_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__443_value)}};
static const lean_object* l_main___closed__444 = (const lean_object*)&l_main___closed__444_value;
static const lean_ctor_object l_main___closed__445_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__442_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__445_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__445_value_aux_0),((lean_object*)&l_main___closed__324_value),LEAN_SCALAR_PTR_LITERAL(98, 165, 37, 87, 65, 230, 59, 175)}};
static const lean_object* l_main___closed__445 = (const lean_object*)&l_main___closed__445_value;
static const lean_string_object l_main___closed__446_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subtract"};
static const lean_object* l_main___closed__446 = (const lean_object*)&l_main___closed__446_value;
static const lean_ctor_object l_main___closed__447_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__442_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__447_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__447_value_aux_0),((lean_object*)&l_main___closed__446_value),LEAN_SCALAR_PTR_LITERAL(199, 124, 5, 37, 203, 213, 59, 77)}};
static const lean_object* l_main___closed__447 = (const lean_object*)&l_main___closed__447_value;
static const lean_string_object l_main___closed__448_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "double"};
static const lean_object* l_main___closed__448 = (const lean_object*)&l_main___closed__448_value;
static const lean_ctor_object l_main___closed__449_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__442_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__449_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__449_value_aux_0),((lean_object*)&l_main___closed__448_value),LEAN_SCALAR_PTR_LITERAL(118, 233, 175, 147, 231, 166, 48, 20)}};
static const lean_object* l_main___closed__449 = (const lean_object*)&l_main___closed__449_value;
static const lean_ctor_object l_main___closed__450_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__442_value),LEAN_SCALAR_PTR_LITERAL(126, 47, 172, 125, 92, 130, 92, 69)}};
static const lean_ctor_object l_main___closed__450_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__450_value_aux_0),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(31, 7, 225, 155, 133, 215, 182, 68)}};
static const lean_object* l_main___closed__450 = (const lean_object*)&l_main___closed__450_value;
static const lean_array_object l_main___closed__451_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__445_value),((lean_object*)&l_main___closed__447_value),((lean_object*)&l_main___closed__449_value),((lean_object*)&l_main___closed__450_value)}};
static const lean_object* l_main___closed__451 = (const lean_object*)&l_main___closed__451_value;
static const lean_string_object l_main___closed__452_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEV_BasisRaw"};
static const lean_object* l_main___closed__452 = (const lean_object*)&l_main___closed__452_value;
static const lean_ctor_object l_main___closed__453_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__452_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_object* l_main___closed__453 = (const lean_object*)&l_main___closed__453_value;
static const lean_array_object l_main___closed__454_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__453_value)}};
static const lean_object* l_main___closed__454 = (const lean_object*)&l_main___closed__454_value;
static const lean_string_object l_main___closed__455_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_step"};
static const lean_object* l_main___closed__455 = (const lean_object*)&l_main___closed__455_value;
static const lean_ctor_object l_main___closed__456_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__452_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__456_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__456_value_aux_0),((lean_object*)&l_main___closed__455_value),LEAN_SCALAR_PTR_LITERAL(244, 61, 64, 151, 73, 1, 23, 137)}};
static const lean_object* l_main___closed__456 = (const lean_object*)&l_main___closed__456_value;
static const lean_string_object l_main___closed__457_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_stop"};
static const lean_object* l_main___closed__457 = (const lean_object*)&l_main___closed__457_value;
static const lean_ctor_object l_main___closed__458_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__452_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__458_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__458_value_aux_0),((lean_object*)&l_main___closed__457_value),LEAN_SCALAR_PTR_LITERAL(126, 141, 50, 248, 149, 52, 169, 107)}};
static const lean_object* l_main___closed__458 = (const lean_object*)&l_main___closed__458_value;
static const lean_string_object l_main___closed__459_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inner_loop"};
static const lean_object* l_main___closed__459 = (const lean_object*)&l_main___closed__459_value;
static const lean_ctor_object l_main___closed__460_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__452_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 32, 210, 71, 82, 249, 89)}};
static const lean_ctor_object l_main___closed__460_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__460_value_aux_0),((lean_object*)&l_main___closed__459_value),LEAN_SCALAR_PTR_LITERAL(31, 141, 210, 117, 243, 125, 50, 25)}};
static const lean_object* l_main___closed__460 = (const lean_object*)&l_main___closed__460_value;
static const lean_array_object l_main___closed__461_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__456_value),((lean_object*)&l_main___closed__458_value),((lean_object*)&l_main___closed__460_value)}};
static const lean_object* l_main___closed__461 = (const lean_object*)&l_main___closed__461_value;
static const lean_string_object l_main___closed__462_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_AccumulateCarriers"};
static const lean_object* l_main___closed__462 = (const lean_object*)&l_main___closed__462_value;
static const lean_ctor_object l_main___closed__463_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_object* l_main___closed__463 = (const lean_object*)&l_main___closed__463_value;
static const lean_array_object l_main___closed__464_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__463_value)}};
static const lean_object* l_main___closed__464 = (const lean_object*)&l_main___closed__464_value;
static const lean_string_object l_main___closed__465_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "array_inverse"};
static const lean_object* l_main___closed__465 = (const lean_object*)&l_main___closed__465_value;
static const lean_ctor_object l_main___closed__466_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__466_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__466_value_aux_0),((lean_object*)&l_main___closed__465_value),LEAN_SCALAR_PTR_LITERAL(116, 18, 4, 130, 54, 4, 74, 137)}};
static const lean_object* l_main___closed__466 = (const lean_object*)&l_main___closed__466_value;
static const lean_string_object l_main___closed__467_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "vector_inverse"};
static const lean_object* l_main___closed__467 = (const lean_object*)&l_main___closed__467_value;
static const lean_ctor_object l_main___closed__468_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__468_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__468_value_aux_0),((lean_object*)&l_main___closed__467_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 162, 49, 179, 145, 153, 129)}};
static const lean_object* l_main___closed__468 = (const lean_object*)&l_main___closed__468_value;
static const lean_string_object l_main___closed__469_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "point_roundtrip"};
static const lean_object* l_main___closed__469 = (const lean_object*)&l_main___closed__469_value;
static const lean_ctor_object l_main___closed__470_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__470_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__470_value_aux_0),((lean_object*)&l_main___closed__469_value),LEAN_SCALAR_PTR_LITERAL(156, 44, 95, 100, 26, 227, 248, 33)}};
static const lean_object* l_main___closed__470 = (const lean_object*)&l_main___closed__470_value;
static const lean_string_object l_main___closed__471_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "point_reverse"};
static const lean_object* l_main___closed__471 = (const lean_object*)&l_main___closed__471_value;
static const lean_ctor_object l_main___closed__472_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__472_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__472_value_aux_0),((lean_object*)&l_main___closed__471_value),LEAN_SCALAR_PTR_LITERAL(147, 0, 191, 151, 250, 168, 201, 203)}};
static const lean_object* l_main___closed__472 = (const lean_object*)&l_main___closed__472_value;
static const lean_string_object l_main___closed__473_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "prepared_roundtrip"};
static const lean_object* l_main___closed__473 = (const lean_object*)&l_main___closed__473_value;
static const lean_ctor_object l_main___closed__474_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__474_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__474_value_aux_0),((lean_object*)&l_main___closed__473_value),LEAN_SCALAR_PTR_LITERAL(108, 3, 93, 23, 40, 223, 201, 143)}};
static const lean_object* l_main___closed__474 = (const lean_object*)&l_main___closed__474_value;
static const lean_string_object l_main___closed__475_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "prepared_reverse"};
static const lean_object* l_main___closed__475 = (const lean_object*)&l_main___closed__475_value;
static const lean_ctor_object l_main___closed__476_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__476_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__476_value_aux_0),((lean_object*)&l_main___closed__475_value),LEAN_SCALAR_PTR_LITERAL(244, 161, 224, 53, 40, 133, 17, 91)}};
static const lean_object* l_main___closed__476 = (const lean_object*)&l_main___closed__476_value;
static const lean_string_object l_main___closed__477_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "accumulator_roundtrip"};
static const lean_object* l_main___closed__477 = (const lean_object*)&l_main___closed__477_value;
static const lean_ctor_object l_main___closed__478_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__478_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__478_value_aux_0),((lean_object*)&l_main___closed__477_value),LEAN_SCALAR_PTR_LITERAL(99, 188, 194, 12, 235, 54, 231, 243)}};
static const lean_object* l_main___closed__478 = (const lean_object*)&l_main___closed__478_value;
static const lean_string_object l_main___closed__479_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "accumulator_reverse"};
static const lean_object* l_main___closed__479 = (const lean_object*)&l_main___closed__479_value;
static const lean_ctor_object l_main___closed__480_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__480_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__480_value_aux_0),((lean_object*)&l_main___closed__479_value),LEAN_SCALAR_PTR_LITERAL(233, 93, 105, 102, 124, 88, 172, 21)}};
static const lean_object* l_main___closed__480 = (const lean_object*)&l_main___closed__480_value;
static const lean_string_object l_main___closed__481_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "q_roundtrip"};
static const lean_object* l_main___closed__481 = (const lean_object*)&l_main___closed__481_value;
static const lean_ctor_object l_main___closed__482_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__482_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__482_value_aux_0),((lean_object*)&l_main___closed__481_value),LEAN_SCALAR_PTR_LITERAL(28, 122, 124, 100, 70, 1, 123, 150)}};
static const lean_object* l_main___closed__482 = (const lean_object*)&l_main___closed__482_value;
static const lean_string_object l_main___closed__483_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "q_reverse"};
static const lean_object* l_main___closed__483 = (const lean_object*)&l_main___closed__483_value;
static const lean_ctor_object l_main___closed__484_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__484_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__484_value_aux_0),((lean_object*)&l_main___closed__483_value),LEAN_SCALAR_PTR_LITERAL(203, 219, 157, 74, 1, 154, 226, 99)}};
static const lean_object* l_main___closed__484 = (const lean_object*)&l_main___closed__484_value;
static const lean_string_object l_main___closed__485_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "e_roundtrip"};
static const lean_object* l_main___closed__485 = (const lean_object*)&l_main___closed__485_value;
static const lean_ctor_object l_main___closed__486_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__486_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__486_value_aux_0),((lean_object*)&l_main___closed__485_value),LEAN_SCALAR_PTR_LITERAL(85, 168, 88, 76, 152, 160, 40, 86)}};
static const lean_object* l_main___closed__486 = (const lean_object*)&l_main___closed__486_value;
static const lean_string_object l_main___closed__487_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "e_reverse"};
static const lean_object* l_main___closed__487 = (const lean_object*)&l_main___closed__487_value;
static const lean_ctor_object l_main___closed__488_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__488_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__488_value_aux_0),((lean_object*)&l_main___closed__487_value),LEAN_SCALAR_PTR_LITERAL(71, 132, 254, 11, 5, 157, 151, 188)}};
static const lean_object* l_main___closed__488 = (const lean_object*)&l_main___closed__488_value;
static const lean_string_object l_main___closed__489_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "weights_roundtrip"};
static const lean_object* l_main___closed__489 = (const lean_object*)&l_main___closed__489_value;
static const lean_ctor_object l_main___closed__490_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__490_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__490_value_aux_0),((lean_object*)&l_main___closed__489_value),LEAN_SCALAR_PTR_LITERAL(39, 65, 236, 205, 34, 139, 36, 42)}};
static const lean_object* l_main___closed__490 = (const lean_object*)&l_main___closed__490_value;
static const lean_string_object l_main___closed__491_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "weights_reverse"};
static const lean_object* l_main___closed__491 = (const lean_object*)&l_main___closed__491_value;
static const lean_ctor_object l_main___closed__492_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(120, 235, 79, 143, 52, 227, 74, 173)}};
static const lean_ctor_object l_main___closed__492_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__492_value_aux_0),((lean_object*)&l_main___closed__491_value),LEAN_SCALAR_PTR_LITERAL(192, 184, 91, 14, 201, 45, 240, 101)}};
static const lean_object* l_main___closed__492 = (const lean_object*)&l_main___closed__492_value;
static const lean_array_object l_main___closed__493_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l_main___closed__466_value),((lean_object*)&l_main___closed__468_value),((lean_object*)&l_main___closed__470_value),((lean_object*)&l_main___closed__472_value),((lean_object*)&l_main___closed__474_value),((lean_object*)&l_main___closed__476_value),((lean_object*)&l_main___closed__478_value),((lean_object*)&l_main___closed__480_value),((lean_object*)&l_main___closed__482_value),((lean_object*)&l_main___closed__484_value),((lean_object*)&l_main___closed__486_value),((lean_object*)&l_main___closed__488_value),((lean_object*)&l_main___closed__490_value),((lean_object*)&l_main___closed__492_value)}};
static const lean_object* l_main___closed__493 = (const lean_object*)&l_main___closed__493_value;
static const lean_string_object l_main___closed__494_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_CodeFieldPacket"};
static const lean_object* l_main___closed__494 = (const lean_object*)&l_main___closed__494_value;
static const lean_ctor_object l_main___closed__495_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__494_value),LEAN_SCALAR_PTR_LITERAL(207, 133, 218, 246, 17, 125, 252, 232)}};
static const lean_object* l_main___closed__495 = (const lean_object*)&l_main___closed__495_value;
static const lean_array_object l_main___closed__496_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__495_value)}};
static const lean_object* l_main___closed__496 = (const lean_object*)&l_main___closed__496_value;
static const lean_string_object l_main___closed__497_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "extracted_root"};
static const lean_object* l_main___closed__497 = (const lean_object*)&l_main___closed__497_value;
static const lean_ctor_object l_main___closed__498_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__494_value),LEAN_SCALAR_PTR_LITERAL(207, 133, 218, 246, 17, 125, 252, 232)}};
static const lean_ctor_object l_main___closed__498_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__498_value_aux_0),((lean_object*)&l_main___closed__497_value),LEAN_SCALAR_PTR_LITERAL(106, 128, 200, 87, 18, 72, 183, 118)}};
static const lean_object* l_main___closed__498 = (const lean_object*)&l_main___closed__498_value;
static const lean_string_object l_main___closed__499_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_CodeFieldUse"};
static const lean_object* l_main___closed__499 = (const lean_object*)&l_main___closed__499_value;
static const lean_string_object l_main___closed__500_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "basis_call"};
static const lean_object* l_main___closed__500 = (const lean_object*)&l_main___closed__500_value;
static const lean_ctor_object l_main___closed__501_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__499_value),LEAN_SCALAR_PTR_LITERAL(134, 68, 239, 157, 216, 146, 3, 131)}};
static const lean_ctor_object l_main___closed__501_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__501_value_aux_0),((lean_object*)&l_main___closed__500_value),LEAN_SCALAR_PTR_LITERAL(141, 91, 210, 39, 196, 240, 180, 152)}};
static const lean_object* l_main___closed__501 = (const lean_object*)&l_main___closed__501_value;
static const lean_array_object l_main___closed__502_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__498_value),((lean_object*)&l_main___closed__501_value)}};
static const lean_object* l_main___closed__502 = (const lean_object*)&l_main___closed__502_value;
static const lean_ctor_object l_main___closed__503_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__499_value),LEAN_SCALAR_PTR_LITERAL(134, 68, 239, 157, 216, 146, 3, 131)}};
static const lean_object* l_main___closed__503 = (const lean_object*)&l_main___closed__503_value;
static const lean_array_object l_main___closed__504_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__503_value)}};
static const lean_object* l_main___closed__504 = (const lean_object*)&l_main___closed__504_value;
static const lean_array_object l_main___closed__505_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__501_value)}};
static const lean_object* l_main___closed__505 = (const lean_object*)&l_main___closed__505_value;
static const lean_string_object l_main___closed__506_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NEV_CodeFieldBridge"};
static const lean_object* l_main___closed__506 = (const lean_object*)&l_main___closed__506_value;
static const lean_ctor_object l_main___closed__507_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_object* l_main___closed__507 = (const lean_object*)&l_main___closed__507_value;
static const lean_array_object l_main___closed__508_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__507_value)}};
static const lean_object* l_main___closed__508 = (const lean_object*)&l_main___closed__508_value;
static const lean_string_object l_main___closed__509_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "raw_roundtrip"};
static const lean_object* l_main___closed__509 = (const lean_object*)&l_main___closed__509_value;
static const lean_ctor_object l_main___closed__510_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__510_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__510_value_aux_0),((lean_object*)&l_main___closed__509_value),LEAN_SCALAR_PTR_LITERAL(60, 253, 249, 220, 217, 236, 38, 246)}};
static const lean_object* l_main___closed__510 = (const lean_object*)&l_main___closed__510_value;
static const lean_string_object l_main___closed__511_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stage_roundtrip"};
static const lean_object* l_main___closed__511 = (const lean_object*)&l_main___closed__511_value;
static const lean_ctor_object l_main___closed__512_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__512_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__512_value_aux_0),((lean_object*)&l_main___closed__511_value),LEAN_SCALAR_PTR_LITERAL(152, 12, 56, 67, 80, 225, 220, 25)}};
static const lean_object* l_main___closed__512 = (const lean_object*)&l_main___closed__512_value;
static const lean_string_object l_main___closed__513_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rem"};
static const lean_object* l_main___closed__513 = (const lean_object*)&l_main___closed__513_value;
static const lean_ctor_object l_main___closed__514_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__514_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__514_value_aux_0),((lean_object*)&l_main___closed__513_value),LEAN_SCALAR_PTR_LITERAL(241, 188, 77, 34, 32, 194, 245, 40)}};
static const lean_object* l_main___closed__514 = (const lean_object*)&l_main___closed__514_value;
static const lean_ctor_object l_main___closed__515_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__515_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__515_value_aux_0),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(220, 0, 167, 28, 35, 101, 34, 57)}};
static const lean_object* l_main___closed__515 = (const lean_object*)&l_main___closed__515_value;
static const lean_ctor_object l_main___closed__516_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__506_value),LEAN_SCALAR_PTR_LITERAL(178, 216, 93, 71, 64, 183, 124, 146)}};
static const lean_ctor_object l_main___closed__516_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__516_value_aux_0),((lean_object*)&l_main___closed__199_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 89, 184, 18, 128, 138, 188)}};
static const lean_object* l_main___closed__516 = (const lean_object*)&l_main___closed__516_value;
static const lean_array_object l_main___closed__517_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l_main___closed__510_value),((lean_object*)&l_main___closed__512_value),((lean_object*)&l_main___closed__514_value),((lean_object*)&l_main___closed__515_value),((lean_object*)&l_main___closed__516_value)}};
static const lean_object* l_main___closed__517 = (const lean_object*)&l_main___closed__517_value;
static const lean_string_object l_main___closed__518_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NEV_PrefixPacket"};
static const lean_object* l_main___closed__518 = (const lean_object*)&l_main___closed__518_value;
static const lean_ctor_object l_main___closed__519_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__518_value),LEAN_SCALAR_PTR_LITERAL(190, 35, 47, 34, 121, 137, 20, 202)}};
static const lean_object* l_main___closed__519 = (const lean_object*)&l_main___closed__519_value;
static const lean_array_object l_main___closed__520_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__519_value)}};
static const lean_object* l_main___closed__520 = (const lean_object*)&l_main___closed__520_value;
static const lean_ctor_object l_main___closed__521_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__518_value),LEAN_SCALAR_PTR_LITERAL(190, 35, 47, 34, 121, 137, 20, 202)}};
static const lean_ctor_object l_main___closed__521_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__521_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(40, 185, 223, 173, 239, 123, 175, 247)}};
static const lean_object* l_main___closed__521 = (const lean_object*)&l_main___closed__521_value;
static const lean_array_object l_main___closed__522_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__521_value)}};
static const lean_object* l_main___closed__522 = (const lean_object*)&l_main___closed__522_value;
static const lean_string_object l_main___closed__523_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NEV_PrefixFinalAudit"};
static const lean_object* l_main___closed__523 = (const lean_object*)&l_main___closed__523_value;
static const lean_ctor_object l_main___closed__524_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__523_value),LEAN_SCALAR_PTR_LITERAL(147, 22, 159, 116, 125, 64, 167, 66)}};
static const lean_object* l_main___closed__524 = (const lean_object*)&l_main___closed__524_value;
static const lean_array_object l_main___closed__525_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__524_value)}};
static const lean_object* l_main___closed__525 = (const lean_object*)&l_main___closed__525_value;
static const lean_string_object l_main___closed__526_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NEV_PrefixCallerDomain"};
static const lean_object* l_main___closed__526 = (const lean_object*)&l_main___closed__526_value;
static const lean_string_object l_main___closed__527_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "gathered"};
static const lean_object* l_main___closed__527 = (const lean_object*)&l_main___closed__527_value;
static const lean_ctor_object l_main___closed__528_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__526_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_ctor_object l_main___closed__528_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__528_value_aux_0),((lean_object*)&l_main___closed__527_value),LEAN_SCALAR_PTR_LITERAL(65, 20, 44, 251, 229, 16, 29, 168)}};
static const lean_object* l_main___closed__528 = (const lean_object*)&l_main___closed__528_value;
static const lean_string_object l_main___closed__529_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "capacities"};
static const lean_object* l_main___closed__529 = (const lean_object*)&l_main___closed__529_value;
static const lean_ctor_object l_main___closed__530_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__526_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_ctor_object l_main___closed__530_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__530_value_aux_0),((lean_object*)&l_main___closed__529_value),LEAN_SCALAR_PTR_LITERAL(242, 253, 42, 188, 73, 44, 131, 24)}};
static const lean_object* l_main___closed__530 = (const lean_object*)&l_main___closed__530_value;
static const lean_string_object l_main___closed__531_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrefixAssembly"};
static const lean_object* l_main___closed__531 = (const lean_object*)&l_main___closed__531_value;
static const lean_string_object l_main___closed__532_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "windows"};
static const lean_object* l_main___closed__532 = (const lean_object*)&l_main___closed__532_value;
static const lean_ctor_object l_main___closed__533_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__531_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_ctor_object l_main___closed__533_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__533_value_aux_0),((lean_object*)&l_main___closed__532_value),LEAN_SCALAR_PTR_LITERAL(153, 29, 140, 184, 94, 179, 171, 167)}};
static const lean_object* l_main___closed__533 = (const lean_object*)&l_main___closed__533_value;
static const lean_ctor_object l_main___closed__534_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__531_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_ctor_object l_main___closed__534_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__534_value_aux_0),((lean_object*)&l_main___closed__362_value),LEAN_SCALAR_PTR_LITERAL(188, 216, 154, 103, 148, 35, 157, 103)}};
static const lean_object* l_main___closed__534 = (const lean_object*)&l_main___closed__534_value;
static const lean_string_object l_main___closed__535_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NEV_PrefixCapacity"};
static const lean_object* l_main___closed__535 = (const lean_object*)&l_main___closed__535_value;
static const lean_string_object l_main___closed__536_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "representative"};
static const lean_object* l_main___closed__536 = (const lean_object*)&l_main___closed__536_value;
static const lean_ctor_object l_main___closed__537_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__535_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_ctor_object l_main___closed__537_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__537_value_aux_0),((lean_object*)&l_main___closed__536_value),LEAN_SCALAR_PTR_LITERAL(39, 20, 211, 119, 55, 242, 117, 241)}};
static const lean_object* l_main___closed__537 = (const lean_object*)&l_main___closed__537_value;
static const lean_string_object l_main___closed__538_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "partition"};
static const lean_object* l_main___closed__538 = (const lean_object*)&l_main___closed__538_value;
static const lean_ctor_object l_main___closed__539_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__535_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_ctor_object l_main___closed__539_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__539_value_aux_0),((lean_object*)&l_main___closed__538_value),LEAN_SCALAR_PTR_LITERAL(183, 174, 250, 94, 178, 96, 193, 200)}};
static const lean_object* l_main___closed__539 = (const lean_object*)&l_main___closed__539_value;
static const lean_string_object l_main___closed__540_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PrefixCalls"};
static const lean_object* l_main___closed__540 = (const lean_object*)&l_main___closed__540_value;
static const lean_string_object l_main___closed__541_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "m31_site"};
static const lean_object* l_main___closed__541 = (const lean_object*)&l_main___closed__541_value;
static const lean_ctor_object l_main___closed__542_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__540_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__542_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__542_value_aux_0),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(188, 87, 241, 76, 23, 156, 243, 140)}};
static const lean_object* l_main___closed__542 = (const lean_object*)&l_main___closed__542_value;
static const lean_string_object l_main___closed__543_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "member"};
static const lean_object* l_main___closed__543 = (const lean_object*)&l_main___closed__543_value;
static const lean_ctor_object l_main___closed__544_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__540_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__544_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__544_value_aux_0),((lean_object*)&l_main___closed__543_value),LEAN_SCALAR_PTR_LITERAL(230, 96, 109, 118, 155, 225, 9, 50)}};
static const lean_object* l_main___closed__544 = (const lean_object*)&l_main___closed__544_value;
static const lean_string_object l_main___closed__545_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_main___closed__545 = (const lean_object*)&l_main___closed__545_value;
static const lean_ctor_object l_main___closed__546_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__540_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_ctor_object l_main___closed__546_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__546_value_aux_0),((lean_object*)&l_main___closed__545_value),LEAN_SCALAR_PTR_LITERAL(53, 167, 82, 129, 250, 27, 30, 174)}};
static const lean_object* l_main___closed__546 = (const lean_object*)&l_main___closed__546_value;
static const lean_array_object l_main___closed__547_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9, .m_other = 0, .m_tag = 246}, .m_size = 9, .m_capacity = 9, .m_data = {((lean_object*)&l_main___closed__528_value),((lean_object*)&l_main___closed__530_value),((lean_object*)&l_main___closed__533_value),((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__537_value),((lean_object*)&l_main___closed__539_value),((lean_object*)&l_main___closed__542_value),((lean_object*)&l_main___closed__544_value),((lean_object*)&l_main___closed__546_value)}};
static const lean_object* l_main___closed__547 = (const lean_object*)&l_main___closed__547_value;
static const lean_ctor_object l_main___closed__548_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__540_value),LEAN_SCALAR_PTR_LITERAL(246, 94, 242, 78, 85, 50, 197, 167)}};
static const lean_object* l_main___closed__548 = (const lean_object*)&l_main___closed__548_value;
static const lean_array_object l_main___closed__549_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__548_value)}};
static const lean_object* l_main___closed__549 = (const lean_object*)&l_main___closed__549_value;
static const lean_array_object l_main___closed__550_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__542_value),((lean_object*)&l_main___closed__544_value),((lean_object*)&l_main___closed__546_value)}};
static const lean_object* l_main___closed__550 = (const lean_object*)&l_main___closed__550_value;
static const lean_string_object l_main___closed__551_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEV_PrefixAudit"};
static const lean_object* l_main___closed__551 = (const lean_object*)&l_main___closed__551_value;
static const lean_ctor_object l_main___closed__552_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__551_value),LEAN_SCALAR_PTR_LITERAL(206, 122, 37, 162, 153, 117, 162, 16)}};
static const lean_object* l_main___closed__552 = (const lean_object*)&l_main___closed__552_value;
static const lean_array_object l_main___closed__553_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__552_value)}};
static const lean_object* l_main___closed__553 = (const lean_object*)&l_main___closed__553_value;
static const lean_array_object l_main___closed__554_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_main___closed__528_value),((lean_object*)&l_main___closed__530_value),((lean_object*)&l_main___closed__533_value),((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__537_value),((lean_object*)&l_main___closed__539_value)}};
static const lean_object* l_main___closed__554 = (const lean_object*)&l_main___closed__554_value;
static const lean_ctor_object l_main___closed__555_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__526_value),LEAN_SCALAR_PTR_LITERAL(189, 114, 177, 235, 3, 188, 197, 251)}};
static const lean_object* l_main___closed__555 = (const lean_object*)&l_main___closed__555_value;
static const lean_array_object l_main___closed__556_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__555_value)}};
static const lean_object* l_main___closed__556 = (const lean_object*)&l_main___closed__556_value;
static const lean_array_object l_main___closed__557_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__528_value),((lean_object*)&l_main___closed__530_value)}};
static const lean_object* l_main___closed__557 = (const lean_object*)&l_main___closed__557_value;
static const lean_ctor_object l_main___closed__558_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__535_value),LEAN_SCALAR_PTR_LITERAL(28, 11, 13, 208, 184, 3, 6, 66)}};
static const lean_object* l_main___closed__558 = (const lean_object*)&l_main___closed__558_value;
static const lean_array_object l_main___closed__559_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__558_value)}};
static const lean_object* l_main___closed__559 = (const lean_object*)&l_main___closed__559_value;
static const lean_array_object l_main___closed__560_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__537_value),((lean_object*)&l_main___closed__539_value)}};
static const lean_object* l_main___closed__560 = (const lean_object*)&l_main___closed__560_value;
static const lean_ctor_object l_main___closed__561_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__531_value),LEAN_SCALAR_PTR_LITERAL(218, 128, 223, 104, 191, 164, 207, 210)}};
static const lean_object* l_main___closed__561 = (const lean_object*)&l_main___closed__561_value;
static const lean_array_object l_main___closed__562_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__561_value)}};
static const lean_object* l_main___closed__562 = (const lean_object*)&l_main___closed__562_value;
static const lean_array_object l_main___closed__563_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__533_value),((lean_object*)&l_main___closed__534_value)}};
static const lean_object* l_main___closed__563 = (const lean_object*)&l_main___closed__563_value;
static const lean_string_object l_main___closed__564_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__564 = (const lean_object*)&l_main___closed__564_value;
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
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_main___closed__2));
v___x_132_ = l_Lean_FileMap_ofString(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
size_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_136_ = ((size_t)5ULL);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_unsigned_to_nat(32u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_141_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
lean_ctor_set(v___x_141_, 2, v___x_137_);
lean_ctor_set(v___x_141_, 3, v___x_137_);
lean_ctor_set_usize(v___x_141_, 4, v___x_136_);
return v___x_141_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_box(1);
v___x_143_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set(v___x_144_, 2, v___x_142_);
return v___x_144_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = 0;
v___x_1630_ = lean_box_uint32(v___x_1629_);
return v___x_1630_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = 1;
v___x_1632_ = lean_box_uint32(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = 2;
v___x_1634_ = lean_box_uint32(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_main___boxed__const__4(void){
_start:
{
uint32_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = 3;
v___x_1636_ = lean_box_uint32(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l_NFA__MemoryLimit_set();
v___x_1640_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v___y_1642_; lean_object* v_fst_1643_; lean_object* v_snd_1644_; lean_object* v___y_1748_; 
lean_dec_ref_known(v___x_1640_, 1);
if (lean_obj_tag(v_args_1637_) == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = ((lean_object*)(l_main___closed__564));
v___y_1748_ = v___x_1982_;
goto v___jp_1747_;
}
else
{
lean_object* v_head_1983_; 
v_head_1983_ = lean_ctor_get(v_args_1637_, 0);
lean_inc(v_head_1983_);
lean_dec_ref_known(v_args_1637_, 2);
v___y_1748_ = v_head_1983_;
goto v___jp_1747_;
}
v___jp_1641_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_array_get_size(v_fst_1643_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_nat_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint32_t v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1648_ = 1;
v_sz_1649_ = lean_array_size(v_fst_1643_);
v___x_1650_ = ((size_t)0ULL);
lean_inc_ref(v_fst_1643_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v___x_1645_, v_sz_1649_, v___x_1650_, v_fst_1643_);
v___x_1652_ = l_Lean_Options_empty;
v___x_1653_ = 0;
v___x_1654_ = ((lean_object*)(l_main___closed__0));
v___x_1655_ = 2;
v___x_1656_ = lean_box(1);
v___x_1657_ = l_Lean_importModules(v___x_1651_, v___x_1652_, v___x_1653_, v___x_1654_, v___x_1647_, v___x_1648_, v___x_1655_, v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; size_t v_sz_1669_; lean_object* v___x_1670_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = ((lean_object*)(l_main___closed__1));
v___x_1660_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_unsigned_to_nat(1u);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1659_);
lean_ctor_set(v___x_1665_, 1, v___x_1660_);
lean_ctor_set(v___x_1665_, 2, v___x_1646_);
lean_ctor_set(v___x_1665_, 3, v___x_1646_);
lean_ctor_set(v___x_1665_, 4, v___x_1661_);
lean_ctor_set(v___x_1665_, 5, v___x_1662_);
lean_ctor_set(v___x_1665_, 6, v___x_1663_);
lean_ctor_set(v___x_1665_, 7, v___x_1664_);
lean_ctor_set(v___x_1665_, 8, v___x_1662_);
lean_ctor_set(v___x_1665_, 9, v___x_1662_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*10, v___x_1647_);
v___x_1666_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_1667_ = l_Lean_Elab_Command_mkState(v_a_1658_, v___x_1666_, v___x_1652_);
v___x_1668_ = lean_st_mk_ref(v___x_1667_);
v_sz_1669_ = lean_array_size(v_snd_1644_);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___x_1645_, v___y_1642_, v_snd_1644_, v_sz_1669_, v___x_1650_, v___x_1647_, v___x_1665_, v___x_1668_);
lean_dec_ref_known(v___x_1665_, 10);
lean_dec_ref(v___y_1642_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v_messages_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = lean_st_ref_get(v___x_1668_);
lean_dec(v___x_1668_);
v_messages_1673_ = lean_ctor_get(v___x_1672_, 1);
lean_inc_ref(v_messages_1673_);
lean_dec(v___x_1672_);
v___x_1674_ = l_Lean_MessageLog_toList(v_messages_1673_);
lean_dec_ref(v_messages_1673_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_1674_, v___x_1675_);
lean_dec(v___x_1674_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1689_; 
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; 
v_unused_1690_ = lean_ctor_get(v___x_1676_, 0);
lean_dec(v_unused_1690_);
v___x_1678_ = v___x_1676_;
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v___x_1676_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1689_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_unbox(v_a_1671_);
lean_dec(v_a_1671_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = l_main___boxed__const__1;
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_main___boxed__const__2;
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1685_);
v___x_1687_ = v___x_1678_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1671_);
v_a_1691_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1676_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1676_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v___x_1668_);
v_a_1699_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1700_ = l_Lean_Exception_toMessageData(v_a_1699_);
v___x_1701_ = l_Lean_MessageData_toString(v___x_1700_);
v___x_1702_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1701_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1702_, 0);
lean_dec(v_unused_1711_);
v___x_1704_ = v___x_1702_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v___x_1702_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_main___boxed__const__3;
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1702_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1702_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v___y_1642_);
v_a_1720_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1657_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1657_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v___y_1642_);
v___x_1728_ = ((lean_object*)(l_main___closed__7));
v___x_1729_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1738_);
v___x_1731_ = v___x_1729_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1729_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = l_main___boxed__const__4;
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1729_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1729_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_main___closed__8));
v___x_1750_ = lean_string_dec_eq(v___y_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_main___closed__9));
v___x_1752_ = lean_string_dec_eq(v___y_1748_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_main___closed__10));
v___x_1754_ = lean_string_dec_eq(v___y_1748_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = ((lean_object*)(l_main___closed__11));
v___x_1756_ = lean_string_dec_eq(v___y_1748_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_main___closed__12));
v___x_1758_ = lean_string_dec_eq(v___y_1748_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_main___closed__13));
v___x_1760_ = lean_string_dec_eq(v___y_1748_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_main___closed__14));
v___x_1762_ = lean_string_dec_eq(v___y_1748_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_main___closed__15));
v___x_1764_ = lean_string_dec_eq(v___y_1748_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_main___closed__16));
v___x_1766_ = lean_string_dec_eq(v___y_1748_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_main___closed__17));
v___x_1768_ = lean_string_dec_eq(v___y_1748_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_main___closed__18));
v___x_1770_ = lean_string_dec_eq(v___y_1748_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_main___closed__19));
v___x_1772_ = lean_string_dec_eq(v___y_1748_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_main___closed__20));
v___x_1774_ = lean_string_dec_eq(v___y_1748_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_main___closed__21));
v___x_1776_ = lean_string_dec_eq(v___y_1748_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_main___closed__22));
v___x_1778_ = lean_string_dec_eq(v___y_1748_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_main___closed__23));
v___x_1780_ = lean_string_dec_eq(v___y_1748_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_main___closed__24));
v___x_1782_ = lean_string_dec_eq(v___y_1748_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_main___closed__25));
v___x_1784_ = lean_string_dec_eq(v___y_1748_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_main___closed__26));
v___x_1786_ = lean_string_dec_eq(v___y_1748_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_main___closed__27));
v___x_1788_ = lean_string_dec_eq(v___y_1748_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_main___closed__28));
v___x_1790_ = lean_string_dec_eq(v___y_1748_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_main___closed__29));
v___x_1792_ = lean_string_dec_eq(v___y_1748_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_main___closed__30));
v___x_1794_ = lean_string_dec_eq(v___y_1748_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_main___closed__31));
v___x_1796_ = lean_string_dec_eq(v___y_1748_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_main___closed__32));
v___x_1798_ = lean_string_dec_eq(v___y_1748_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_main___closed__33));
v___x_1800_ = lean_string_dec_eq(v___y_1748_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_main___closed__34));
v___x_1802_ = lean_string_dec_eq(v___y_1748_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_main___closed__35));
v___x_1804_ = lean_string_dec_eq(v___y_1748_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_main___closed__36));
v___x_1806_ = lean_string_dec_eq(v___y_1748_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_main___closed__37));
v___x_1808_ = lean_string_dec_eq(v___y_1748_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_main___closed__38));
v___x_1810_ = lean_string_dec_eq(v___y_1748_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_main___closed__39));
v___x_1812_ = lean_string_dec_eq(v___y_1748_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_main___closed__40));
v___x_1814_ = lean_string_dec_eq(v___y_1748_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_main___closed__41));
v___x_1816_ = lean_string_dec_eq(v___y_1748_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_main___closed__42));
v___x_1818_ = lean_string_dec_eq(v___y_1748_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_main___closed__43));
v___x_1820_ = lean_string_dec_eq(v___y_1748_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_main___closed__44));
v___x_1822_ = lean_string_dec_eq(v___y_1748_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_main___closed__45));
v___x_1824_ = lean_string_dec_eq(v___y_1748_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_main___closed__46));
v___x_1826_ = lean_string_dec_eq(v___y_1748_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_main___closed__47));
v___x_1828_ = lean_string_dec_eq(v___y_1748_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_main___closed__48));
v___x_1830_ = lean_string_dec_eq(v___y_1748_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_main___closed__49));
v___x_1832_ = lean_string_dec_eq(v___y_1748_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_main___closed__50));
v___x_1834_ = lean_string_dec_eq(v___y_1748_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_main___closed__51));
v___x_1836_ = lean_string_dec_eq(v___y_1748_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_main___closed__52));
v___x_1838_ = lean_string_dec_eq(v___y_1748_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_main___closed__53));
v___x_1840_ = lean_string_dec_eq(v___y_1748_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_main___closed__54));
v___x_1842_ = lean_string_dec_eq(v___y_1748_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_main___closed__55));
v___x_1844_ = lean_string_dec_eq(v___y_1748_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_main___closed__56));
v___x_1846_ = lean_string_dec_eq(v___y_1748_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_main___closed__57));
v___x_1848_ = lean_string_dec_eq(v___y_1748_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_main___closed__58));
v___x_1850_ = lean_string_dec_eq(v___y_1748_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_main___closed__59));
v___x_1852_ = lean_string_dec_eq(v___y_1748_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_main___closed__60));
v___x_1854_ = lean_string_dec_eq(v___y_1748_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_main___closed__61));
v___x_1856_ = lean_string_dec_eq(v___y_1748_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_main___closed__62));
v___x_1858_ = lean_string_dec_eq(v___y_1748_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_main___closed__63));
v___x_1860_ = lean_string_dec_eq(v___y_1748_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_main___closed__64));
v___x_1862_ = lean_string_dec_eq(v___y_1748_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_main___closed__65));
v___x_1864_ = lean_string_dec_eq(v___y_1748_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = ((lean_object*)(l_main___closed__66));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1865_;
v_snd_1644_ = v___x_1865_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_main___closed__69));
v___x_1867_ = ((lean_object*)(l_main___closed__72));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1866_;
v_snd_1644_ = v___x_1867_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_main___closed__69));
v___x_1869_ = ((lean_object*)(l_main___closed__75));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1868_;
v_snd_1644_ = v___x_1869_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_main___closed__69));
v___x_1871_ = ((lean_object*)(l_main___closed__78));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1870_;
v_snd_1644_ = v___x_1871_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_main___closed__81));
v___x_1873_ = ((lean_object*)(l_main___closed__86));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1872_;
v_snd_1644_ = v___x_1873_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_main___closed__89));
v___x_1875_ = ((lean_object*)(l_main___closed__104));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1874_;
v_snd_1644_ = v___x_1875_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_main___closed__107));
v___x_1877_ = ((lean_object*)(l_main___closed__114));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1876_;
v_snd_1644_ = v___x_1877_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_main___closed__117));
v___x_1879_ = ((lean_object*)(l_main___closed__124));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1878_;
v_snd_1644_ = v___x_1879_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_main___closed__127));
v___x_1881_ = ((lean_object*)(l_main___closed__131));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1880_;
v_snd_1644_ = v___x_1881_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_main___closed__134));
v___x_1883_ = ((lean_object*)(l_main___closed__139));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1882_;
v_snd_1644_ = v___x_1883_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = ((lean_object*)(l_main___closed__142));
v___x_1885_ = ((lean_object*)(l_main___closed__149));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1884_;
v_snd_1644_ = v___x_1885_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_main___closed__152));
v___x_1887_ = ((lean_object*)(l_main___closed__154));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1886_;
v_snd_1644_ = v___x_1887_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = ((lean_object*)(l_main___closed__157));
v___x_1889_ = ((lean_object*)(l_main___closed__160));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1888_;
v_snd_1644_ = v___x_1889_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_main___closed__163));
v___x_1891_ = ((lean_object*)(l_main___closed__167));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1890_;
v_snd_1644_ = v___x_1891_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_main___closed__170));
v___x_1893_ = ((lean_object*)(l_main___closed__173));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1892_;
v_snd_1644_ = v___x_1893_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l_main___closed__69));
v___x_1895_ = ((lean_object*)(l_main___closed__174));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1894_;
v_snd_1644_ = v___x_1895_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_main___closed__177));
v___x_1897_ = ((lean_object*)(l_main___closed__180));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1896_;
v_snd_1644_ = v___x_1897_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_main___closed__183));
v___x_1899_ = ((lean_object*)(l_main___closed__185));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1898_;
v_snd_1644_ = v___x_1899_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_main___closed__188));
v___x_1901_ = ((lean_object*)(l_main___closed__193));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1900_;
v_snd_1644_ = v___x_1901_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_main___closed__196));
v___x_1903_ = ((lean_object*)(l_main___closed__201));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1902_;
v_snd_1644_ = v___x_1903_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_main___closed__204));
v___x_1905_ = ((lean_object*)(l_main___closed__217));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1904_;
v_snd_1644_ = v___x_1905_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_main___closed__220));
v___x_1907_ = ((lean_object*)(l_main___closed__229));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1906_;
v_snd_1644_ = v___x_1907_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_main___closed__232));
v___x_1909_ = ((lean_object*)(l_main___closed__235));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1908_;
v_snd_1644_ = v___x_1909_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l_main___closed__238));
v___x_1911_ = ((lean_object*)(l_main___closed__244));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1910_;
v_snd_1644_ = v___x_1911_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l_main___closed__247));
v___x_1913_ = ((lean_object*)(l_main___closed__250));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1912_;
v_snd_1644_ = v___x_1913_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_main___closed__253));
v___x_1915_ = ((lean_object*)(l_main___closed__257));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1914_;
v_snd_1644_ = v___x_1915_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_main___closed__260));
v___x_1917_ = ((lean_object*)(l_main___closed__264));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1916_;
v_snd_1644_ = v___x_1917_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = ((lean_object*)(l_main___closed__267));
v___x_1919_ = ((lean_object*)(l_main___closed__274));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1918_;
v_snd_1644_ = v___x_1919_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = ((lean_object*)(l_main___closed__277));
v___x_1921_ = ((lean_object*)(l_main___closed__279));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1920_;
v_snd_1644_ = v___x_1921_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_main___closed__282));
v___x_1923_ = ((lean_object*)(l_main___closed__287));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1922_;
v_snd_1644_ = v___x_1923_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_main___closed__290));
v___x_1925_ = ((lean_object*)(l_main___closed__296));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1924_;
v_snd_1644_ = v___x_1925_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = ((lean_object*)(l_main___closed__299));
v___x_1927_ = ((lean_object*)(l_main___closed__302));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1926_;
v_snd_1644_ = v___x_1927_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_main___closed__305));
v___x_1929_ = ((lean_object*)(l_main___closed__319));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1928_;
v_snd_1644_ = v___x_1929_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_main___closed__322));
v___x_1931_ = ((lean_object*)(l_main___closed__328));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1930_;
v_snd_1644_ = v___x_1931_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_main___closed__331));
v___x_1933_ = ((lean_object*)(l_main___closed__346));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1932_;
v_snd_1644_ = v___x_1933_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_main___closed__349));
v___x_1935_ = ((lean_object*)(l_main___closed__353));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1934_;
v_snd_1644_ = v___x_1935_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_main___closed__356));
v___x_1937_ = ((lean_object*)(l_main___closed__358));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1936_;
v_snd_1644_ = v___x_1937_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_main___closed__361));
v___x_1939_ = ((lean_object*)(l_main___closed__366));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1938_;
v_snd_1644_ = v___x_1939_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_main___closed__369));
v___x_1941_ = ((lean_object*)(l_main___closed__374));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1940_;
v_snd_1644_ = v___x_1941_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_main___closed__377));
v___x_1943_ = ((lean_object*)(l_main___closed__382));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1942_;
v_snd_1644_ = v___x_1943_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_main___closed__385));
v___x_1945_ = ((lean_object*)(l_main___closed__392));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1944_;
v_snd_1644_ = v___x_1945_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_main___closed__395));
v___x_1947_ = ((lean_object*)(l_main___closed__400));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1946_;
v_snd_1644_ = v___x_1947_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l_main___closed__403));
v___x_1949_ = ((lean_object*)(l_main___closed__405));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1948_;
v_snd_1644_ = v___x_1949_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = ((lean_object*)(l_main___closed__408));
v___x_1951_ = ((lean_object*)(l_main___closed__413));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1950_;
v_snd_1644_ = v___x_1951_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_main___closed__416));
v___x_1953_ = ((lean_object*)(l_main___closed__419));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1952_;
v_snd_1644_ = v___x_1953_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_main___closed__422));
v___x_1955_ = ((lean_object*)(l_main___closed__441));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1954_;
v_snd_1644_ = v___x_1955_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_main___closed__444));
v___x_1957_ = ((lean_object*)(l_main___closed__451));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1956_;
v_snd_1644_ = v___x_1957_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_main___closed__454));
v___x_1959_ = ((lean_object*)(l_main___closed__461));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1958_;
v_snd_1644_ = v___x_1959_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_main___closed__464));
v___x_1961_ = ((lean_object*)(l_main___closed__493));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1960_;
v_snd_1644_ = v___x_1961_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_main___closed__496));
v___x_1963_ = ((lean_object*)(l_main___closed__502));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1962_;
v_snd_1644_ = v___x_1963_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_main___closed__504));
v___x_1965_ = ((lean_object*)(l_main___closed__505));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1964_;
v_snd_1644_ = v___x_1965_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_main___closed__508));
v___x_1967_ = ((lean_object*)(l_main___closed__517));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1966_;
v_snd_1644_ = v___x_1967_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_main___closed__520));
v___x_1969_ = ((lean_object*)(l_main___closed__522));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1968_;
v_snd_1644_ = v___x_1969_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_main___closed__525));
v___x_1971_ = ((lean_object*)(l_main___closed__547));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1970_;
v_snd_1644_ = v___x_1971_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_main___closed__549));
v___x_1973_ = ((lean_object*)(l_main___closed__550));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1972_;
v_snd_1644_ = v___x_1973_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_main___closed__553));
v___x_1975_ = ((lean_object*)(l_main___closed__554));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1974_;
v_snd_1644_ = v___x_1975_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_main___closed__556));
v___x_1977_ = ((lean_object*)(l_main___closed__557));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1976_;
v_snd_1644_ = v___x_1977_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_main___closed__559));
v___x_1979_ = ((lean_object*)(l_main___closed__560));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1978_;
v_snd_1644_ = v___x_1979_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_main___closed__562));
v___x_1981_ = ((lean_object*)(l_main___closed__563));
v___y_1642_ = v___y_1748_;
v_fst_1643_ = v___x_1980_;
v_snd_1644_ = v___x_1981_;
goto v___jp_1641_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_args_1637_);
v_a_1984_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1640_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1640_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = _lean_main(v_args_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_1995_, lean_object* v_as_x27_1996_, lean_object* v_b_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_1996_, v_b_1997_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_2001_, lean_object* v_as_x27_2002_, lean_object* v_b_2003_, lean_object* v_a_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_2001_, v_as_x27_2002_, v_b_2003_, v_a_2004_);
lean_dec(v_as_x27_2002_);
lean_dec(v_as_2001_);
return v_res_2006_;
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
