// Lean compiler output
// Module: NFM_Driver
// Imports: public import Init public meta import Init public import Lean public import NFA_WALKER public import NFA_MemoryLimit
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_NFA__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_main___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__8;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof0"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof1"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof2"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof3"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof4"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof5"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof6"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof7"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof8"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof9"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof10"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof11"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof12"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof13"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof14"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof15"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof16"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof17"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof18"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof19"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof20"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof21"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof22"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof23"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof24"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof25"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof26"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof27"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_string_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof28"};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof29"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_string_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof30"};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof31"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_string_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof32"};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_array_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_ctor_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_ctor_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_array_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__45_value),((lean_object*)&l_main___closed__47_value)}};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_ctor_object l_main___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__50_value_aux_0),((lean_object*)&l_main___closed__49_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_ctor_object l_main___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__52_value_aux_0),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_string_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_ctor_object l_main___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__54_value_aux_0),((lean_object*)&l_main___closed__53_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_string_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_ctor_object l_main___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__56_value_aux_0),((lean_object*)&l_main___closed__55_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_string_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_ctor_object l_main___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__57_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__58_value_aux_0),((lean_object*)&l_main___closed__49_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_ctor_object l_main___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__59_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__60_value_aux_0),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_string_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_ctor_object l_main___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__61_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__62_value_aux_0),((lean_object*)&l_main___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_ctor_object l_main___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__63_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__64_value_aux_0),((lean_object*)&l_main___closed__55_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_array_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__50_value),((lean_object*)&l_main___closed__52_value),((lean_object*)&l_main___closed__54_value),((lean_object*)&l_main___closed__56_value),((lean_object*)&l_main___closed__58_value),((lean_object*)&l_main___closed__60_value),((lean_object*)&l_main___closed__62_value),((lean_object*)&l_main___closed__64_value)}};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_string_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFM_CombinedFinal"};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_ctor_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__66_value),LEAN_SCALAR_PTR_LITERAL(128, 241, 130, 15, 207, 124, 18, 231)}};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_array_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__67_value)}};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_string_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_string_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFM_ProductInstance"};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_string_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tail_law"};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_ctor_object l_main___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__72_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__72_value_aux_1),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(18, 4, 130, 45, 231, 249, 80, 103)}};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_string_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "installed"};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_ctor_object l_main___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__74_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__74_value_aux_1),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(49, 64, 12, 130, 97, 100, 181, 138)}};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_string_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wrapper"};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_ctor_object l_main___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__76_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__76_value_aux_1),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(173, 78, 168, 213, 70, 99, 52, 197)}};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_array_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__72_value),((lean_object*)&l_main___closed__74_value),((lean_object*)&l_main___closed__76_value)}};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_string_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFM_CallDomains"};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_string_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tail_counts"};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_ctor_object l_main___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__80_value_aux_0),((lean_object*)&l_main___closed__78_value),LEAN_SCALAR_PTR_LITERAL(28, 182, 30, 20, 17, 15, 40, 165)}};
static const lean_ctor_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__80_value_aux_1),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(28, 112, 226, 119, 52, 124, 202, 240)}};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_string_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "terminal"};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_ctor_object l_main___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_0),((lean_object*)&l_main___closed__78_value),LEAN_SCALAR_PTR_LITERAL(28, 182, 30, 20, 17, 15, 40, 165)}};
static const lean_ctor_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(110, 28, 239, 55, 39, 140, 216, 27)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_string_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "main_law"};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_ctor_object l_main___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_1),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(91, 92, 160, 243, 255, 19, 254, 98)}};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_array_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__80_value),((lean_object*)&l_main___closed__82_value),((lean_object*)&l_main___closed__84_value)}};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_string_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFM_Span"};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_string_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "window"};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_ctor_object l_main___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__88_value_aux_0),((lean_object*)&l_main___closed__86_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__88_value_aux_1),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(212, 99, 40, 183, 138, 131, 214, 78)}};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_string_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Frames"};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_ctor_object l_main___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__90_value_aux_0),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(87, 248, 228, 255, 233, 2, 254, 94)}};
static const lean_ctor_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__90_value_aux_1),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(191, 246, 200, 55, 1, 85, 150, 96)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sequence"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_ctor_object l_main___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_0),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(87, 248, 228, 255, 233, 2, 254, 94)}};
static const lean_ctor_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_1),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(4, 253, 116, 32, 188, 71, 54, 146)}};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_array_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__88_value),((lean_object*)&l_main___closed__90_value),((lean_object*)&l_main___closed__92_value)}};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_string_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFM_Domains"};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_string_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "slots"};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_ctor_object l_main___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__96_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__96_value_aux_1),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(126, 66, 142, 1, 163, 23, 219, 29)}};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_string_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_ctor_object l_main___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__98_value_aux_0),((lean_object*)&l_main___closed__86_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__98_value_aux_1),((lean_object*)&l_main___closed__97_value),LEAN_SCALAR_PTR_LITERAL(207, 75, 193, 166, 166, 255, 152, 94)}};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_string_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tail"};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_ctor_object l_main___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_0),((lean_object*)&l_main___closed__86_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(175, 160, 152, 99, 169, 9, 74, 195)}};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_array_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__96_value),((lean_object*)&l_main___closed__98_value),((lean_object*)&l_main___closed__100_value)}};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Single"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_string_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "domains"};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_ctor_object l_main___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__104_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__104_value_aux_1),((lean_object*)&l_main___closed__103_value),LEAN_SCALAR_PTR_LITERAL(250, 91, 23, 186, 33, 41, 156, 120)}};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_string_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "limb_cap"};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_ctor_object l_main___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_1),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(109, 216, 106, 241, 154, 201, 222, 223)}};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_string_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sums_reset"};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_ctor_object l_main___closed__108_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__108_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__108_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__108_value_aux_1),((lean_object*)&l_main___closed__107_value),LEAN_SCALAR_PTR_LITERAL(217, 142, 132, 164, 186, 103, 151, 208)}};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_array_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__104_value),((lean_object*)&l_main___closed__106_value),((lean_object*)&l_main___closed__108_value)}};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "main_same"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_1),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(17, 13, 72, 22, 179, 169, 150, 197)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "same"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_ctor_object l_main___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__113_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__113_value_aux_1),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(136, 225, 49, 109, 161, 134, 112, 52)}};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_string_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "emitted"};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_ctor_object l_main___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__115_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__115_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(25, 203, 78, 204, 6, 110, 68, 189)}};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_array_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__111_value),((lean_object*)&l_main___closed__113_value),((lean_object*)&l_main___closed__115_value)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_string_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFM_Cuts"};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "erased"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_ctor_object l_main___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(117, 55, 90, 132, 124, 22, 88, 174)}};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_string_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_ctor_object l_main___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_1),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(183, 69, 1, 228, 233, 22, 164, 235)}};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_string_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abort_prefix"};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_ctor_object l_main___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__123_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__123_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__123_value_aux_1),((lean_object*)&l_main___closed__122_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 251, 208, 222, 37, 175, 67)}};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_array_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__119_value),((lean_object*)&l_main___closed__121_value),((lean_object*)&l_main___closed__123_value)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Thread"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_string_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "advance"};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_ctor_object l_main___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__127_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__127_value_aux_1),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(0, 44, 131, 14, 179, 219, 49, 39)}};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_ctor_object l_main___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__128_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_1),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(248, 15, 109, 66, 111, 241, 252, 39)}};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_string_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "window_erased"};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_ctor_object l_main___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_1),((lean_object*)&l_main___closed__129_value),LEAN_SCALAR_PTR_LITERAL(62, 212, 90, 206, 108, 28, 221, 21)}};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_array_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__127_value),((lean_object*)&l_main___closed__128_value),((lean_object*)&l_main___closed__130_value)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_string_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance4"};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_ctor_object l_main___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__133_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__133_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__133_value_aux_1),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(27, 35, 21, 223, 238, 83, 53, 179)}};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_string_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance5"};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_ctor_object l_main___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__135_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__135_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__135_value_aux_1),((lean_object*)&l_main___closed__134_value),LEAN_SCALAR_PTR_LITERAL(98, 105, 130, 74, 21, 187, 121, 84)}};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_string_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance6"};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_ctor_object l_main___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__137_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_1),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(127, 221, 39, 217, 235, 184, 187, 188)}};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_string_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_ctor_object l_main___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__139_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__139_value_aux_1),((lean_object*)&l_main___closed__138_value),LEAN_SCALAR_PTR_LITERAL(25, 192, 101, 193, 116, 160, 52, 50)}};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_array_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__133_value),((lean_object*)&l_main___closed__135_value),((lean_object*)&l_main___closed__137_value),((lean_object*)&l_main___closed__139_value)}};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_string_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance0"};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_ctor_object l_main___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__142_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__142_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__142_value_aux_1),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(72, 218, 125, 145, 26, 60, 66, 185)}};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_string_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance1"};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_ctor_object l_main___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__144_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_1),((lean_object*)&l_main___closed__143_value),LEAN_SCALAR_PTR_LITERAL(111, 214, 217, 182, 79, 81, 150, 175)}};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_string_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance2"};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_ctor_object l_main___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__146_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_1),((lean_object*)&l_main___closed__145_value),LEAN_SCALAR_PTR_LITERAL(50, 199, 149, 52, 163, 123, 10, 73)}};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_string_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance3"};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_ctor_object l_main___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__148_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_1),((lean_object*)&l_main___closed__147_value),LEAN_SCALAR_PTR_LITERAL(253, 86, 175, 235, 209, 155, 38, 3)}};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_array_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__142_value),((lean_object*)&l_main___closed__144_value),((lean_object*)&l_main___closed__146_value),((lean_object*)&l_main___closed__148_value)}};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_string_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFM_Control"};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_string_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "stopped"};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_ctor_object l_main___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__152_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__152_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__152_value_aux_1),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(38, 222, 9, 153, 75, 54, 109, 149)}};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_string_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFM_InnerControl"};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_string_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_ctor_object l_main___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__155_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__155_value_aux_0),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__155_value_aux_1),((lean_object*)&l_main___closed__154_value),LEAN_SCALAR_PTR_LITERAL(160, 5, 238, 112, 253, 92, 35, 153)}};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_string_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_ctor_object l_main___closed__157_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__157_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__157_value_aux_0),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__157_value_aux_1),((lean_object*)&l_main___closed__156_value),LEAN_SCALAR_PTR_LITERAL(173, 63, 11, 215, 68, 78, 129, 62)}};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_string_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "at_cut"};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_ctor_object l_main___closed__159_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__159_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__159_value_aux_0),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__159_value_aux_1),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(209, 204, 74, 21, 22, 19, 116, 22)}};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_array_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__152_value),((lean_object*)&l_main___closed__155_value),((lean_object*)&l_main___closed__157_value),((lean_object*)&l_main___closed__159_value)}};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_string_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_count"};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_ctor_object l_main___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__162_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_1),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(199, 86, 211, 81, 73, 218, 83, 204)}};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_string_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "state_sequence"};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_ctor_object l_main___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__164_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_1),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(99, 202, 198, 244, 29, 25, 63, 89)}};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_string_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "next_at"};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_ctor_object l_main___closed__166_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__166_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_1),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(224, 38, 147, 240, 112, 154, 134, 154)}};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_string_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "body_at"};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_ctor_object l_main___closed__168_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__168_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__168_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__168_value_aux_1),((lean_object*)&l_main___closed__167_value),LEAN_SCALAR_PTR_LITERAL(111, 47, 23, 243, 133, 137, 78, 242)}};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_array_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__162_value),((lean_object*)&l_main___closed__164_value),((lean_object*)&l_main___closed__166_value),((lean_object*)&l_main___closed__168_value)}};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_string_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next5"};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_ctor_object l_main___closed__171_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__171_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__171_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__171_value_aux_1),((lean_object*)&l_main___closed__170_value),LEAN_SCALAR_PTR_LITERAL(161, 234, 60, 182, 15, 80, 36, 164)}};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_string_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next6"};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_ctor_object l_main___closed__173_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__173_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__173_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__173_value_aux_1),((lean_object*)&l_main___closed__172_value),LEAN_SCALAR_PTR_LITERAL(116, 231, 213, 25, 116, 238, 186, 201)}};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_string_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixed_outer"};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_ctor_object l_main___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__175_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__175_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__175_value_aux_1),((lean_object*)&l_main___closed__174_value),LEAN_SCALAR_PTR_LITERAL(55, 225, 94, 109, 221, 102, 54, 232)}};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_string_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixed_terms"};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_ctor_object l_main___closed__177_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__177_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__177_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__177_value_aux_1),((lean_object*)&l_main___closed__176_value),LEAN_SCALAR_PTR_LITERAL(26, 101, 195, 203, 0, 183, 19, 181)}};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_array_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__171_value),((lean_object*)&l_main___closed__173_value),((lean_object*)&l_main___closed__175_value),((lean_object*)&l_main___closed__177_value)}};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_string_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next1"};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_ctor_object l_main___closed__180_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__180_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__180_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__180_value_aux_1),((lean_object*)&l_main___closed__179_value),LEAN_SCALAR_PTR_LITERAL(64, 26, 212, 95, 77, 191, 199, 40)}};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_string_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next2"};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_ctor_object l_main___closed__182_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__182_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__182_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__182_value_aux_1),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 5, 6, 20, 199, 121, 101)}};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_string_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next3"};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_ctor_object l_main___closed__184_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__184_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__184_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__184_value_aux_1),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(237, 11, 178, 68, 3, 176, 155, 77)}};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_string_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next4"};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_ctor_object l_main___closed__186_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__186_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__186_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__186_value_aux_1),((lean_object*)&l_main___closed__185_value),LEAN_SCALAR_PTR_LITERAL(41, 34, 253, 149, 7, 230, 117, 180)}};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_array_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__180_value),((lean_object*)&l_main___closed__182_value),((lean_object*)&l_main___closed__184_value),((lean_object*)&l_main___closed__186_value)}};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_string_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedStep"};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_string_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "update_replay"};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_ctor_object l_main___closed__190_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__190_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_0),((lean_object*)&l_main___closed__188_value),LEAN_SCALAR_PTR_LITERAL(166, 134, 206, 222, 20, 145, 99, 64)}};
static const lean_ctor_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_1),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(93, 105, 20, 51, 229, 47, 71, 67)}};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_string_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_InnerActual"};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_string_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "canonical_at_cut"};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_ctor_object l_main___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__193_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_0),((lean_object*)&l_main___closed__191_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_1),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(220, 117, 150, 134, 164, 227, 145, 108)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_string_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_TraceResult"};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_string_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_mark"};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_ctor_object l_main___closed__196_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__196_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__196_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__196_value_aux_1),((lean_object*)&l_main___closed__195_value),LEAN_SCALAR_PTR_LITERAL(242, 17, 164, 78, 33, 83, 4, 86)}};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_string_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next0"};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_ctor_object l_main___closed__198_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__198_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__198_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__198_value_aux_1),((lean_object*)&l_main___closed__197_value),LEAN_SCALAR_PTR_LITERAL(8, 19, 179, 5, 66, 208, 134, 192)}};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_array_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__190_value),((lean_object*)&l_main___closed__193_value),((lean_object*)&l_main___closed__196_value),((lean_object*)&l_main___closed__198_value)}};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_string_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_bind"};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_ctor_object l_main___closed__201_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__201_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__201_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__201_value_aux_1),((lean_object*)&l_main___closed__200_value),LEAN_SCALAR_PTR_LITERAL(132, 52, 163, 84, 164, 40, 235, 86)}};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_string_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFF_FullOne"};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_string_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "replay"};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_ctor_object l_main___closed__204_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__204_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_0),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(148, 82, 37, 38, 223, 114, 24, 172)}};
static const lean_ctor_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(182, 129, 194, 232, 243, 17, 14, 137)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_string_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "borrowed_frame"};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
static const lean_ctor_object l_main___closed__206_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__206_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__206_value_aux_0),((lean_object*)&l_main___closed__191_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__206_value_aux_1),((lean_object*)&l_main___closed__205_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 249, 51, 82, 48, 35, 7)}};
static const lean_object* l_main___closed__206 = (const lean_object*)&l_main___closed__206_value;
static const lean_string_object l_main___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_lift"};
static const lean_object* l_main___closed__207 = (const lean_object*)&l_main___closed__207_value;
static const lean_ctor_object l_main___closed__208_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__208_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__208_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__208_value_aux_1),((lean_object*)&l_main___closed__207_value),LEAN_SCALAR_PTR_LITERAL(81, 23, 212, 251, 142, 3, 166, 22)}};
static const lean_object* l_main___closed__208 = (const lean_object*)&l_main___closed__208_value;
static const lean_array_object l_main___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__201_value),((lean_object*)&l_main___closed__204_value),((lean_object*)&l_main___closed__206_value),((lean_object*)&l_main___closed__208_value)}};
static const lean_object* l_main___closed__209 = (const lean_object*)&l_main___closed__209_value;
static const lean_string_object l_main___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFI_FailurePrefixes"};
static const lean_object* l_main___closed__210 = (const lean_object*)&l_main___closed__210_value;
static const lean_string_object l_main___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "trace_prefix"};
static const lean_object* l_main___closed__211 = (const lean_object*)&l_main___closed__211_value;
static const lean_ctor_object l_main___closed__212_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__212_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__212_value_aux_0),((lean_object*)&l_main___closed__210_value),LEAN_SCALAR_PTR_LITERAL(101, 18, 190, 101, 2, 217, 219, 28)}};
static const lean_ctor_object l_main___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__212_value_aux_1),((lean_object*)&l_main___closed__211_value),LEAN_SCALAR_PTR_LITERAL(166, 120, 11, 231, 192, 75, 149, 142)}};
static const lean_object* l_main___closed__212 = (const lean_object*)&l_main___closed__212_value;
static const lean_string_object l_main___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFI_TailTrace"};
static const lean_object* l_main___closed__213 = (const lean_object*)&l_main___closed__213_value;
static const lean_ctor_object l_main___closed__214_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__214_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__214_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(4, 231, 152, 194, 252, 118, 242, 97)}};
static const lean_ctor_object l_main___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__214_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(165, 0, 6, 167, 220, 113, 238, 100)}};
static const lean_object* l_main___closed__214 = (const lean_object*)&l_main___closed__214_value;
static const lean_string_object l_main___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_ReadDomains"};
static const lean_object* l_main___closed__215 = (const lean_object*)&l_main___closed__215_value;
static const lean_string_object l_main___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "selected"};
static const lean_object* l_main___closed__216 = (const lean_object*)&l_main___closed__216_value;
static const lean_ctor_object l_main___closed__217_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__217_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__217_value_aux_0),((lean_object*)&l_main___closed__215_value),LEAN_SCALAR_PTR_LITERAL(20, 16, 99, 141, 245, 60, 73, 254)}};
static const lean_ctor_object l_main___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__217_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(42, 142, 165, 201, 6, 101, 247, 250)}};
static const lean_object* l_main___closed__217 = (const lean_object*)&l_main___closed__217_value;
static const lean_ctor_object l_main___closed__218_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__218_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__218_value_aux_0),((lean_object*)&l_main___closed__191_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__218_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(9, 251, 44, 26, 241, 90, 249, 48)}};
static const lean_object* l_main___closed__218 = (const lean_object*)&l_main___closed__218_value;
static const lean_array_object l_main___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__212_value),((lean_object*)&l_main___closed__214_value),((lean_object*)&l_main___closed__217_value),((lean_object*)&l_main___closed__218_value)}};
static const lean_object* l_main___closed__219 = (const lean_object*)&l_main___closed__219_value;
static const lean_string_object l_main___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_CoreReduction"};
static const lean_object* l_main___closed__220 = (const lean_object*)&l_main___closed__220_value;
static const lean_string_object l_main___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__221 = (const lean_object*)&l_main___closed__221_value;
static const lean_ctor_object l_main___closed__222_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__222_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__222_value_aux_0),((lean_object*)&l_main___closed__220_value),LEAN_SCALAR_PTR_LITERAL(12, 126, 227, 112, 249, 85, 34, 37)}};
static const lean_ctor_object l_main___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__222_value_aux_1),((lean_object*)&l_main___closed__221_value),LEAN_SCALAR_PTR_LITERAL(166, 171, 119, 132, 12, 138, 26, 31)}};
static const lean_object* l_main___closed__222 = (const lean_object*)&l_main___closed__222_value;
static const lean_string_object l_main___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rejected"};
static const lean_object* l_main___closed__223 = (const lean_object*)&l_main___closed__223_value;
static const lean_ctor_object l_main___closed__224_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__224_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_0),((lean_object*)&l_main___closed__210_value),LEAN_SCALAR_PTR_LITERAL(101, 18, 190, 101, 2, 217, 219, 28)}};
static const lean_ctor_object l_main___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_1),((lean_object*)&l_main___closed__223_value),LEAN_SCALAR_PTR_LITERAL(35, 125, 236, 110, 138, 18, 194, 0)}};
static const lean_object* l_main___closed__224 = (const lean_object*)&l_main___closed__224_value;
static const lean_ctor_object l_main___closed__225_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__225_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__225_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(4, 231, 152, 194, 252, 118, 242, 97)}};
static const lean_ctor_object l_main___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__225_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(166, 248, 148, 201, 3, 4, 50, 160)}};
static const lean_object* l_main___closed__225 = (const lean_object*)&l_main___closed__225_value;
static const lean_string_object l_main___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFF_LoggedRaw"};
static const lean_object* l_main___closed__226 = (const lean_object*)&l_main___closed__226_value;
static const lean_string_object l_main___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "headline"};
static const lean_object* l_main___closed__227 = (const lean_object*)&l_main___closed__227_value;
static const lean_ctor_object l_main___closed__228_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__228_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 187, 109, 99, 51, 126, 174)}};
static const lean_ctor_object l_main___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(110, 207, 7, 126, 159, 133, 60, 190)}};
static const lean_object* l_main___closed__228 = (const lean_object*)&l_main___closed__228_value;
static const lean_array_object l_main___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__222_value),((lean_object*)&l_main___closed__224_value),((lean_object*)&l_main___closed__225_value),((lean_object*)&l_main___closed__228_value)}};
static const lean_object* l_main___closed__229 = (const lean_object*)&l_main___closed__229_value;
static const lean_string_object l_main___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_SingleTrace"};
static const lean_object* l_main___closed__230 = (const lean_object*)&l_main___closed__230_value;
static const lean_ctor_object l_main___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__231_value_aux_0),((lean_object*)&l_main___closed__230_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__231_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(61, 26, 157, 130, 170, 242, 171, 144)}};
static const lean_object* l_main___closed__231 = (const lean_object*)&l_main___closed__231_value;
static const lean_string_object l_main___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_main___closed__232 = (const lean_object*)&l_main___closed__232_value;
static const lean_ctor_object l_main___closed__233_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__233_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__233_value_aux_0),((lean_object*)&l_main___closed__215_value),LEAN_SCALAR_PTR_LITERAL(20, 16, 99, 141, 245, 60, 73, 254)}};
static const lean_ctor_object l_main___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__233_value_aux_1),((lean_object*)&l_main___closed__232_value),LEAN_SCALAR_PTR_LITERAL(129, 69, 191, 201, 171, 254, 143, 228)}};
static const lean_object* l_main___closed__233 = (const lean_object*)&l_main___closed__233_value;
static const lean_string_object l_main___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFF_RawLog"};
static const lean_object* l_main___closed__234 = (const lean_object*)&l_main___closed__234_value;
static const lean_string_object l_main___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natural"};
static const lean_object* l_main___closed__235 = (const lean_object*)&l_main___closed__235_value;
static const lean_ctor_object l_main___closed__236_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__236_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__236_value_aux_0),((lean_object*)&l_main___closed__234_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__236_value_aux_1),((lean_object*)&l_main___closed__235_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 234, 141, 227, 195, 71, 191)}};
static const lean_object* l_main___closed__236 = (const lean_object*)&l_main___closed__236_value;
static const lean_ctor_object l_main___closed__237_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__237_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__237_value_aux_0),((lean_object*)&l_main___closed__230_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__237_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(14, 74, 27, 120, 132, 130, 101, 177)}};
static const lean_object* l_main___closed__237 = (const lean_object*)&l_main___closed__237_value;
static const lean_array_object l_main___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__231_value),((lean_object*)&l_main___closed__233_value),((lean_object*)&l_main___closed__236_value),((lean_object*)&l_main___closed__237_value)}};
static const lean_object* l_main___closed__238 = (const lean_object*)&l_main___closed__238_value;
static const lean_string_object l_main___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_LoggedDomains"};
static const lean_object* l_main___closed__239 = (const lean_object*)&l_main___closed__239_value;
static const lean_string_object l_main___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "four"};
static const lean_object* l_main___closed__240 = (const lean_object*)&l_main___closed__240_value;
static const lean_ctor_object l_main___closed__241_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__241_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__241_value_aux_0),((lean_object*)&l_main___closed__239_value),LEAN_SCALAR_PTR_LITERAL(16, 148, 160, 32, 220, 222, 109, 183)}};
static const lean_ctor_object l_main___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__241_value_aux_1),((lean_object*)&l_main___closed__240_value),LEAN_SCALAR_PTR_LITERAL(3, 173, 209, 219, 100, 130, 71, 101)}};
static const lean_object* l_main___closed__241 = (const lean_object*)&l_main___closed__241_value;
static const lean_string_object l_main___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "main_erased"};
static const lean_object* l_main___closed__242 = (const lean_object*)&l_main___closed__242_value;
static const lean_ctor_object l_main___closed__243_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__243_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__243_value_aux_0),((lean_object*)&l_main___closed__230_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__243_value_aux_1),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(78, 226, 209, 160, 249, 49, 177, 170)}};
static const lean_object* l_main___closed__243 = (const lean_object*)&l_main___closed__243_value;
static const lean_ctor_object l_main___closed__244_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__244_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 187, 109, 99, 51, 126, 174)}};
static const lean_ctor_object l_main___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(133, 223, 8, 68, 65, 103, 154, 125)}};
static const lean_object* l_main___closed__244 = (const lean_object*)&l_main___closed__244_value;
static const lean_string_object l_main___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFF_LoggedOne"};
static const lean_object* l_main___closed__245 = (const lean_object*)&l_main___closed__245_value;
static const lean_ctor_object l_main___closed__246_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__246_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__246_value_aux_0),((lean_object*)&l_main___closed__245_value),LEAN_SCALAR_PTR_LITERAL(23, 173, 85, 152, 243, 194, 49, 246)}};
static const lean_ctor_object l_main___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__246_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(161, 83, 95, 14, 109, 100, 11, 2)}};
static const lean_object* l_main___closed__246 = (const lean_object*)&l_main___closed__246_value;
static const lean_array_object l_main___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__241_value),((lean_object*)&l_main___closed__243_value),((lean_object*)&l_main___closed__244_value),((lean_object*)&l_main___closed__246_value)}};
static const lean_object* l_main___closed__247 = (const lean_object*)&l_main___closed__247_value;
static const lean_string_object l_main___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_RawTypedLog"};
static const lean_object* l_main___closed__248 = (const lean_object*)&l_main___closed__248_value;
static const lean_ctor_object l_main___closed__249_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__249_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__249_value_aux_0),((lean_object*)&l_main___closed__248_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__249_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(7, 77, 214, 252, 146, 120, 209, 89)}};
static const lean_object* l_main___closed__249 = (const lean_object*)&l_main___closed__249_value;
static const lean_string_object l_main___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_ProductCall"};
static const lean_object* l_main___closed__250 = (const lean_object*)&l_main___closed__250_value;
static const lean_ctor_object l_main___closed__251_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__251_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__251_value_aux_0),((lean_object*)&l_main___closed__250_value),LEAN_SCALAR_PTR_LITERAL(142, 228, 132, 23, 103, 2, 148, 55)}};
static const lean_ctor_object l_main___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__251_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(148, 182, 96, 132, 240, 142, 198, 70)}};
static const lean_object* l_main___closed__251 = (const lean_object*)&l_main___closed__251_value;
static const lean_string_object l_main___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFI_SingleDomains"};
static const lean_object* l_main___closed__252 = (const lean_object*)&l_main___closed__252_value;
static const lean_string_object l_main___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reached"};
static const lean_object* l_main___closed__253 = (const lean_object*)&l_main___closed__253_value;
static const lean_ctor_object l_main___closed__254_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__254_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__254_value_aux_0),((lean_object*)&l_main___closed__252_value),LEAN_SCALAR_PTR_LITERAL(145, 179, 180, 57, 88, 75, 141, 19)}};
static const lean_ctor_object l_main___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__254_value_aux_1),((lean_object*)&l_main___closed__253_value),LEAN_SCALAR_PTR_LITERAL(135, 62, 207, 187, 220, 244, 159, 114)}};
static const lean_object* l_main___closed__254 = (const lean_object*)&l_main___closed__254_value;
static const lean_ctor_object l_main___closed__255_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__255_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__255_value_aux_0),((lean_object*)&l_main___closed__220_value),LEAN_SCALAR_PTR_LITERAL(12, 126, 227, 112, 249, 85, 34, 37)}};
static const lean_ctor_object l_main___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__255_value_aux_1),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(20, 74, 193, 122, 239, 44, 196, 48)}};
static const lean_object* l_main___closed__255 = (const lean_object*)&l_main___closed__255_value;
static const lean_array_object l_main___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__249_value),((lean_object*)&l_main___closed__251_value),((lean_object*)&l_main___closed__254_value),((lean_object*)&l_main___closed__255_value)}};
static const lean_object* l_main___closed__256 = (const lean_object*)&l_main___closed__256_value;
static const lean_string_object l_main___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFI_OuterTrace"};
static const lean_object* l_main___closed__257 = (const lean_object*)&l_main___closed__257_value;
static const lean_string_object l_main___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "frames"};
static const lean_object* l_main___closed__258 = (const lean_object*)&l_main___closed__258_value;
static const lean_ctor_object l_main___closed__259_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__259_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_0),((lean_object*)&l_main___closed__257_value),LEAN_SCALAR_PTR_LITERAL(8, 118, 2, 4, 86, 237, 27, 215)}};
static const lean_ctor_object l_main___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_1),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(39, 31, 106, 231, 221, 14, 152, 56)}};
static const lean_object* l_main___closed__259 = (const lean_object*)&l_main___closed__259_value;
static const lean_string_object l_main___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedPush"};
static const lean_object* l_main___closed__260 = (const lean_object*)&l_main___closed__260_value;
static const lean_string_object l_main___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public_replay"};
static const lean_object* l_main___closed__261 = (const lean_object*)&l_main___closed__261_value;
static const lean_ctor_object l_main___closed__262_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__262_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__262_value_aux_0),((lean_object*)&l_main___closed__260_value),LEAN_SCALAR_PTR_LITERAL(121, 180, 87, 35, 209, 192, 221, 181)}};
static const lean_ctor_object l_main___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__262_value_aux_1),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(66, 7, 33, 227, 225, 81, 185, 245)}};
static const lean_object* l_main___closed__262 = (const lean_object*)&l_main___closed__262_value;
static const lean_string_object l_main___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedLoop"};
static const lean_object* l_main___closed__263 = (const lean_object*)&l_main___closed__263_value;
static const lean_ctor_object l_main___closed__264_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__264_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__264_value_aux_0),((lean_object*)&l_main___closed__263_value),LEAN_SCALAR_PTR_LITERAL(186, 99, 211, 216, 149, 255, 96, 20)}};
static const lean_ctor_object l_main___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__264_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(48, 73, 57, 165, 103, 103, 36, 175)}};
static const lean_object* l_main___closed__264 = (const lean_object*)&l_main___closed__264_value;
static const lean_string_object l_main___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_PrivateCuts"};
static const lean_object* l_main___closed__265 = (const lean_object*)&l_main___closed__265_value;
static const lean_ctor_object l_main___closed__266_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__266_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__266_value_aux_0),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(189, 98, 135, 203, 147, 60, 89, 216)}};
static const lean_ctor_object l_main___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__266_value_aux_1),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(164, 251, 16, 63, 14, 2, 32, 56)}};
static const lean_object* l_main___closed__266 = (const lean_object*)&l_main___closed__266_value;
static const lean_array_object l_main___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__259_value),((lean_object*)&l_main___closed__262_value),((lean_object*)&l_main___closed__264_value),((lean_object*)&l_main___closed__266_value)}};
static const lean_object* l_main___closed__267 = (const lean_object*)&l_main___closed__267_value;
static const lean_string_object l_main___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_LoggedWrapper"};
static const lean_object* l_main___closed__268 = (const lean_object*)&l_main___closed__268_value;
static const lean_ctor_object l_main___closed__269_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__269_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__269_value_aux_0),((lean_object*)&l_main___closed__268_value),LEAN_SCALAR_PTR_LITERAL(73, 209, 125, 72, 224, 37, 185, 37)}};
static const lean_ctor_object l_main___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__269_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(212, 162, 139, 9, 179, 60, 229, 246)}};
static const lean_object* l_main___closed__269 = (const lean_object*)&l_main___closed__269_value;
static const lean_ctor_object l_main___closed__270_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__270_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__270_value_aux_0),((lean_object*)&l_main___closed__257_value),LEAN_SCALAR_PTR_LITERAL(8, 118, 2, 4, 86, 237, 27, 215)}};
static const lean_ctor_object l_main___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__270_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(234, 179, 17, 19, 116, 77, 238, 75)}};
static const lean_object* l_main___closed__270 = (const lean_object*)&l_main___closed__270_value;
static const lean_string_object l_main___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFF_Cell"};
static const lean_object* l_main___closed__271 = (const lean_object*)&l_main___closed__271_value;
static const lean_string_object l_main___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "primitive_reply"};
static const lean_object* l_main___closed__272 = (const lean_object*)&l_main___closed__272_value;
static const lean_ctor_object l_main___closed__273_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__273_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__273_value_aux_0),((lean_object*)&l_main___closed__271_value),LEAN_SCALAR_PTR_LITERAL(128, 0, 184, 35, 50, 111, 115, 54)}};
static const lean_ctor_object l_main___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__273_value_aux_1),((lean_object*)&l_main___closed__272_value),LEAN_SCALAR_PTR_LITERAL(190, 107, 87, 73, 62, 118, 131, 147)}};
static const lean_object* l_main___closed__273 = (const lean_object*)&l_main___closed__273_value;
static const lean_string_object l_main___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_main___closed__274 = (const lean_object*)&l_main___closed__274_value;
static const lean_ctor_object l_main___closed__275_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__275_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__275_value_aux_0),((lean_object*)&l_main___closed__239_value),LEAN_SCALAR_PTR_LITERAL(16, 148, 160, 32, 220, 222, 109, 183)}};
static const lean_ctor_object l_main___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__275_value_aux_1),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(96, 244, 64, 92, 69, 230, 194, 112)}};
static const lean_object* l_main___closed__275 = (const lean_object*)&l_main___closed__275_value;
static const lean_array_object l_main___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__269_value),((lean_object*)&l_main___closed__270_value),((lean_object*)&l_main___closed__273_value),((lean_object*)&l_main___closed__275_value)}};
static const lean_object* l_main___closed__276 = (const lean_object*)&l_main___closed__276_value;
static const lean_string_object l_main___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "private_replay"};
static const lean_object* l_main___closed__277 = (const lean_object*)&l_main___closed__277_value;
static const lean_ctor_object l_main___closed__278_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__278_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_0),((lean_object*)&l_main___closed__260_value),LEAN_SCALAR_PTR_LITERAL(121, 180, 87, 35, 209, 192, 221, 181)}};
static const lean_ctor_object l_main___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(168, 70, 104, 218, 61, 144, 195, 211)}};
static const lean_object* l_main___closed__278 = (const lean_object*)&l_main___closed__278_value;
static const lean_string_object l_main___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_LoggedEight"};
static const lean_object* l_main___closed__279 = (const lean_object*)&l_main___closed__279_value;
static const lean_ctor_object l_main___closed__280_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__280_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__280_value_aux_0),((lean_object*)&l_main___closed__279_value),LEAN_SCALAR_PTR_LITERAL(68, 120, 197, 213, 127, 179, 11, 77)}};
static const lean_ctor_object l_main___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__280_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(166, 111, 119, 169, 197, 99, 171, 152)}};
static const lean_object* l_main___closed__280 = (const lean_object*)&l_main___closed__280_value;
static const lean_string_object l_main___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFI_OuterCut"};
static const lean_object* l_main___closed__281 = (const lean_object*)&l_main___closed__281_value;
static const lean_ctor_object l_main___closed__282_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__282_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__282_value_aux_0),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 109, 171, 132, 5, 27, 67)}};
static const lean_ctor_object l_main___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__282_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(178, 139, 75, 13, 4, 24, 238, 252)}};
static const lean_object* l_main___closed__282 = (const lean_object*)&l_main___closed__282_value;
static const lean_string_object l_main___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "operands"};
static const lean_object* l_main___closed__283 = (const lean_object*)&l_main___closed__283_value;
static const lean_ctor_object l_main___closed__284_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__284_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__284_value_aux_0),((lean_object*)&l_main___closed__248_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__284_value_aux_1),((lean_object*)&l_main___closed__283_value),LEAN_SCALAR_PTR_LITERAL(135, 66, 146, 168, 212, 42, 105, 225)}};
static const lean_object* l_main___closed__284 = (const lean_object*)&l_main___closed__284_value;
static const lean_array_object l_main___closed__285_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__278_value),((lean_object*)&l_main___closed__280_value),((lean_object*)&l_main___closed__282_value),((lean_object*)&l_main___closed__284_value)}};
static const lean_object* l_main___closed__285 = (const lean_object*)&l_main___closed__285_value;
static const lean_string_object l_main___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_OuterActual"};
static const lean_object* l_main___closed__286 = (const lean_object*)&l_main___closed__286_value;
static const lean_ctor_object l_main___closed__287_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__287_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__287_value_aux_0),((lean_object*)&l_main___closed__286_value),LEAN_SCALAR_PTR_LITERAL(77, 210, 129, 247, 118, 183, 212, 1)}};
static const lean_ctor_object l_main___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__287_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(120, 143, 136, 115, 55, 174, 103, 186)}};
static const lean_object* l_main___closed__287 = (const lean_object*)&l_main___closed__287_value;
static const lean_ctor_object l_main___closed__288_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__288_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__288_value_aux_0),((lean_object*)&l_main___closed__271_value),LEAN_SCALAR_PTR_LITERAL(128, 0, 184, 35, 50, 111, 115, 54)}};
static const lean_ctor_object l_main___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__288_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(18, 252, 70, 209, 2, 116, 227, 57)}};
static const lean_object* l_main___closed__288 = (const lean_object*)&l_main___closed__288_value;
static const lean_string_object l_main___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFE_WrapperBridge"};
static const lean_object* l_main___closed__289 = (const lean_object*)&l_main___closed__289_value;
static const lean_ctor_object l_main___closed__290_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__290_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__290_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(193, 8, 198, 52, 196, 97, 243, 20)}};
static const lean_ctor_object l_main___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__290_value_aux_1),((lean_object*)&l_main___closed__240_value),LEAN_SCALAR_PTR_LITERAL(222, 125, 100, 106, 166, 221, 233, 53)}};
static const lean_object* l_main___closed__290 = (const lean_object*)&l_main___closed__290_value;
static const lean_string_object l_main___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "same_input"};
static const lean_object* l_main___closed__291 = (const lean_object*)&l_main___closed__291_value;
static const lean_ctor_object l_main___closed__292_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__292_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_0),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 109, 171, 132, 5, 27, 67)}};
static const lean_ctor_object l_main___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_1),((lean_object*)&l_main___closed__291_value),LEAN_SCALAR_PTR_LITERAL(64, 132, 157, 37, 89, 91, 248, 180)}};
static const lean_object* l_main___closed__292 = (const lean_object*)&l_main___closed__292_value;
static const lean_array_object l_main___closed__293_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__287_value),((lean_object*)&l_main___closed__288_value),((lean_object*)&l_main___closed__290_value),((lean_object*)&l_main___closed__292_value)}};
static const lean_object* l_main___closed__293 = (const lean_object*)&l_main___closed__293_value;
static const lean_string_object l_main___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cell_replay"};
static const lean_object* l_main___closed__294 = (const lean_object*)&l_main___closed__294_value;
static const lean_ctor_object l_main___closed__295_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__295_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__295_value_aux_0),((lean_object*)&l_main___closed__279_value),LEAN_SCALAR_PTR_LITERAL(68, 120, 197, 213, 127, 179, 11, 77)}};
static const lean_ctor_object l_main___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__295_value_aux_1),((lean_object*)&l_main___closed__294_value),LEAN_SCALAR_PTR_LITERAL(121, 134, 180, 163, 179, 11, 81, 78)}};
static const lean_object* l_main___closed__295 = (const lean_object*)&l_main___closed__295_value;
static const lean_string_object l_main___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFI_OpeningFrame"};
static const lean_object* l_main___closed__296 = (const lean_object*)&l_main___closed__296_value;
static const lean_string_object l_main___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "receiver_and_return_frame"};
static const lean_object* l_main___closed__297 = (const lean_object*)&l_main___closed__297_value;
static const lean_ctor_object l_main___closed__298_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__298_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__298_value_aux_0),((lean_object*)&l_main___closed__296_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__298_value_aux_1),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(54, 192, 35, 244, 227, 237, 210, 15)}};
static const lean_object* l_main___closed__298 = (const lean_object*)&l_main___closed__298_value;
static const lean_ctor_object l_main___closed__299_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__299_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__299_value_aux_0),((lean_object*)&l_main___closed__248_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__299_value_aux_1),((lean_object*)&l_main___closed__232_value),LEAN_SCALAR_PTR_LITERAL(104, 87, 122, 181, 117, 124, 197, 119)}};
static const lean_object* l_main___closed__299 = (const lean_object*)&l_main___closed__299_value;
static const lean_ctor_object l_main___closed__300_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__300_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__300_value_aux_0),((lean_object*)&l_main___closed__268_value),LEAN_SCALAR_PTR_LITERAL(73, 209, 125, 72, 224, 37, 185, 37)}};
static const lean_ctor_object l_main___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__300_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(63, 89, 80, 39, 31, 102, 170, 240)}};
static const lean_object* l_main___closed__300 = (const lean_object*)&l_main___closed__300_value;
static const lean_array_object l_main___closed__301_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__295_value),((lean_object*)&l_main___closed__298_value),((lean_object*)&l_main___closed__299_value),((lean_object*)&l_main___closed__300_value)}};
static const lean_object* l_main___closed__301 = (const lean_object*)&l_main___closed__301_value;
static const lean_string_object l_main___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFF_BaseMultiply"};
static const lean_object* l_main___closed__302 = (const lean_object*)&l_main___closed__302_value;
static const lean_ctor_object l_main___closed__303_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__303_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__303_value_aux_0),((lean_object*)&l_main___closed__302_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__303_value_aux_1),((lean_object*)&l_main___closed__221_value),LEAN_SCALAR_PTR_LITERAL(89, 171, 227, 195, 108, 177, 191, 65)}};
static const lean_object* l_main___closed__303 = (const lean_object*)&l_main___closed__303_value;
static const lean_string_object l_main___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFE_DotBridge"};
static const lean_object* l_main___closed__304 = (const lean_object*)&l_main___closed__304_value;
static const lean_ctor_object l_main___closed__305_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__305_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__305_value_aux_0),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(196, 85, 115, 203, 129, 162, 182, 230)}};
static const lean_ctor_object l_main___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__305_value_aux_1),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(68, 217, 118, 251, 9, 206, 68, 35)}};
static const lean_object* l_main___closed__305 = (const lean_object*)&l_main___closed__305_value;
static const lean_string_object l_main___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arbitrary_complement"};
static const lean_object* l_main___closed__306 = (const lean_object*)&l_main___closed__306_value;
static const lean_ctor_object l_main___closed__307_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__307_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_0),((lean_object*)&l_main___closed__296_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_1),((lean_object*)&l_main___closed__306_value),LEAN_SCALAR_PTR_LITERAL(206, 233, 40, 55, 182, 39, 125, 227)}};
static const lean_object* l_main___closed__307 = (const lean_object*)&l_main___closed__307_value;
static const lean_string_object l_main___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFF_LoggedOuterStep"};
static const lean_object* l_main___closed__308 = (const lean_object*)&l_main___closed__308_value;
static const lean_ctor_object l_main___closed__309_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__309_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__309_value_aux_0),((lean_object*)&l_main___closed__308_value),LEAN_SCALAR_PTR_LITERAL(148, 21, 130, 45, 156, 30, 140, 40)}};
static const lean_ctor_object l_main___closed__309_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__309_value_aux_1),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(50, 126, 68, 84, 237, 125, 113, 195)}};
static const lean_object* l_main___closed__309 = (const lean_object*)&l_main___closed__309_value;
static const lean_array_object l_main___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__303_value),((lean_object*)&l_main___closed__305_value),((lean_object*)&l_main___closed__307_value),((lean_object*)&l_main___closed__309_value)}};
static const lean_object* l_main___closed__310 = (const lean_object*)&l_main___closed__310_value;
static const lean_ctor_object l_main___closed__311_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__311_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__311_value_aux_0),((lean_object*)&l_main___closed__234_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__311_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(14, 152, 225, 79, 207, 165, 40, 65)}};
static const lean_object* l_main___closed__311 = (const lean_object*)&l_main___closed__311_value;
static const lean_string_object l_main___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedTail"};
static const lean_object* l_main___closed__312 = (const lean_object*)&l_main___closed__312_value;
static const lean_ctor_object l_main___closed__313_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__313_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__313_value_aux_0),((lean_object*)&l_main___closed__312_value),LEAN_SCALAR_PTR_LITERAL(207, 173, 189, 88, 177, 37, 16, 19)}};
static const lean_ctor_object l_main___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__313_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(233, 61, 74, 4, 216, 92, 73, 72)}};
static const lean_object* l_main___closed__313 = (const lean_object*)&l_main___closed__313_value;
static const lean_string_object l_main___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "same_heap_frame"};
static const lean_object* l_main___closed__314 = (const lean_object*)&l_main___closed__314_value;
static const lean_ctor_object l_main___closed__315_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__315_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__315_value_aux_0),((lean_object*)&l_main___closed__296_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__315_value_aux_1),((lean_object*)&l_main___closed__314_value),LEAN_SCALAR_PTR_LITERAL(199, 192, 115, 116, 46, 133, 12, 191)}};
static const lean_object* l_main___closed__315 = (const lean_object*)&l_main___closed__315_value;
static const lean_string_object l_main___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFI_WrapperTrace"};
static const lean_object* l_main___closed__316 = (const lean_object*)&l_main___closed__316_value;
static const lean_ctor_object l_main___closed__317_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__317_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__317_value_aux_0),((lean_object*)&l_main___closed__316_value),LEAN_SCALAR_PTR_LITERAL(108, 62, 131, 135, 24, 53, 95, 21)}};
static const lean_ctor_object l_main___closed__317_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__317_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(181, 207, 198, 86, 178, 179, 146, 230)}};
static const lean_object* l_main___closed__317 = (const lean_object*)&l_main___closed__317_value;
static const lean_array_object l_main___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__311_value),((lean_object*)&l_main___closed__313_value),((lean_object*)&l_main___closed__315_value),((lean_object*)&l_main___closed__317_value)}};
static const lean_object* l_main___closed__318 = (const lean_object*)&l_main___closed__318_value;
static const lean_ctor_object l_main___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__319_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_0),((lean_object*)&l_main___closed__308_value),LEAN_SCALAR_PTR_LITERAL(148, 21, 130, 45, 156, 30, 140, 40)}};
static const lean_ctor_object l_main___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_1),((lean_object*)&l_main___closed__154_value),LEAN_SCALAR_PTR_LITERAL(170, 196, 98, 68, 56, 229, 108, 245)}};
static const lean_object* l_main___closed__319 = (const lean_object*)&l_main___closed__319_value;
static const lean_string_object l_main___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_FullWrapper"};
static const lean_object* l_main___closed__320 = (const lean_object*)&l_main___closed__320_value;
static const lean_ctor_object l_main___closed__321_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__321_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_0),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(215, 28, 127, 186, 250, 168, 228, 167)}};
static const lean_ctor_object l_main___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(34, 108, 222, 12, 74, 200, 81, 62)}};
static const lean_object* l_main___closed__321 = (const lean_object*)&l_main___closed__321_value;
static const lean_string_object l_main___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "original_byte"};
static const lean_object* l_main___closed__322 = (const lean_object*)&l_main___closed__322_value;
static const lean_ctor_object l_main___closed__323_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__323_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__323_value_aux_0),((lean_object*)&l_main___closed__296_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__323_value_aux_1),((lean_object*)&l_main___closed__322_value),LEAN_SCALAR_PTR_LITERAL(127, 79, 70, 98, 221, 64, 84, 140)}};
static const lean_object* l_main___closed__323 = (const lean_object*)&l_main___closed__323_value;
static const lean_ctor_object l_main___closed__324_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__324_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__324_value_aux_0),((lean_object*)&l_main___closed__316_value),LEAN_SCALAR_PTR_LITERAL(108, 62, 131, 135, 24, 53, 95, 21)}};
static const lean_ctor_object l_main___closed__324_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__324_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 80, 154, 43, 28, 133, 69)}};
static const lean_object* l_main___closed__324 = (const lean_object*)&l_main___closed__324_value;
static const lean_array_object l_main___closed__325_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__319_value),((lean_object*)&l_main___closed__321_value),((lean_object*)&l_main___closed__323_value),((lean_object*)&l_main___closed__324_value)}};
static const lean_object* l_main___closed__325 = (const lean_object*)&l_main___closed__325_value;
static const lean_string_object l_main___closed__326_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "word_product"};
static const lean_object* l_main___closed__326 = (const lean_object*)&l_main___closed__326_value;
static const lean_ctor_object l_main___closed__327_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__327_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__327_value_aux_0),((lean_object*)&l_main___closed__302_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__327_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__327_value_aux_1),((lean_object*)&l_main___closed__326_value),LEAN_SCALAR_PTR_LITERAL(59, 155, 210, 33, 254, 7, 108, 147)}};
static const lean_object* l_main___closed__327 = (const lean_object*)&l_main___closed__327_value;
static const lean_string_object l_main___closed__328_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RPx_Deployed"};
static const lean_object* l_main___closed__328 = (const lean_object*)&l_main___closed__328_value;
static const lean_string_object l_main___closed__329_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deployed"};
static const lean_object* l_main___closed__329 = (const lean_object*)&l_main___closed__329_value;
static const lean_ctor_object l_main___closed__330_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__330_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__330_value_aux_0),((lean_object*)&l_main___closed__328_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 132, 221, 229, 11, 19, 160)}};
static const lean_ctor_object l_main___closed__330_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__330_value_aux_1),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(170, 12, 223, 81, 221, 8, 194, 27)}};
static const lean_object* l_main___closed__330 = (const lean_object*)&l_main___closed__330_value;
static const lean_string_object l_main___closed__331_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFI_InnerTrace"};
static const lean_object* l_main___closed__331 = (const lean_object*)&l_main___closed__331_value;
static const lean_ctor_object l_main___closed__332_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__332_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__332_value_aux_0),((lean_object*)&l_main___closed__331_value),LEAN_SCALAR_PTR_LITERAL(137, 7, 11, 159, 52, 26, 77, 24)}};
static const lean_ctor_object l_main___closed__332_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__332_value_aux_1),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(18, 176, 48, 207, 229, 245, 223, 227)}};
static const lean_object* l_main___closed__332 = (const lean_object*)&l_main___closed__332_value;
static const lean_string_object l_main___closed__333_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFI_WrapperDomains"};
static const lean_object* l_main___closed__333 = (const lean_object*)&l_main___closed__333_value;
static const lean_ctor_object l_main___closed__334_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__334_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__334_value_aux_0),((lean_object*)&l_main___closed__333_value),LEAN_SCALAR_PTR_LITERAL(25, 232, 182, 77, 28, 85, 252, 251)}};
static const lean_ctor_object l_main___closed__334_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__334_value_aux_1),((lean_object*)&l_main___closed__253_value),LEAN_SCALAR_PTR_LITERAL(95, 174, 230, 152, 166, 73, 36, 117)}};
static const lean_object* l_main___closed__334 = (const lean_object*)&l_main___closed__334_value;
static const lean_array_object l_main___closed__335_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__327_value),((lean_object*)&l_main___closed__330_value),((lean_object*)&l_main___closed__332_value),((lean_object*)&l_main___closed__334_value)}};
static const lean_object* l_main___closed__335 = (const lean_object*)&l_main___closed__335_value;
static const lean_string_object l_main___closed__336_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "same_log"};
static const lean_object* l_main___closed__336 = (const lean_object*)&l_main___closed__336_value;
static const lean_ctor_object l_main___closed__337_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__337_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__337_value_aux_0),((lean_object*)&l_main___closed__234_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__337_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__337_value_aux_1),((lean_object*)&l_main___closed__336_value),LEAN_SCALAR_PTR_LITERAL(116, 64, 109, 93, 5, 183, 193, 164)}};
static const lean_object* l_main___closed__337 = (const lean_object*)&l_main___closed__337_value;
static const lean_ctor_object l_main___closed__338_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__338_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__338_value_aux_0),((lean_object*)&l_main___closed__188_value),LEAN_SCALAR_PTR_LITERAL(166, 134, 206, 222, 20, 145, 99, 64)}};
static const lean_ctor_object l_main___closed__338_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__338_value_aux_1),((lean_object*)&l_main___closed__154_value),LEAN_SCALAR_PTR_LITERAL(112, 206, 112, 91, 179, 105, 101, 83)}};
static const lean_object* l_main___closed__338 = (const lean_object*)&l_main___closed__338_value;
static const lean_ctor_object l_main___closed__339_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__339_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__339_value_aux_0),((lean_object*)&l_main___closed__331_value),LEAN_SCALAR_PTR_LITERAL(137, 7, 11, 159, 52, 26, 77, 24)}};
static const lean_ctor_object l_main___closed__339_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__339_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(255, 45, 228, 219, 214, 7, 132, 57)}};
static const lean_object* l_main___closed__339 = (const lean_object*)&l_main___closed__339_value;
static const lean_string_object l_main___closed__340_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "div_prefix"};
static const lean_object* l_main___closed__340 = (const lean_object*)&l_main___closed__340_value;
static const lean_ctor_object l_main___closed__341_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__341_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__341_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__341_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__341_value_aux_1),((lean_object*)&l_main___closed__340_value),LEAN_SCALAR_PTR_LITERAL(21, 52, 77, 98, 180, 229, 144, 242)}};
static const lean_object* l_main___closed__341 = (const lean_object*)&l_main___closed__341_value;
static const lean_array_object l_main___closed__342_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__337_value),((lean_object*)&l_main___closed__338_value),((lean_object*)&l_main___closed__339_value),((lean_object*)&l_main___closed__341_value)}};
static const lean_object* l_main___closed__342 = (const lean_object*)&l_main___closed__342_value;
static const lean_string_object l_main___closed__343_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFF_LoggedOuterLoop"};
static const lean_object* l_main___closed__343 = (const lean_object*)&l_main___closed__343_value;
static const lean_ctor_object l_main___closed__344_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__344_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__344_value_aux_0),((lean_object*)&l_main___closed__343_value),LEAN_SCALAR_PTR_LITERAL(75, 181, 148, 102, 119, 146, 80, 84)}};
static const lean_ctor_object l_main___closed__344_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__344_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(21, 186, 247, 122, 2, 162, 159, 69)}};
static const lean_object* l_main___closed__344 = (const lean_object*)&l_main___closed__344_value;
static const lean_ctor_object l_main___closed__345_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__345_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__345_value_aux_0),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(215, 28, 127, 186, 250, 168, 228, 167)}};
static const lean_ctor_object l_main___closed__345_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__345_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(225, 72, 246, 189, 106, 159, 81, 158)}};
static const lean_object* l_main___closed__345 = (const lean_object*)&l_main___closed__345_value;
static const lean_string_object l_main___closed__346_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFI_InnerCut"};
static const lean_object* l_main___closed__346 = (const lean_object*)&l_main___closed__346_value;
static const lean_ctor_object l_main___closed__347_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__347_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__347_value_aux_0),((lean_object*)&l_main___closed__346_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 141, 195, 90, 19, 102, 43)}};
static const lean_ctor_object l_main___closed__347_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__347_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(98, 184, 69, 141, 2, 108, 194, 166)}};
static const lean_object* l_main___closed__347 = (const lean_object*)&l_main___closed__347_value;
static const lean_string_object l_main___closed__348_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fail_prefix"};
static const lean_object* l_main___closed__348 = (const lean_object*)&l_main___closed__348_value;
static const lean_ctor_object l_main___closed__349_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__349_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__349_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__349_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__349_value_aux_1),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(148, 52, 2, 203, 44, 199, 228, 14)}};
static const lean_object* l_main___closed__349 = (const lean_object*)&l_main___closed__349_value;
static const lean_array_object l_main___closed__350_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__344_value),((lean_object*)&l_main___closed__345_value),((lean_object*)&l_main___closed__347_value),((lean_object*)&l_main___closed__349_value)}};
static const lean_object* l_main___closed__350 = (const lean_object*)&l_main___closed__350_value;
static const lean_string_object l_main___closed__351_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "product_bound"};
static const lean_object* l_main___closed__351 = (const lean_object*)&l_main___closed__351_value;
static const lean_ctor_object l_main___closed__352_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__352_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_0),((lean_object*)&l_main___closed__302_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__352_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_1),((lean_object*)&l_main___closed__351_value),LEAN_SCALAR_PTR_LITERAL(125, 149, 230, 231, 156, 185, 249, 245)}};
static const lean_object* l_main___closed__352 = (const lean_object*)&l_main___closed__352_value;
static const lean_string_object l_main___closed__353_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFF_QueryProduct"};
static const lean_object* l_main___closed__353 = (const lean_object*)&l_main___closed__353_value;
static const lean_ctor_object l_main___closed__354_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__354_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__354_value_aux_0),((lean_object*)&l_main___closed__353_value),LEAN_SCALAR_PTR_LITERAL(12, 135, 44, 229, 33, 168, 124, 190)}};
static const lean_ctor_object l_main___closed__354_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__354_value_aux_1),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(77, 45, 9, 231, 125, 16, 2, 172)}};
static const lean_object* l_main___closed__354 = (const lean_object*)&l_main___closed__354_value;
static const lean_ctor_object l_main___closed__355_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__355_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__355_value_aux_0),((lean_object*)&l_main___closed__346_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 141, 195, 90, 19, 102, 43)}};
static const lean_ctor_object l_main___closed__355_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__355_value_aux_1),((lean_object*)&l_main___closed__291_value),LEAN_SCALAR_PTR_LITERAL(48, 42, 211, 247, 201, 221, 50, 124)}};
static const lean_object* l_main___closed__355 = (const lean_object*)&l_main___closed__355_value;
static const lean_string_object l_main___closed__356_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_pure"};
static const lean_object* l_main___closed__356 = (const lean_object*)&l_main___closed__356_value;
static const lean_ctor_object l_main___closed__357_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__357_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__357_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__357_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__357_value_aux_1),((lean_object*)&l_main___closed__356_value),LEAN_SCALAR_PTR_LITERAL(0, 54, 162, 74, 223, 242, 248, 137)}};
static const lean_object* l_main___closed__357 = (const lean_object*)&l_main___closed__357_value;
static const lean_array_object l_main___closed__358_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__352_value),((lean_object*)&l_main___closed__354_value),((lean_object*)&l_main___closed__355_value),((lean_object*)&l_main___closed__357_value)}};
static const lean_object* l_main___closed__358 = (const lean_object*)&l_main___closed__358_value;
static const lean_string_object l_main___closed__359_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__359 = (const lean_object*)&l_main___closed__359_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* l_main___boxed__const__3;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v___y_14_, lean_object* v_as_15_, size_t v_sz_16_, size_t v_i_17_, uint8_t v_b_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_snd_23_; uint8_t v___x_28_; lean_object* v_a_30_; 
v___x_28_ = lean_usize_dec_lt(v_i_17_, v_sz_16_);
if (v___x_28_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(v_b_18_);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Command_getRef___redArg(v___y_19_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
v___x_48_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_19_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_quotContext_x3f_49_; lean_object* v_a_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
lean_dec_ref_known(v___x_48_, 1);
v_quotContext_x3f_49_ = lean_ctor_get(v___y_19_, 5);
v_a_50_ = lean_array_uget_borrowed(v_as_15_, v_i_17_);
v___x_51_ = 0;
v___x_52_ = l_Lean_SourceInfo_fromRef(v_a_47_, v___x_51_);
lean_dec(v_a_47_);
if (lean_obj_tag(v_quotContext_x3f_49_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_20_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_dec_ref_known(v___x_72_, 1);
goto v___jp_53_;
}
else
{
lean_object* v_a_73_; 
lean_dec(v___x_52_);
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v_a_30_ = v_a_73_;
goto v___jp_29_;
}
}
else
{
goto v___jp_53_;
}
v___jp_53_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_54_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4));
v___x_55_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5));
lean_inc_n(v___x_52_, 2);
v___x_56_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_52_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6));
v___x_58_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_52_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
lean_inc(v_a_50_);
v___x_59_ = lean_mk_syntax_ident(v_a_50_);
v___x_60_ = l_Lean_Syntax_node3(v___x_52_, v___x_54_, v___x_56_, v___x_58_, v___x_59_);
v___x_61_ = l_Lean_Elab_Command_elabCommand(v___x_60_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref_known(v___x_61_, 1);
v___x_62_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7));
v___x_63_ = lean_string_append(v___x_62_, v___y_14_);
v___x_64_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8));
v___x_65_ = lean_string_append(v___x_63_, v___x_64_);
lean_inc_n(v_a_50_, 2);
v___x_66_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_50_, v___x_28_);
v___x_67_ = lean_string_append(v___x_65_, v___x_66_);
lean_dec_ref(v___x_66_);
v___x_68_ = l_NEP_audit(v_a_50_, v___x_67_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v___x_69_; 
lean_dec_ref_known(v___x_68_, 1);
v___x_69_ = lean_box(v_b_18_);
v_snd_23_ = v___x_69_;
goto v___jp_22_;
}
else
{
lean_object* v_a_70_; 
v_a_70_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_68_, 1);
v_a_30_ = v_a_70_;
goto v___jp_29_;
}
}
else
{
lean_object* v_a_71_; 
v_a_71_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_61_, 1);
v_a_30_ = v_a_71_;
goto v___jp_29_;
}
}
}
else
{
lean_object* v_a_74_; 
lean_dec(v_a_47_);
v_a_74_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_48_, 1);
v_a_30_ = v_a_74_;
goto v___jp_29_;
}
}
else
{
lean_object* v_a_75_; 
v_a_75_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_46_, 1);
v_a_30_ = v_a_75_;
goto v___jp_29_;
}
}
v___jp_22_:
{
size_t v___x_24_; size_t v___x_25_; uint8_t v___x_26_; 
v___x_24_ = ((size_t)1ULL);
v___x_25_ = lean_usize_add(v_i_17_, v___x_24_);
v___x_26_ = lean_unbox(v_snd_23_);
lean_dec(v_snd_23_);
v_i_17_ = v___x_25_;
v_b_18_ = v___x_26_;
goto _start;
}
v___jp_29_:
{
uint8_t v___x_31_; 
v___x_31_ = l_Lean_Exception_isInterrupt(v_a_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_Lean_Exception_toMessageData(v_a_30_);
v___x_33_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_32_, v___y_19_, v___y_20_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v___x_34_; 
lean_dec_ref_known(v___x_33_, 1);
v___x_34_ = lean_box(v___x_28_);
v_snd_23_ = v___x_34_;
goto v___jp_22_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_35_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
else
{
lean_object* v___x_43_; 
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v_a_30_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v___y_76_, lean_object* v_as_77_, lean_object* v_sz_78_, lean_object* v_i_79_, lean_object* v_b_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
size_t v_sz_boxed_84_; size_t v_i_boxed_85_; uint8_t v_b_boxed_86_; lean_object* v_res_87_; 
v_sz_boxed_84_ = lean_unbox_usize(v_sz_78_);
lean_dec(v_sz_78_);
v_i_boxed_85_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_b_boxed_86_ = lean_unbox(v_b_80_);
v_res_87_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_76_, v_as_77_, v_sz_boxed_84_, v_i_boxed_85_, v_b_boxed_86_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_as_77_);
lean_dec_ref(v___y_76_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_88_, size_t v_i_89_, lean_object* v_bs_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_usize_dec_lt(v_i_89_, v_sz_88_);
if (v___x_91_ == 0)
{
return v_bs_90_;
}
else
{
lean_object* v_v_92_; lean_object* v___x_93_; lean_object* v_bs_x27_94_; uint8_t v___x_95_; lean_object* v___x_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; 
v_v_92_ = lean_array_uget(v_bs_90_, v_i_89_);
v___x_93_ = lean_unsigned_to_nat(0u);
v_bs_x27_94_ = lean_array_uset(v_bs_90_, v_i_89_, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_96_, 0, v_v_92_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_91_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1 + 1, v___x_91_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1 + 2, v___x_95_);
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_89_, v___x_97_);
v___x_99_ = lean_array_uset(v_bs_x27_94_, v_i_89_, v___x_96_);
v_i_89_ = v___x_98_;
v_bs_90_ = v___x_99_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_101_, lean_object* v_i_102_, lean_object* v_bs_103_){
_start:
{
size_t v_sz_boxed_104_; size_t v_i_boxed_105_; lean_object* v_res_106_; 
v_sz_boxed_104_ = lean_unbox_usize(v_sz_101_);
lean_dec(v_sz_101_);
v_i_boxed_105_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_104_, v_i_boxed_105_, v_bs_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_as_x27_107_, lean_object* v_b_108_){
_start:
{
if (lean_obj_tag(v_as_x27_107_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v_b_108_);
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v_data_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_head_111_ = lean_ctor_get(v_as_x27_107_, 0);
v_tail_112_ = lean_ctor_get(v_as_x27_107_, 1);
v_data_113_ = lean_ctor_get(v_head_111_, 4);
lean_inc(v_data_113_);
v___x_114_ = l_Lean_MessageData_toString(v_data_113_);
v___x_115_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = lean_box(0);
v_as_x27_107_ = v_tail_112_;
v_b_108_ = v___x_116_;
goto _start;
}
else
{
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_as_x27_118_, lean_object* v_b_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_118_, v_b_119_);
lean_dec(v_as_x27_118_);
return v_res_121_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_main___closed__3));
v___x_128_ = l_Lean_FileMap_ofString(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_129_ = 0;
v___x_130_ = lean_box(0);
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_box(0);
v___x_133_ = lean_box(0);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_136_ = ((lean_object*)(l_main___closed__2));
v___x_137_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
lean_ctor_set(v___x_137_, 2, v___x_134_);
lean_ctor_set(v___x_137_, 3, v___x_134_);
lean_ctor_set(v___x_137_, 4, v___x_133_);
lean_ctor_set(v___x_137_, 5, v___x_132_);
lean_ctor_set(v___x_137_, 6, v___x_131_);
lean_ctor_set(v___x_137_, 7, v___x_130_);
lean_ctor_set(v___x_137_, 8, v___x_132_);
lean_ctor_set(v___x_137_, 9, v___x_132_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*10, v___x_129_);
return v___x_137_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_unsigned_to_nat(32u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_unsigned_to_nat(32u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_146_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_144_);
lean_ctor_set(v___x_146_, 2, v___x_142_);
lean_ctor_set(v___x_146_, 3, v___x_142_);
lean_ctor_set_usize(v___x_146_, 4, v___x_141_);
return v___x_146_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(1);
v___x_148_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
lean_ctor_set(v___x_149_, 2, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = 0;
v___x_1200_ = lean_box_uint32(v___x_1199_);
return v___x_1200_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = 1;
v___x_1202_ = lean_box_uint32(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = 2;
v___x_1204_ = lean_box_uint32(v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = l_NFA__MemoryLimit_set();
v___x_1208_ = ((lean_object*)(l_main___closed__0));
v___x_1209_ = l_Lean_findSysroot(v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_initSearchPath(v_a_1210_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref_known(v___x_1212_, 1);
v___x_1213_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___y_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___y_1294_; 
lean_dec_ref_known(v___x_1213_, 1);
if (lean_obj_tag(v_args_1205_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l_main___closed__359));
v___y_1294_ = v___x_1432_;
goto v___jp_1293_;
}
else
{
lean_object* v_head_1433_; 
v_head_1433_ = lean_ctor_get(v_args_1205_, 0);
lean_inc(v_head_1433_);
lean_dec_ref_known(v_args_1205_, 2);
v___y_1294_ = v_head_1433_;
goto v___jp_1293_;
}
v___jp_1214_:
{
size_t v_sz_1218_; size_t v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint32_t v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; uint8_t v___x_1225_; uint8_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_sz_1218_ = lean_array_size(v_fst_1216_);
v___x_1219_ = ((size_t)0ULL);
lean_inc_ref(v_fst_1216_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_1218_, v___x_1219_, v_fst_1216_);
v___x_1221_ = l_Lean_Options_empty;
v___x_1222_ = 0;
v___x_1223_ = ((lean_object*)(l_main___closed__1));
v___x_1224_ = 0;
v___x_1225_ = 1;
v___x_1226_ = 2;
v___x_1227_ = lean_box(1);
v___x_1228_ = l_Lean_importModules(v___x_1220_, v___x_1221_, v___x_1222_, v___x_1223_, v___x_1224_, v___x_1225_, v___x_1226_, v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; size_t v_sz_1234_; lean_object* v___x_1235_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_1231_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_1232_ = l_Lean_Elab_Command_mkState(v_a_1229_, v___x_1231_, v___x_1221_);
v___x_1233_ = lean_st_mk_ref(v___x_1232_);
v_sz_1234_ = lean_array_size(v_snd_1217_);
v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_1215_, v_snd_1217_, v_sz_1234_, v___x_1219_, v___x_1224_, v___x_1230_, v___x_1233_);
lean_dec_ref(v___y_1215_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v_messages_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = lean_st_ref_get(v___x_1233_);
lean_dec(v___x_1233_);
v_messages_1238_ = lean_ctor_get(v___x_1237_, 1);
lean_inc_ref(v_messages_1238_);
lean_dec(v___x_1237_);
v___x_1239_ = l_Lean_MessageLog_toList(v_messages_1238_);
lean_dec_ref(v_messages_1238_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_1239_, v___x_1240_);
lean_dec(v___x_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1254_; 
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1255_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1254_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_main___boxed__const__1;
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1246_);
v___x_1248_ = v___x_1243_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = l_main___boxed__const__2;
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1250_);
v___x_1252_ = v___x_1243_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1236_);
v_a_1256_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1241_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1241_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v___x_1233_);
v_a_1264_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1265_ = l_Lean_Exception_toMessageData(v_a_1264_);
v___x_1266_ = l_Lean_MessageData_toString(v___x_1265_);
v___x_1267_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1276_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = l_main___boxed__const__3;
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1267_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1267_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___y_1215_);
v_a_1285_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1228_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1228_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
v___jp_1293_:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_main___closed__9));
v___x_1296_ = lean_string_dec_eq(v___y_1294_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_main___closed__10));
v___x_1298_ = lean_string_dec_eq(v___y_1294_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_main___closed__11));
v___x_1300_ = lean_string_dec_eq(v___y_1294_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_main___closed__12));
v___x_1302_ = lean_string_dec_eq(v___y_1294_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_main___closed__13));
v___x_1304_ = lean_string_dec_eq(v___y_1294_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_main___closed__14));
v___x_1306_ = lean_string_dec_eq(v___y_1294_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_main___closed__15));
v___x_1308_ = lean_string_dec_eq(v___y_1294_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_main___closed__16));
v___x_1310_ = lean_string_dec_eq(v___y_1294_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_main___closed__17));
v___x_1312_ = lean_string_dec_eq(v___y_1294_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_main___closed__18));
v___x_1314_ = lean_string_dec_eq(v___y_1294_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_main___closed__19));
v___x_1316_ = lean_string_dec_eq(v___y_1294_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_main___closed__20));
v___x_1318_ = lean_string_dec_eq(v___y_1294_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_main___closed__21));
v___x_1320_ = lean_string_dec_eq(v___y_1294_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_main___closed__22));
v___x_1322_ = lean_string_dec_eq(v___y_1294_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_main___closed__23));
v___x_1324_ = lean_string_dec_eq(v___y_1294_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_main___closed__24));
v___x_1326_ = lean_string_dec_eq(v___y_1294_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_main___closed__25));
v___x_1328_ = lean_string_dec_eq(v___y_1294_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_main___closed__26));
v___x_1330_ = lean_string_dec_eq(v___y_1294_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_main___closed__27));
v___x_1332_ = lean_string_dec_eq(v___y_1294_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_main___closed__28));
v___x_1334_ = lean_string_dec_eq(v___y_1294_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_main___closed__29));
v___x_1336_ = lean_string_dec_eq(v___y_1294_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_main___closed__30));
v___x_1338_ = lean_string_dec_eq(v___y_1294_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_main___closed__31));
v___x_1340_ = lean_string_dec_eq(v___y_1294_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_main___closed__32));
v___x_1342_ = lean_string_dec_eq(v___y_1294_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_main___closed__33));
v___x_1344_ = lean_string_dec_eq(v___y_1294_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_main___closed__34));
v___x_1346_ = lean_string_dec_eq(v___y_1294_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_main___closed__35));
v___x_1348_ = lean_string_dec_eq(v___y_1294_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_main___closed__36));
v___x_1350_ = lean_string_dec_eq(v___y_1294_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_main___closed__37));
v___x_1352_ = lean_string_dec_eq(v___y_1294_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_main___closed__38));
v___x_1354_ = lean_string_dec_eq(v___y_1294_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_main___closed__39));
v___x_1356_ = lean_string_dec_eq(v___y_1294_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_main___closed__40));
v___x_1358_ = lean_string_dec_eq(v___y_1294_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_main___closed__41));
v___x_1360_ = lean_string_dec_eq(v___y_1294_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_main___closed__42));
v___x_1362_ = lean_string_dec_eq(v___y_1294_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = ((lean_object*)(l_main___closed__43));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1363_;
v_snd_1217_ = v___x_1363_;
goto v___jp_1214_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_main___closed__48));
v___x_1365_ = ((lean_object*)(l_main___closed__65));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1364_;
v_snd_1217_ = v___x_1365_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_main___closed__68));
v___x_1367_ = ((lean_object*)(l_main___closed__77));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1366_;
v_snd_1217_ = v___x_1367_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_main___closed__68));
v___x_1369_ = ((lean_object*)(l_main___closed__85));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1368_;
v_snd_1217_ = v___x_1369_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_main___closed__68));
v___x_1371_ = ((lean_object*)(l_main___closed__93));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1370_;
v_snd_1217_ = v___x_1371_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_main___closed__68));
v___x_1373_ = ((lean_object*)(l_main___closed__101));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1372_;
v_snd_1217_ = v___x_1373_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l_main___closed__68));
v___x_1375_ = ((lean_object*)(l_main___closed__109));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1374_;
v_snd_1217_ = v___x_1375_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_main___closed__68));
v___x_1377_ = ((lean_object*)(l_main___closed__116));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1376_;
v_snd_1217_ = v___x_1377_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_main___closed__68));
v___x_1379_ = ((lean_object*)(l_main___closed__124));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1378_;
v_snd_1217_ = v___x_1379_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_main___closed__68));
v___x_1381_ = ((lean_object*)(l_main___closed__131));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1380_;
v_snd_1217_ = v___x_1381_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_main___closed__68));
v___x_1383_ = ((lean_object*)(l_main___closed__140));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1382_;
v_snd_1217_ = v___x_1383_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_main___closed__68));
v___x_1385_ = ((lean_object*)(l_main___closed__149));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1384_;
v_snd_1217_ = v___x_1385_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = ((lean_object*)(l_main___closed__68));
v___x_1387_ = ((lean_object*)(l_main___closed__160));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1386_;
v_snd_1217_ = v___x_1387_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_main___closed__68));
v___x_1389_ = ((lean_object*)(l_main___closed__169));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1388_;
v_snd_1217_ = v___x_1389_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_main___closed__68));
v___x_1391_ = ((lean_object*)(l_main___closed__178));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1390_;
v_snd_1217_ = v___x_1391_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l_main___closed__68));
v___x_1393_ = ((lean_object*)(l_main___closed__187));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1392_;
v_snd_1217_ = v___x_1393_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_main___closed__68));
v___x_1395_ = ((lean_object*)(l_main___closed__199));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1394_;
v_snd_1217_ = v___x_1395_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_main___closed__68));
v___x_1397_ = ((lean_object*)(l_main___closed__209));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1396_;
v_snd_1217_ = v___x_1397_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_main___closed__68));
v___x_1399_ = ((lean_object*)(l_main___closed__219));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1398_;
v_snd_1217_ = v___x_1399_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_main___closed__68));
v___x_1401_ = ((lean_object*)(l_main___closed__229));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1400_;
v_snd_1217_ = v___x_1401_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_main___closed__68));
v___x_1403_ = ((lean_object*)(l_main___closed__238));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1402_;
v_snd_1217_ = v___x_1403_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l_main___closed__68));
v___x_1405_ = ((lean_object*)(l_main___closed__247));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1404_;
v_snd_1217_ = v___x_1405_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_main___closed__68));
v___x_1407_ = ((lean_object*)(l_main___closed__256));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1406_;
v_snd_1217_ = v___x_1407_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = ((lean_object*)(l_main___closed__68));
v___x_1409_ = ((lean_object*)(l_main___closed__267));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1408_;
v_snd_1217_ = v___x_1409_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_main___closed__68));
v___x_1411_ = ((lean_object*)(l_main___closed__276));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1410_;
v_snd_1217_ = v___x_1411_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_main___closed__68));
v___x_1413_ = ((lean_object*)(l_main___closed__285));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1412_;
v_snd_1217_ = v___x_1413_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_main___closed__68));
v___x_1415_ = ((lean_object*)(l_main___closed__293));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1414_;
v_snd_1217_ = v___x_1415_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_main___closed__68));
v___x_1417_ = ((lean_object*)(l_main___closed__301));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1416_;
v_snd_1217_ = v___x_1417_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_main___closed__68));
v___x_1419_ = ((lean_object*)(l_main___closed__310));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1418_;
v_snd_1217_ = v___x_1419_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_main___closed__68));
v___x_1421_ = ((lean_object*)(l_main___closed__318));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1420_;
v_snd_1217_ = v___x_1421_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_main___closed__68));
v___x_1423_ = ((lean_object*)(l_main___closed__325));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1422_;
v_snd_1217_ = v___x_1423_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_main___closed__68));
v___x_1425_ = ((lean_object*)(l_main___closed__335));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1424_;
v_snd_1217_ = v___x_1425_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_main___closed__68));
v___x_1427_ = ((lean_object*)(l_main___closed__342));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1426_;
v_snd_1217_ = v___x_1427_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_main___closed__68));
v___x_1429_ = ((lean_object*)(l_main___closed__350));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1428_;
v_snd_1217_ = v___x_1429_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_main___closed__68));
v___x_1431_ = ((lean_object*)(l_main___closed__358));
v___y_1215_ = v___y_1294_;
v_fst_1216_ = v___x_1430_;
v_snd_1217_ = v___x_1431_;
goto v___jp_1214_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_args_1205_);
v_a_1434_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1213_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1213_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_args_1205_);
v_a_1442_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1212_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1212_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_args_1205_);
v_a_1450_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1209_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1209_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = _lean_main(v_args_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_1461_, lean_object* v_as_x27_1462_, lean_object* v_b_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_1462_, v_b_1463_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_1467_, lean_object* v_as_x27_1468_, lean_object* v_b_1469_, lean_object* v_a_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_1467_, v_as_x27_1468_, v_b_1469_, v_a_1470_);
lean_dec(v_as_x27_1468_);
lean_dec(v_as_1467_);
return v_res_1472_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFM__Driver(uint8_t builtin) {
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
res = initialize_NFA__WALKER(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NFA__MemoryLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
l_main___boxed__const__3 = _init_l_main___boxed__const__3();
lean_mark_persistent(l_main___boxed__const__3);
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
  res = initialize_NFM__Driver(1 /* builtin */);
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
