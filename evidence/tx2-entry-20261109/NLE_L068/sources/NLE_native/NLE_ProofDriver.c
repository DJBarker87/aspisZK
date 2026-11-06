// Lean compiler output
// Module: NLE_ProofDriver
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof0"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof1"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof2"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof3"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof4"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof5"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof6"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof7"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof8"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_array_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NLE_COMBINED_IMPORT"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_ctor_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__20_value),LEAN_SCALAR_PTR_LITERAL(42, 22, 103, 149, 148, 104, 254, 239)}};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_array_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__21_value)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NLE_SafeCuts"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "common_reply"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_ctor_object l_main___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(104, 30, 207, 229, 172, 218, 214, 134)}};
static const lean_ctor_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__25_value_aux_0),((lean_object*)&l_main___closed__24_value),LEAN_SCALAR_PTR_LITERAL(91, 77, 123, 68, 38, 225, 112, 166)}};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NLE_CallerScope"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "checkpoint"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_ctor_object l_main___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(71, 218, 31, 63, 88, 212, 247, 241)}};
static const lean_ctor_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__28_value_aux_0),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(159, 104, 121, 30, 200, 115, 80, 58)}};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_ctor_object l_main___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(71, 218, 31, 63, 88, 212, 247, 241)}};
static const lean_ctor_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__30_value_aux_0),((lean_object*)&l_main___closed__29_value),LEAN_SCALAR_PTR_LITERAL(79, 153, 251, 102, 239, 78, 164, 78)}};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RPx_Deployed"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deployed"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_ctor_object l_main___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__31_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__34_value_aux_0),((lean_object*)&l_main___closed__32_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 132, 221, 229, 11, 19, 160)}};
static const lean_ctor_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__34_value_aux_1),((lean_object*)&l_main___closed__33_value),LEAN_SCALAR_PTR_LITERAL(170, 12, 223, 81, 221, 8, 194, 27)}};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NKU_ParentFold"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_ctor_object l_main___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__35_value),LEAN_SCALAR_PTR_LITERAL(145, 239, 94, 119, 61, 93, 27, 253)}};
static const lean_ctor_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__37_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(15, 172, 234, 112, 101, 134, 130, 11)}};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cohort"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_ctor_object l_main___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__35_value),LEAN_SCALAR_PTR_LITERAL(145, 239, 94, 119, 61, 93, 27, 253)}};
static const lean_ctor_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__39_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(112, 88, 239, 177, 232, 172, 155, 121)}};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "clauses"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_ctor_object l_main___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__35_value),LEAN_SCALAR_PTR_LITERAL(145, 239, 94, 119, 61, 93, 27, 253)}};
static const lean_ctor_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__41_value_aux_0),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(65, 114, 11, 93, 144, 66, 236, 51)}};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_array_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_main___closed__25_value),((lean_object*)&l_main___closed__28_value),((lean_object*)&l_main___closed__30_value),((lean_object*)&l_main___closed__34_value),((lean_object*)&l_main___closed__37_value),((lean_object*)&l_main___closed__39_value),((lean_object*)&l_main___closed__41_value)}};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_string_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NLE_RouteFold"};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "child_packet"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_ctor_object l_main___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__43_value),LEAN_SCALAR_PTR_LITERAL(116, 211, 20, 32, 95, 9, 17, 42)}};
static const lean_ctor_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__45_value_aux_0),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(227, 211, 171, 89, 188, 14, 93, 89)}};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NLE_NativeTags"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "error_roundtrip"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_ctor_object l_main___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 212, 147, 191, 131, 178, 226, 196)}};
static const lean_ctor_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__48_value_aux_0),((lean_object*)&l_main___closed__47_value),LEAN_SCALAR_PTR_LITERAL(17, 139, 148, 184, 174, 189, 0, 50)}};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "parse_roundtrip"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_ctor_object l_main___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 212, 147, 191, 131, 178, 226, 196)}};
static const lean_ctor_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__50_value_aux_0),((lean_object*)&l_main___closed__49_value),LEAN_SCALAR_PTR_LITERAL(252, 7, 190, 166, 147, 17, 92, 140)}};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "common_roundtrip"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_ctor_object l_main___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 212, 147, 191, 131, 178, 226, 196)}};
static const lean_ctor_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__52_value_aux_0),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(53, 63, 45, 81, 244, 75, 79, 197)}};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_string_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parse_domain"};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_ctor_object l_main___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 212, 147, 191, 131, 178, 226, 196)}};
static const lean_ctor_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__54_value_aux_0),((lean_object*)&l_main___closed__53_value),LEAN_SCALAR_PTR_LITERAL(140, 138, 117, 97, 213, 39, 151, 103)}};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_string_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "common_domain"};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_ctor_object l_main___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(68, 212, 147, 191, 131, 178, 226, 196)}};
static const lean_ctor_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__56_value_aux_0),((lean_object*)&l_main___closed__55_value),LEAN_SCALAR_PTR_LITERAL(174, 202, 4, 34, 233, 45, 30, 254)}};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_string_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "parse_continuation"};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_ctor_object l_main___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(104, 30, 207, 229, 172, 218, 214, 134)}};
static const lean_ctor_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__58_value_aux_0),((lean_object*)&l_main___closed__57_value),LEAN_SCALAR_PTR_LITERAL(140, 58, 229, 143, 184, 6, 168, 60)}};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parse_error"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_ctor_object l_main___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(104, 30, 207, 229, 172, 218, 214, 134)}};
static const lean_ctor_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__60_value_aux_0),((lean_object*)&l_main___closed__59_value),LEAN_SCALAR_PTR_LITERAL(53, 63, 104, 12, 132, 244, 12, 120)}};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_array_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__45_value),((lean_object*)&l_main___closed__48_value),((lean_object*)&l_main___closed__50_value),((lean_object*)&l_main___closed__52_value),((lean_object*)&l_main___closed__54_value),((lean_object*)&l_main___closed__56_value),((lean_object*)&l_main___closed__58_value),((lean_object*)&l_main___closed__60_value)}};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NLE_Wrapper"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "clear_result"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_ctor_object l_main___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(7, 46, 137, 52, 127, 169, 56, 70)}};
static const lean_ctor_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__64_value_aux_0),((lean_object*)&l_main___closed__63_value),LEAN_SCALAR_PTR_LITERAL(180, 169, 58, 81, 95, 9, 200, 155)}};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_string_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NLE_Dispatch"};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_ctor_object l_main___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__65_value),LEAN_SCALAR_PTR_LITERAL(82, 129, 31, 32, 58, 192, 132, 159)}};
static const lean_ctor_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__66_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(16, 25, 49, 167, 144, 65, 251, 103)}};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_string_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "emitted"};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_ctor_object l_main___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__65_value),LEAN_SCALAR_PTR_LITERAL(82, 129, 31, 32, 58, 192, 132, 159)}};
static const lean_ctor_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__68_value_aux_0),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(147, 221, 55, 108, 23, 81, 168, 167)}};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_string_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NLE_Entry"};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_ctor_object l_main___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(38, 153, 116, 151, 95, 139, 64, 75)}};
static const lean_ctor_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__70_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(116, 75, 3, 152, 75, 254, 153, 197)}};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_ctor_object l_main___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(38, 153, 116, 151, 95, 139, 64, 75)}};
static const lean_ctor_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__71_value_aux_0),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(111, 192, 172, 231, 129, 237, 114, 165)}};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_string_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rejected"};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_ctor_object l_main___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(38, 153, 116, 151, 95, 139, 64, 75)}};
static const lean_ctor_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__73_value_aux_0),((lean_object*)&l_main___closed__72_value),LEAN_SCALAR_PTR_LITERAL(36, 200, 96, 62, 213, 184, 215, 248)}};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_string_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "asq8_route"};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_ctor_object l_main___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__43_value),LEAN_SCALAR_PTR_LITERAL(116, 211, 20, 32, 95, 9, 17, 42)}};
static const lean_ctor_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__75_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(79, 11, 65, 5, 24, 77, 108, 186)}};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_string_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "entry"};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_ctor_object l_main___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__43_value),LEAN_SCALAR_PTR_LITERAL(116, 211, 20, 32, 95, 9, 17, 42)}};
static const lean_ctor_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__77_value_aux_0),((lean_object*)&l_main___closed__76_value),LEAN_SCALAR_PTR_LITERAL(51, 234, 0, 77, 213, 21, 145, 211)}};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_array_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__64_value),((lean_object*)&l_main___closed__66_value),((lean_object*)&l_main___closed__68_value),((lean_object*)&l_main___closed__70_value),((lean_object*)&l_main___closed__71_value),((lean_object*)&l_main___closed__73_value),((lean_object*)&l_main___closed__75_value),((lean_object*)&l_main___closed__77_value)}};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_string_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NLE_MapError"};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_string_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "abort"};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_ctor_object l_main___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 108, 150, 120, 94, 92, 73)}};
static const lean_ctor_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__81_value_aux_0),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(89, 157, 112, 167, 22, 220, 235, 250)}};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_string_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "diverge"};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_ctor_object l_main___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 108, 150, 120, 94, 92, 73)}};
static const lean_ctor_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__83_value_aux_0),((lean_object*)&l_main___closed__82_value),LEAN_SCALAR_PTR_LITERAL(204, 155, 116, 185, 209, 63, 142, 101)}};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_string_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NLE_ErrorPrefix"};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_ctor_object l_main___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(249, 197, 5, 177, 237, 3, 78, 166)}};
static const lean_ctor_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__85_value_aux_0),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(194, 61, 10, 10, 105, 163, 191, 72)}};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_ctor_object l_main___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(249, 197, 5, 177, 237, 3, 78, 166)}};
static const lean_ctor_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__86_value_aux_0),((lean_object*)&l_main___closed__82_value),LEAN_SCALAR_PTR_LITERAL(15, 118, 169, 18, 124, 132, 196, 18)}};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_ctor_object l_main___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(249, 197, 5, 177, 237, 3, 78, 166)}};
static const lean_ctor_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__87_value_aux_0),((lean_object*)&l_main___closed__72_value),LEAN_SCALAR_PTR_LITERAL(167, 144, 122, 2, 190, 218, 20, 210)}};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_string_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fold_source"};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_ctor_object l_main___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(7, 46, 137, 52, 127, 169, 56, 70)}};
static const lean_ctor_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__89_value_aux_0),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(208, 170, 142, 247, 91, 192, 22, 73)}};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_string_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "snapshot_frame"};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_ctor_object l_main___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(7, 46, 137, 52, 127, 169, 56, 70)}};
static const lean_ctor_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__91_value_aux_0),((lean_object*)&l_main___closed__90_value),LEAN_SCALAR_PTR_LITERAL(148, 162, 21, 178, 53, 182, 72, 136)}};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_string_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "snapshot_result"};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_ctor_object l_main___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(7, 46, 137, 52, 127, 169, 56, 70)}};
static const lean_ctor_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__93_value_aux_0),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(250, 14, 39, 194, 224, 226, 219, 107)}};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_array_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__81_value),((lean_object*)&l_main___closed__83_value),((lean_object*)&l_main___closed__85_value),((lean_object*)&l_main___closed__86_value),((lean_object*)&l_main___closed__87_value),((lean_object*)&l_main___closed__89_value),((lean_object*)&l_main___closed__91_value),((lean_object*)&l_main___closed__93_value)}};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_string_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NLE_OwnedStep"};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_string_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "emit_result"};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_ctor_object l_main___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_0),((lean_object*)&l_main___closed__96_value),LEAN_SCALAR_PTR_LITERAL(144, 13, 235, 169, 149, 252, 215, 40)}};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_string_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "emit_events"};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_ctor_object l_main___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__99_value_aux_0),((lean_object*)&l_main___closed__98_value),LEAN_SCALAR_PTR_LITERAL(145, 204, 212, 79, 77, 87, 157, 222)}};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_string_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tx2_result"};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_ctor_object l_main___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__101_value_aux_0),((lean_object*)&l_main___closed__100_value),LEAN_SCALAR_PTR_LITERAL(7, 113, 178, 239, 213, 150, 109, 102)}};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "release_observer"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_ctor_object l_main___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(223, 95, 138, 46, 97, 116, 203, 65)}};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_string_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NLE_OwnedFine"};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_string_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "installed"};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_ctor_object l_main___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(255, 169, 118, 194, 206, 21, 181, 21)}};
static const lean_ctor_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_0),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(14, 139, 244, 4, 213, 55, 75, 70)}};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_ctor_object l_main___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(255, 169, 118, 194, 206, 21, 181, 21)}};
static const lean_ctor_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__107_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(193, 165, 254, 66, 221, 50, 46, 222)}};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_string_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "success"};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_ctor_object l_main___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 108, 150, 120, 94, 92, 73)}};
static const lean_ctor_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__109_value_aux_0),((lean_object*)&l_main___closed__108_value),LEAN_SCALAR_PTR_LITERAL(21, 190, 71, 13, 38, 94, 78, 200)}};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rejection"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__79_value),LEAN_SCALAR_PTR_LITERAL(118, 148, 108, 150, 120, 94, 92, 73)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(244, 201, 118, 47, 122, 252, 223, 2)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_array_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__97_value),((lean_object*)&l_main___closed__99_value),((lean_object*)&l_main___closed__101_value),((lean_object*)&l_main___closed__103_value),((lean_object*)&l_main___closed__106_value),((lean_object*)&l_main___closed__107_value),((lean_object*)&l_main___closed__109_value),((lean_object*)&l_main___closed__111_value)}};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_string_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "validate_result"};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_ctor_object l_main___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__114_value_aux_0),((lean_object*)&l_main___closed__113_value),LEAN_SCALAR_PTR_LITERAL(53, 180, 68, 164, 136, 11, 112, 201)}};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_string_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "validate_events"};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_ctor_object l_main___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__116_value_aux_0),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(218, 23, 210, 52, 3, 104, 110, 219)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_string_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof_result"};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_ctor_object l_main___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__118_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(2, 18, 25, 206, 182, 251, 159, 5)}};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_string_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof_events"};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_ctor_object l_main___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__120_value_aux_0),((lean_object*)&l_main___closed__119_value),LEAN_SCALAR_PTR_LITERAL(229, 157, 156, 214, 227, 18, 61, 179)}};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_string_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "checkpoint_result"};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_ctor_object l_main___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__122_value_aux_0),((lean_object*)&l_main___closed__121_value),LEAN_SCALAR_PTR_LITERAL(40, 231, 158, 151, 64, 185, 55, 20)}};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_string_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "checkpoint_events"};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_ctor_object l_main___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__124_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(107, 168, 231, 55, 218, 180, 193, 136)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "encode_result"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_ctor_object l_main___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__126_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(11, 218, 208, 155, 233, 32, 134, 138)}};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_string_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "encode_events"};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_ctor_object l_main___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(110, 68, 140, 85, 162, 215, 236, 227)}};
static const lean_ctor_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_0),((lean_object*)&l_main___closed__127_value),LEAN_SCALAR_PTR_LITERAL(169, 105, 127, 105, 234, 38, 97, 134)}};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_array_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__114_value),((lean_object*)&l_main___closed__116_value),((lean_object*)&l_main___closed__118_value),((lean_object*)&l_main___closed__120_value),((lean_object*)&l_main___closed__122_value),((lean_object*)&l_main___closed__124_value),((lean_object*)&l_main___closed__126_value),((lean_object*)&l_main___closed__128_value)}};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_string_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NLE_ParseInstall"};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_ctor_object l_main___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__130_value),LEAN_SCALAR_PTR_LITERAL(129, 249, 244, 167, 151, 26, 146, 232)}};
static const lean_ctor_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__131_value_aux_0),((lean_object*)&l_main___closed__108_value),LEAN_SCALAR_PTR_LITERAL(174, 101, 15, 12, 117, 202, 205, 25)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_ctor_object l_main___closed__132_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__130_value),LEAN_SCALAR_PTR_LITERAL(129, 249, 244, 167, 151, 26, 146, 232)}};
static const lean_ctor_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__132_value_aux_0),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(228, 204, 52, 110, 228, 100, 189, 237)}};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_string_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NLE_AuthScope"};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_string_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mark_stub_domain"};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_ctor_object l_main___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(11, 196, 103, 113, 238, 116, 96, 237)}};
static const lean_ctor_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__135_value_aux_0),((lean_object*)&l_main___closed__134_value),LEAN_SCALAR_PTR_LITERAL(43, 17, 186, 220, 182, 166, 171, 241)}};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_string_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entered"};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_ctor_object l_main___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(11, 196, 103, 113, 238, 116, 96, 237)}};
static const lean_ctor_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_0),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(77, 53, 117, 228, 138, 164, 229, 17)}};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_ctor_object l_main___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(11, 196, 103, 113, 238, 116, 96, 237)}};
static const lean_ctor_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__138_value_aux_0),((lean_object*)&l_main___closed__55_value),LEAN_SCALAR_PTR_LITERAL(45, 114, 181, 204, 33, 157, 82, 178)}};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_string_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NLE_AuthLiteral"};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_ctor_object l_main___closed__140_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__139_value),LEAN_SCALAR_PTR_LITERAL(197, 48, 93, 19, 216, 5, 243, 208)}};
static const lean_ctor_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__140_value_aux_0),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(220, 128, 82, 132, 110, 133, 252, 63)}};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_string_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NLE_Owned"};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_string_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "errorMap_result"};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_ctor_object l_main___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(248, 179, 21, 16, 20, 239, 108, 124)}};
static const lean_ctor_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__143_value_aux_0),((lean_object*)&l_main___closed__142_value),LEAN_SCALAR_PTR_LITERAL(125, 241, 183, 227, 166, 204, 52, 237)}};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_ctor_object l_main___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(248, 179, 21, 16, 20, 239, 108, 124)}};
static const lean_ctor_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(2, 27, 151, 26, 130, 89, 29, 156)}};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_array_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__131_value),((lean_object*)&l_main___closed__132_value),((lean_object*)&l_main___closed__135_value),((lean_object*)&l_main___closed__137_value),((lean_object*)&l_main___closed__138_value),((lean_object*)&l_main___closed__140_value),((lean_object*)&l_main___closed__143_value),((lean_object*)&l_main___closed__144_value)}};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_string_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NLE_Auth"};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_string_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "parameterized_fold"};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_ctor_object l_main___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_0),((lean_object*)&l_main___closed__147_value),LEAN_SCALAR_PTR_LITERAL(251, 59, 219, 132, 84, 112, 184, 190)}};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_string_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NLE_Length"};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_string_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof_extent"};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_ctor_object l_main___closed__151_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__149_value),LEAN_SCALAR_PTR_LITERAL(186, 94, 161, 249, 250, 190, 164, 136)}};
static const lean_ctor_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__151_value_aux_0),((lean_object*)&l_main___closed__150_value),LEAN_SCALAR_PTR_LITERAL(223, 85, 113, 250, 207, 145, 195, 62)}};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_string_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "validated_length"};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_ctor_object l_main___closed__153_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__149_value),LEAN_SCALAR_PTR_LITERAL(186, 94, 161, 249, 250, 190, 164, 136)}};
static const lean_ctor_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__153_value_aux_0),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(237, 52, 251, 176, 51, 197, 246, 173)}};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_string_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public_extent"};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_ctor_object l_main___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__149_value),LEAN_SCALAR_PTR_LITERAL(186, 94, 161, 249, 250, 190, 164, 136)}};
static const lean_ctor_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__155_value_aux_0),((lean_object*)&l_main___closed__154_value),LEAN_SCALAR_PTR_LITERAL(156, 76, 89, 144, 138, 182, 69, 167)}};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_string_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "public_scope"};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_ctor_object l_main___closed__157_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__149_value),LEAN_SCALAR_PTR_LITERAL(186, 94, 161, 249, 250, 190, 164, 136)}};
static const lean_ctor_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__157_value_aux_0),((lean_object*)&l_main___closed__156_value),LEAN_SCALAR_PTR_LITERAL(69, 52, 46, 151, 203, 5, 122, 253)}};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_string_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NLE_SnapshotClause"};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_string_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "proof_bytes"};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_ctor_object l_main___closed__160_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(101, 16, 192, 137, 189, 246, 145, 245)}};
static const lean_ctor_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__160_value_aux_0),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(43, 253, 6, 194, 31, 105, 87, 137)}};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_string_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "proof_scope"};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_ctor_object l_main___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__158_value),LEAN_SCALAR_PTR_LITERAL(101, 16, 192, 137, 189, 246, 145, 245)}};
static const lean_ctor_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_0),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(94, 29, 31, 75, 86, 24, 57, 139)}};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_string_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NLE_RangeClause"};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_string_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "caller_proof"};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_ctor_object l_main___closed__165_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(249, 14, 240, 133, 230, 223, 254, 122)}};
static const lean_ctor_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__165_value_aux_0),((lean_object*)&l_main___closed__164_value),LEAN_SCALAR_PTR_LITERAL(176, 187, 50, 8, 141, 247, 179, 87)}};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_array_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__148_value),((lean_object*)&l_main___closed__151_value),((lean_object*)&l_main___closed__153_value),((lean_object*)&l_main___closed__155_value),((lean_object*)&l_main___closed__157_value),((lean_object*)&l_main___closed__160_value),((lean_object*)&l_main___closed__162_value),((lean_object*)&l_main___closed__165_value)}};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_string_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parse_result"};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_ctor_object l_main___closed__168_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__168_value_aux_0),((lean_object*)&l_main___closed__167_value),LEAN_SCALAR_PTR_LITERAL(84, 156, 82, 89, 242, 23, 84, 201)}};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_string_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parse_frame"};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_ctor_object l_main___closed__170_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__170_value_aux_0),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(172, 121, 73, 55, 179, 2, 255, 249)}};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_string_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parse_reject"};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_ctor_object l_main___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__172_value_aux_0),((lean_object*)&l_main___closed__171_value),LEAN_SCALAR_PTR_LITERAL(81, 134, 177, 155, 238, 85, 199, 143)}};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_string_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mark_result"};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_ctor_object l_main___closed__174_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__174_value_aux_0),((lean_object*)&l_main___closed__173_value),LEAN_SCALAR_PTR_LITERAL(217, 180, 134, 166, 101, 164, 190, 115)}};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_string_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mark_events"};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_ctor_object l_main___closed__176_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__176_value_aux_0),((lean_object*)&l_main___closed__175_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 183, 168, 248, 60, 72, 41)}};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_string_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "common_result"};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_ctor_object l_main___closed__178_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__178_value_aux_0),((lean_object*)&l_main___closed__177_value),LEAN_SCALAR_PTR_LITERAL(14, 212, 86, 154, 149, 50, 46, 201)}};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_string_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mark_abort"};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_ctor_object l_main___closed__180_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__180_value_aux_0),((lean_object*)&l_main___closed__179_value),LEAN_SCALAR_PTR_LITERAL(226, 213, 106, 87, 168, 80, 73, 137)}};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_ctor_object l_main___closed__181_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 172, 225, 228, 9, 189, 125)}};
static const lean_ctor_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__181_value_aux_0),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(188, 193, 189, 155, 134, 154, 243, 155)}};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_array_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__168_value),((lean_object*)&l_main___closed__170_value),((lean_object*)&l_main___closed__172_value),((lean_object*)&l_main___closed__174_value),((lean_object*)&l_main___closed__176_value),((lean_object*)&l_main___closed__178_value),((lean_object*)&l_main___closed__180_value),((lean_object*)&l_main___closed__181_value)}};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_string_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_ctor_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_string_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_ctor_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__185_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_array_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__184_value),((lean_object*)&l_main___closed__186_value)}};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_string_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_ctor_object l_main___closed__189_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__189_value_aux_0),((lean_object*)&l_main___closed__188_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_string_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_ctor_object l_main___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__191_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_string_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_ctor_object l_main___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_0),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_string_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_ctor_object l_main___closed__195_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__183_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__195_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_string_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_ctor_object l_main___closed__197_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__196_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__197_value_aux_0),((lean_object*)&l_main___closed__188_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_string_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_ctor_object l_main___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__199_value_aux_0),((lean_object*)&l_main___closed__190_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_string_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_ctor_object l_main___closed__201_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__200_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__201_value_aux_0),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_string_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_ctor_object l_main___closed__203_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__203_value_aux_0),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_array_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__189_value),((lean_object*)&l_main___closed__191_value),((lean_object*)&l_main___closed__193_value),((lean_object*)&l_main___closed__195_value),((lean_object*)&l_main___closed__197_value),((lean_object*)&l_main___closed__199_value),((lean_object*)&l_main___closed__201_value),((lean_object*)&l_main___closed__203_value)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_string_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
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
uint32_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 0;
v___x_687_ = lean_box_uint32(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_688_; lean_object* v___x_689_; 
v___x_688_ = 1;
v___x_689_ = lean_box_uint32(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_690_; lean_object* v___x_691_; 
v___x_690_ = 2;
v___x_691_ = lean_box_uint32(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = l_NFA__MemoryLimit_set();
v___x_695_ = ((lean_object*)(l_main___closed__0));
v___x_696_ = l_Lean_findSysroot(v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v___x_698_ = lean_box(0);
v___x_699_ = l_Lean_initSearchPath(v_a_697_, v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; 
lean_dec_ref_known(v___x_699_, 1);
v___x_700_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v___y_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; lean_object* v___y_781_; 
lean_dec_ref_known(v___x_700_, 1);
if (lean_obj_tag(v_args_692_) == 0)
{
lean_object* v___x_823_; 
v___x_823_ = ((lean_object*)(l_main___closed__205));
v___y_781_ = v___x_823_;
goto v___jp_780_;
}
else
{
lean_object* v_head_824_; 
v_head_824_ = lean_ctor_get(v_args_692_, 0);
lean_inc(v_head_824_);
lean_dec_ref_known(v_args_692_, 2);
v___y_781_ = v_head_824_;
goto v___jp_780_;
}
v___jp_701_:
{
size_t v_sz_705_; size_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint32_t v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_sz_705_ = lean_array_size(v_fst_703_);
v___x_706_ = ((size_t)0ULL);
lean_inc_ref(v_fst_703_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_705_, v___x_706_, v_fst_703_);
v___x_708_ = l_Lean_Options_empty;
v___x_709_ = 0;
v___x_710_ = ((lean_object*)(l_main___closed__1));
v___x_711_ = 0;
v___x_712_ = 1;
v___x_713_ = 2;
v___x_714_ = lean_box(1);
v___x_715_ = l_Lean_importModules(v___x_707_, v___x_708_, v___x_709_, v___x_710_, v___x_711_, v___x_712_, v___x_713_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; size_t v_sz_721_; lean_object* v___x_722_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_718_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_719_ = l_Lean_Elab_Command_mkState(v_a_716_, v___x_718_, v___x_708_);
v___x_720_ = lean_st_mk_ref(v___x_719_);
v_sz_721_ = lean_array_size(v_snd_704_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_702_, v_snd_704_, v_sz_721_, v___x_706_, v___x_711_, v___x_717_, v___x_720_);
lean_dec_ref(v___y_702_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v_messages_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_st_ref_get(v___x_720_);
lean_dec(v___x_720_);
v_messages_725_ = lean_ctor_get(v___x_724_, 1);
lean_inc_ref(v_messages_725_);
lean_dec(v___x_724_);
v___x_726_ = l_Lean_MessageLog_toList(v_messages_725_);
lean_dec_ref(v_messages_725_);
v___x_727_ = lean_box(0);
v___x_728_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_726_, v___x_727_);
lean_dec(v___x_726_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_741_; 
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_742_);
v___x_730_ = v___x_728_;
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_741_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
uint8_t v___x_732_; 
v___x_732_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = l_main___boxed__const__1;
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_733_);
v___x_735_ = v___x_730_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = l_main___boxed__const__2;
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_737_);
v___x_739_ = v___x_730_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_723_);
v_a_743_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_728_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_728_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_720_);
v_a_751_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_722_, 1);
v___x_752_ = l_Lean_Exception_toMessageData(v_a_751_);
v___x_753_ = l_Lean_MessageData_toString(v___x_752_);
v___x_754_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_754_, 0);
lean_dec(v_unused_763_);
v___x_756_ = v___x_754_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_dec(v___x_754_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_main___boxed__const__3;
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_a_764_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_754_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_754_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v___y_702_);
v_a_772_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_715_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_715_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
v___jp_780_:
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l_main___closed__9));
v___x_783_ = lean_string_dec_eq(v___y_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_main___closed__10));
v___x_785_ = lean_string_dec_eq(v___y_781_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l_main___closed__11));
v___x_787_ = lean_string_dec_eq(v___y_781_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l_main___closed__12));
v___x_789_ = lean_string_dec_eq(v___y_781_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l_main___closed__13));
v___x_791_ = lean_string_dec_eq(v___y_781_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l_main___closed__14));
v___x_793_ = lean_string_dec_eq(v___y_781_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_main___closed__15));
v___x_795_ = lean_string_dec_eq(v___y_781_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l_main___closed__16));
v___x_797_ = lean_string_dec_eq(v___y_781_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l_main___closed__17));
v___x_799_ = lean_string_dec_eq(v___y_781_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_main___closed__18));
v___x_801_ = lean_string_dec_eq(v___y_781_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_main___closed__19));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_802_;
v_snd_704_ = v___x_802_;
goto v___jp_701_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_main___closed__22));
v___x_804_ = ((lean_object*)(l_main___closed__42));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_803_;
v_snd_704_ = v___x_804_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_main___closed__22));
v___x_806_ = ((lean_object*)(l_main___closed__61));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_805_;
v_snd_704_ = v___x_806_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_main___closed__22));
v___x_808_ = ((lean_object*)(l_main___closed__78));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_807_;
v_snd_704_ = v___x_808_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_main___closed__22));
v___x_810_ = ((lean_object*)(l_main___closed__94));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_809_;
v_snd_704_ = v___x_810_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_main___closed__22));
v___x_812_ = ((lean_object*)(l_main___closed__112));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_811_;
v_snd_704_ = v___x_812_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_main___closed__22));
v___x_814_ = ((lean_object*)(l_main___closed__129));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_813_;
v_snd_704_ = v___x_814_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_main___closed__22));
v___x_816_ = ((lean_object*)(l_main___closed__145));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_815_;
v_snd_704_ = v___x_816_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_main___closed__22));
v___x_818_ = ((lean_object*)(l_main___closed__166));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_817_;
v_snd_704_ = v___x_818_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_main___closed__22));
v___x_820_ = ((lean_object*)(l_main___closed__182));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_819_;
v_snd_704_ = v___x_820_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_main___closed__187));
v___x_822_ = ((lean_object*)(l_main___closed__204));
v___y_702_ = v___y_781_;
v_fst_703_ = v___x_821_;
v_snd_704_ = v___x_822_;
goto v___jp_701_;
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_args_692_);
v_a_825_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_700_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_700_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_args_692_);
v_a_833_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_699_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_699_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_args_692_);
v_a_841_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_696_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_696_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = _lean_main(v_args_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_852_, lean_object* v_as_x27_853_, lean_object* v_b_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_853_, v_b_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_858_, lean_object* v_as_x27_859_, lean_object* v_b_860_, lean_object* v_a_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_858_, v_as_x27_859_, v_b_860_, v_a_861_);
lean_dec(v_as_x27_859_);
lean_dec(v_as_858_);
return v_res_863_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NLE__ProofDriver(uint8_t builtin) {
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
  res = initialize_NLE__ProofDriver(1 /* builtin */);
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
