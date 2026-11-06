// Lean compiler output
// Module: NJC_ProofDriver
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
static const lean_array_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NJC_COMBINED_IMPORT"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_ctor_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__15_value),LEAN_SCALAR_PTR_LITERAL(3, 48, 99, 52, 107, 108, 5, 168)}};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_array_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__16_value)}};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NJC_ResumeCalls"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "clause"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_ctor_object l_main___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 247, 171, 30, 33, 217, 230, 218)}};
static const lean_ctor_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__20_value_aux_0),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(240, 100, 42, 197, 22, 185, 250, 231)}};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "installed"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_ctor_object l_main___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 247, 171, 30, 33, 217, 230, 218)}};
static const lean_ctor_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__22_value_aux_0),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 30, 121, 63, 12, 225, 22)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 247, 171, 30, 33, 217, 230, 218)}};
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__24_value_aux_0),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(107, 79, 54, 81, 13, 213, 78, 7)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NJC_RawWindows"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_ctor_object l_main___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__25_value),LEAN_SCALAR_PTR_LITERAL(89, 172, 37, 32, 68, 92, 66, 83)}};
static const lean_ctor_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__27_value_aux_0),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(235, 134, 60, 62, 99, 71, 215, 86)}};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_ctor_object l_main___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__25_value),LEAN_SCALAR_PTR_LITERAL(89, 172, 37, 32, 68, 92, 66, 83)}};
static const lean_ctor_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__29_value_aux_0),((lean_object*)&l_main___closed__28_value),LEAN_SCALAR_PTR_LITERAL(16, 18, 103, 129, 71, 178, 76, 222)}};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NJC_OrderedCalls"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mark"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_ctor_object l_main___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(109, 169, 94, 189, 24, 141, 27, 152)}};
static const lean_ctor_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__32_value_aux_0),((lean_object*)&l_main___closed__31_value),LEAN_SCALAR_PTR_LITERAL(229, 164, 11, 229, 163, 35, 100, 110)}};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "powers"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_ctor_object l_main___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(109, 169, 94, 189, 24, 141, 27, 152)}};
static const lean_ctor_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__34_value_aux_0),((lean_object*)&l_main___closed__33_value),LEAN_SCALAR_PTR_LITERAL(222, 85, 122, 15, 89, 165, 160, 141)}};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_ctor_object l_main___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(109, 169, 94, 189, 24, 141, 27, 152)}};
static const lean_ctor_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__35_value_aux_0),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(20, 233, 30, 160, 137, 41, 155, 158)}};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_ctor_object l_main___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(109, 169, 94, 189, 24, 141, 27, 152)}};
static const lean_ctor_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__36_value_aux_0),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(128, 220, 135, 42, 65, 200, 68, 17)}};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_string_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NJC_OptionClause"};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_ctor_object l_main___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__37_value),LEAN_SCALAR_PTR_LITERAL(64, 175, 220, 253, 217, 61, 157, 21)}};
static const lean_ctor_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__39_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(234, 24, 90, 4, 71, 219, 90, 55)}};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "frame"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_ctor_object l_main___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__37_value),LEAN_SCALAR_PTR_LITERAL(64, 175, 220, 253, 217, 61, 157, 21)}};
static const lean_ctor_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__41_value_aux_0),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(173, 103, 4, 18, 251, 149, 221, 74)}};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NJC_ValidateResult"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_string_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_ctor_object l_main___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(33, 222, 186, 55, 113, 20, 214, 178)}};
static const lean_ctor_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__44_value_aux_0),((lean_object*)&l_main___closed__43_value),LEAN_SCALAR_PTR_LITERAL(169, 237, 178, 19, 69, 153, 155, 37)}};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_ctor_object l_main___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(33, 222, 186, 55, 113, 20, 214, 178)}};
static const lean_ctor_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__45_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 180, 143, 240, 189, 24, 135, 176)}};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RPx_Deployed"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_string_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deployed"};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_ctor_object l_main___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__49_value_aux_0),((lean_object*)&l_main___closed__47_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 132, 221, 229, 11, 19, 160)}};
static const lean_ctor_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__49_value_aux_1),((lean_object*)&l_main___closed__48_value),LEAN_SCALAR_PTR_LITERAL(170, 12, 223, 81, 221, 8, 194, 27)}};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_array_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l_main___closed__20_value),((lean_object*)&l_main___closed__22_value),((lean_object*)&l_main___closed__24_value),((lean_object*)&l_main___closed__27_value),((lean_object*)&l_main___closed__29_value),((lean_object*)&l_main___closed__32_value),((lean_object*)&l_main___closed__34_value),((lean_object*)&l_main___closed__35_value),((lean_object*)&l_main___closed__36_value),((lean_object*)&l_main___closed__39_value),((lean_object*)&l_main___closed__41_value),((lean_object*)&l_main___closed__44_value),((lean_object*)&l_main___closed__45_value),((lean_object*)&l_main___closed__49_value)}};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NJC_ValidatePort"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_ctor_object l_main___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(57, 149, 206, 125, 67, 32, 183, 207)}};
static const lean_ctor_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__52_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(215, 243, 42, 223, 172, 232, 181, 246)}};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_ctor_object l_main___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(57, 149, 206, 125, 67, 32, 183, 207)}};
static const lean_ctor_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__53_value_aux_0),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(192, 168, 142, 86, 5, 210, 73, 8)}};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NJC_ValidateCalls"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_ctor_object l_main___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(95, 218, 36, 207, 44, 112, 80, 166)}};
static const lean_ctor_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__55_value_aux_0),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(193, 197, 236, 202, 252, 50, 117, 236)}};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reference"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_ctor_object l_main___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(95, 218, 36, 207, 44, 112, 80, 166)}};
static const lean_ctor_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__57_value_aux_0),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(95, 207, 129, 14, 81, 185, 166, 42)}};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_ctor_object l_main___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(95, 218, 36, 207, 44, 112, 80, 166)}};
static const lean_ctor_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__58_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(161, 76, 114, 48, 172, 93, 83, 111)}};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NJC_FilledClause"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_ctor_object l_main___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__59_value),LEAN_SCALAR_PTR_LITERAL(244, 227, 114, 161, 231, 113, 197, 209)}};
static const lean_ctor_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__61_value_aux_0),((lean_object*)&l_main___closed__60_value),LEAN_SCALAR_PTR_LITERAL(104, 75, 64, 49, 152, 128, 63, 165)}};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_ctor_object l_main___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__59_value),LEAN_SCALAR_PTR_LITERAL(244, 227, 114, 161, 231, 113, 197, 209)}};
static const lean_ctor_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__62_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(174, 4, 129, 234, 126, 97, 59, 157)}};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NJC_RawPort"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transport"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_ctor_object l_main___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__63_value),LEAN_SCALAR_PTR_LITERAL(229, 229, 11, 226, 65, 39, 171, 55)}};
static const lean_ctor_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__65_value_aux_0),((lean_object*)&l_main___closed__64_value),LEAN_SCALAR_PTR_LITERAL(56, 216, 111, 131, 196, 71, 82, 47)}};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_string_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bounded"};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_ctor_object l_main___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__63_value),LEAN_SCALAR_PTR_LITERAL(229, 229, 11, 226, 65, 39, 171, 55)}};
static const lean_ctor_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__67_value_aux_0),((lean_object*)&l_main___closed__66_value),LEAN_SCALAR_PTR_LITERAL(169, 86, 232, 136, 50, 4, 35, 92)}};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_string_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NJC_ScanPartition"};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_string_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "thirty"};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_ctor_object l_main___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(115, 82, 24, 105, 44, 57, 58, 223)}};
static const lean_ctor_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__70_value_aux_0),((lean_object*)&l_main___closed__69_value),LEAN_SCALAR_PTR_LITERAL(132, 94, 84, 17, 68, 33, 57, 137)}};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_string_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "blocks"};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_ctor_object l_main___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(115, 82, 24, 105, 44, 57, 58, 223)}};
static const lean_ctor_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__72_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(111, 72, 190, 26, 83, 180, 206, 113)}};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_string_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "opening"};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_ctor_object l_main___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(115, 82, 24, 105, 44, 57, 58, 223)}};
static const lean_ctor_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__74_value_aux_0),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(178, 93, 67, 99, 104, 68, 13, 219)}};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_string_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NJC_ScanViews"};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_string_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "query"};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_ctor_object l_main___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(124, 117, 60, 235, 163, 17, 240, 39)}};
static const lean_ctor_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__77_value_aux_0),((lean_object*)&l_main___closed__76_value),LEAN_SCALAR_PTR_LITERAL(7, 51, 77, 76, 54, 26, 211, 213)}};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_string_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "subwindow"};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_ctor_object l_main___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(124, 117, 60, 235, 163, 17, 240, 39)}};
static const lean_ctor_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__79_value_aux_0),((lean_object*)&l_main___closed__78_value),LEAN_SCALAR_PTR_LITERAL(83, 7, 162, 24, 18, 255, 60, 142)}};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_string_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "final"};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_ctor_object l_main___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(124, 117, 60, 235, 163, 17, 240, 39)}};
static const lean_ctor_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__81_value_aux_0),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(133, 21, 238, 202, 166, 117, 155, 72)}};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_array_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*15, .m_other = 0, .m_tag = 246}, .m_size = 15, .m_capacity = 15, .m_data = {((lean_object*)&l_main___closed__52_value),((lean_object*)&l_main___closed__53_value),((lean_object*)&l_main___closed__55_value),((lean_object*)&l_main___closed__57_value),((lean_object*)&l_main___closed__58_value),((lean_object*)&l_main___closed__61_value),((lean_object*)&l_main___closed__62_value),((lean_object*)&l_main___closed__65_value),((lean_object*)&l_main___closed__67_value),((lean_object*)&l_main___closed__70_value),((lean_object*)&l_main___closed__72_value),((lean_object*)&l_main___closed__74_value),((lean_object*)&l_main___closed__77_value),((lean_object*)&l_main___closed__79_value),((lean_object*)&l_main___closed__81_value)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_string_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NJC_Sections"};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_string_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "weights"};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_ctor_object l_main___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(251, 168, 245, 67, 246, 206, 36, 103)}};
static const lean_ctor_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__85_value_aux_0),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 30, 162, 98, 173, 55, 154)}};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_string_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_ctor_object l_main___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(251, 168, 245, 67, 246, 206, 36, 103)}};
static const lean_ctor_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__87_value_aux_0),((lean_object*)&l_main___closed__86_value),LEAN_SCALAR_PTR_LITERAL(142, 45, 83, 50, 39, 83, 10, 2)}};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_string_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NJC_QueryOccurrence"};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_string_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "checkpoint_size"};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_ctor_object l_main___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(228, 184, 127, 86, 207, 249, 130, 182)}};
static const lean_ctor_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__90_value_aux_0),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(77, 51, 129, 97, 35, 250, 227, 139)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "closed"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_ctor_object l_main___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(228, 184, 127, 86, 207, 249, 130, 182)}};
static const lean_ctor_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(79, 97, 159, 165, 32, 87, 159, 85)}};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_string_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NJC_CutTypes"};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_string_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "powers_array"};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_ctor_object l_main___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(50, 80, 142, 13, 190, 151, 247, 166)}};
static const lean_ctor_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__95_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(228, 222, 176, 211, 40, 48, 33, 247)}};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_string_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "readerK"};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_ctor_object l_main___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(50, 80, 142, 13, 190, 151, 247, 166)}};
static const lean_ctor_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_0),((lean_object*)&l_main___closed__96_value),LEAN_SCALAR_PTR_LITERAL(36, 255, 137, 68, 232, 78, 73, 29)}};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_ctor_object l_main___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(50, 80, 142, 13, 190, 151, 247, 166)}};
static const lean_ctor_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__98_value_aux_0),((lean_object*)&l_main___closed__33_value),LEAN_SCALAR_PTR_LITERAL(173, 147, 3, 1, 99, 80, 239, 94)}};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_string_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "weightStep"};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_ctor_object l_main___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(50, 80, 142, 13, 190, 151, 247, 166)}};
static const lean_ctor_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_0),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(192, 170, 46, 183, 105, 11, 119, 0)}};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_string_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NJC_Contains"};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_ctor_object l_main___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__101_value),LEAN_SCALAR_PTR_LITERAL(188, 200, 241, 209, 2, 205, 147, 203)}};
static const lean_ctor_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(43, 205, 157, 170, 227, 60, 51, 44)}};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_string_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "list"};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_ctor_object l_main___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__101_value),LEAN_SCALAR_PTR_LITERAL(188, 200, 241, 209, 2, 205, 147, 203)}};
static const lean_ctor_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__105_value_aux_0),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(185, 163, 22, 37, 35, 47, 208, 187)}};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_ctor_object l_main___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__101_value),LEAN_SCALAR_PTR_LITERAL(188, 200, 241, 209, 2, 205, 147, 203)}};
static const lean_ctor_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(22, 95, 135, 178, 194, 92, 53, 79)}};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_string_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NJC_ValidateArithmetic"};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_string_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shift"};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_ctor_object l_main___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__107_value),LEAN_SCALAR_PTR_LITERAL(205, 107, 237, 224, 11, 25, 16, 126)}};
static const lean_ctor_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__109_value_aux_0),((lean_object*)&l_main___closed__108_value),LEAN_SCALAR_PTR_LITERAL(77, 169, 175, 199, 74, 5, 124, 195)}};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "increment"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__107_value),LEAN_SCALAR_PTR_LITERAL(205, 107, 237, 224, 11, 25, 16, 126)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(121, 110, 123, 152, 17, 214, 220, 140)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NJC_ValidateStep"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_ctor_object l_main___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(124, 147, 209, 161, 209, 235, 65, 247)}};
static const lean_ctor_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__113_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(214, 235, 52, 28, 134, 205, 14, 159)}};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_string_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "loop_exact"};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_ctor_object l_main___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__51_value),LEAN_SCALAR_PTR_LITERAL(57, 149, 206, 125, 67, 32, 183, 207)}};
static const lean_ctor_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__115_value_aux_0),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(127, 148, 133, 212, 99, 218, 14, 255)}};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_array_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*15, .m_other = 0, .m_tag = 246}, .m_size = 15, .m_capacity = 15, .m_data = {((lean_object*)&l_main___closed__85_value),((lean_object*)&l_main___closed__87_value),((lean_object*)&l_main___closed__90_value),((lean_object*)&l_main___closed__92_value),((lean_object*)&l_main___closed__95_value),((lean_object*)&l_main___closed__97_value),((lean_object*)&l_main___closed__98_value),((lean_object*)&l_main___closed__100_value),((lean_object*)&l_main___closed__103_value),((lean_object*)&l_main___closed__105_value),((lean_object*)&l_main___closed__106_value),((lean_object*)&l_main___closed__109_value),((lean_object*)&l_main___closed__111_value),((lean_object*)&l_main___closed__113_value),((lean_object*)&l_main___closed__115_value)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_string_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NJC_ClosedCalls"};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inactive_clause"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_ctor_object l_main___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(39, 39, 38, 165, 251, 80, 255, 96)}};
static const lean_ctor_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_0),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(157, 182, 43, 70, 211, 167, 176, 15)}};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_string_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "geometry_clause"};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_ctor_object l_main___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(39, 39, 38, 165, 251, 80, 255, 96)}};
static const lean_ctor_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_0),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(141, 127, 137, 102, 23, 142, 0, 103)}};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_ctor_object l_main___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(39, 39, 38, 165, 251, 80, 255, 96)}};
static const lean_ctor_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__122_value_aux_0),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(166, 77, 109, 200, 251, 77, 236, 14)}};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_ctor_object l_main___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(39, 39, 38, 165, 251, 80, 255, 96)}};
static const lean_ctor_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__123_value_aux_0),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(146, 99, 62, 231, 186, 172, 83, 179)}};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_string_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "opening_clause"};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_ctor_object l_main___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(39, 39, 38, 165, 251, 80, 255, 96)}};
static const lean_ctor_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__125_value_aux_0),((lean_object*)&l_main___closed__124_value),LEAN_SCALAR_PTR_LITERAL(159, 97, 115, 179, 162, 110, 55, 216)}};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_string_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NJC_ReaderResults"};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_string_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "decodeK"};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_ctor_object l_main___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(203, 231, 53, 61, 24, 68, 168, 24)}};
static const lean_ctor_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_0),((lean_object*)&l_main___closed__127_value),LEAN_SCALAR_PTR_LITERAL(64, 40, 251, 16, 61, 119, 138, 165)}};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_ctor_object l_main___closed__129_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(203, 231, 53, 61, 24, 68, 168, 24)}};
static const lean_ctor_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__129_value_aux_0),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(241, 231, 237, 27, 76, 133, 45, 3)}};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_string_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "boundedK"};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_ctor_object l_main___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(203, 231, 53, 61, 24, 68, 168, 24)}};
static const lean_ctor_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__131_value_aux_0),((lean_object*)&l_main___closed__130_value),LEAN_SCALAR_PTR_LITERAL(140, 167, 105, 213, 185, 51, 56, 221)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_string_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NJC_EReaderResults"};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_string_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "decodeE"};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_ctor_object l_main___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(188, 58, 70, 87, 86, 206, 241, 112)}};
static const lean_ctor_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__134_value_aux_0),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(156, 220, 82, 77, 66, 145, 55, 245)}};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_ctor_object l_main___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(188, 58, 70, 87, 86, 206, 241, 112)}};
static const lean_ctor_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__135_value_aux_0),((lean_object*)&l_main___closed__28_value),LEAN_SCALAR_PTR_LITERAL(217, 74, 107, 67, 171, 200, 112, 114)}};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_string_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NJC_ReaderWindows"};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_ctor_object l_main___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(111, 240, 59, 15, 2, 131, 76, 122)}};
static const lean_ctor_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_0),((lean_object*)&l_main___closed__28_value),LEAN_SCALAR_PTR_LITERAL(222, 136, 29, 82, 104, 191, 67, 94)}};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_ctor_object l_main___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(111, 240, 59, 15, 2, 131, 76, 122)}};
static const lean_ctor_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__138_value_aux_0),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(125, 213, 206, 145, 14, 92, 119, 186)}};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_string_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_ctor_object l_main___closed__140_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(111, 240, 59, 15, 2, 131, 76, 122)}};
static const lean_ctor_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__140_value_aux_0),((lean_object*)&l_main___closed__139_value),LEAN_SCALAR_PTR_LITERAL(196, 230, 96, 54, 17, 9, 102, 186)}};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_string_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "child"};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_ctor_object l_main___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(251, 168, 245, 67, 246, 206, 36, 103)}};
static const lean_ctor_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__142_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(64, 11, 57, 18, 32, 175, 238, 28)}};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_string_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "semantic"};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_ctor_object l_main___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(251, 168, 245, 67, 246, 206, 36, 103)}};
static const lean_ctor_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_0),((lean_object*)&l_main___closed__143_value),LEAN_SCALAR_PTR_LITERAL(105, 211, 18, 156, 18, 147, 40, 81)}};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_array_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*15, .m_other = 0, .m_tag = 246}, .m_size = 15, .m_capacity = 15, .m_data = {((lean_object*)&l_main___closed__119_value),((lean_object*)&l_main___closed__121_value),((lean_object*)&l_main___closed__122_value),((lean_object*)&l_main___closed__123_value),((lean_object*)&l_main___closed__125_value),((lean_object*)&l_main___closed__128_value),((lean_object*)&l_main___closed__129_value),((lean_object*)&l_main___closed__131_value),((lean_object*)&l_main___closed__134_value),((lean_object*)&l_main___closed__135_value),((lean_object*)&l_main___closed__137_value),((lean_object*)&l_main___closed__138_value),((lean_object*)&l_main___closed__140_value),((lean_object*)&l_main___closed__142_value),((lean_object*)&l_main___closed__144_value)}};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_string_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_ctor_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_string_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_ctor_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_array_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__147_value),((lean_object*)&l_main___closed__149_value)}};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_string_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_ctor_object l_main___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__152_value_aux_0),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_string_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_ctor_object l_main___closed__154_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__154_value_aux_0),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_string_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_ctor_object l_main___closed__156_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__156_value_aux_0),((lean_object*)&l_main___closed__155_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_string_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_ctor_object l_main___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__146_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__158_value_aux_0),((lean_object*)&l_main___closed__157_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_string_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_ctor_object l_main___closed__160_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__160_value_aux_0),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_string_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_ctor_object l_main___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_0),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_string_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_ctor_object l_main___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_0),((lean_object*)&l_main___closed__155_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_string_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_ctor_object l_main___closed__166_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_0),((lean_object*)&l_main___closed__157_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_array_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__152_value),((lean_object*)&l_main___closed__154_value),((lean_object*)&l_main___closed__156_value),((lean_object*)&l_main___closed__158_value),((lean_object*)&l_main___closed__160_value),((lean_object*)&l_main___closed__162_value),((lean_object*)&l_main___closed__164_value),((lean_object*)&l_main___closed__166_value)}};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_string_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
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
uint32_t v___x_596_; lean_object* v___x_597_; 
v___x_596_ = 0;
v___x_597_ = lean_box_uint32(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_598_; lean_object* v___x_599_; 
v___x_598_ = 1;
v___x_599_ = lean_box_uint32(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_600_; lean_object* v___x_601_; 
v___x_600_ = 2;
v___x_601_ = lean_box_uint32(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_602_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = l_NFA__MemoryLimit_set();
v___x_605_ = ((lean_object*)(l_main___closed__0));
v___x_606_ = l_Lean_findSysroot(v___x_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_box(0);
v___x_609_ = l_Lean_initSearchPath(v_a_607_, v___x_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; 
lean_dec_ref_known(v___x_609_, 1);
v___x_610_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v___y_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___y_691_; 
lean_dec_ref_known(v___x_610_, 1);
if (lean_obj_tag(v_args_602_) == 0)
{
lean_object* v___x_713_; 
v___x_713_ = ((lean_object*)(l_main___closed__168));
v___y_691_ = v___x_713_;
goto v___jp_690_;
}
else
{
lean_object* v_head_714_; 
v_head_714_ = lean_ctor_get(v_args_602_, 0);
lean_inc(v_head_714_);
lean_dec_ref_known(v_args_602_, 2);
v___y_691_ = v_head_714_;
goto v___jp_690_;
}
v___jp_611_:
{
size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint32_t v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_sz_615_ = lean_array_size(v_fst_613_);
v___x_616_ = ((size_t)0ULL);
lean_inc_ref(v_fst_613_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_615_, v___x_616_, v_fst_613_);
v___x_618_ = l_Lean_Options_empty;
v___x_619_ = 0;
v___x_620_ = ((lean_object*)(l_main___closed__1));
v___x_621_ = 0;
v___x_622_ = 1;
v___x_623_ = 2;
v___x_624_ = lean_box(1);
v___x_625_ = l_Lean_importModules(v___x_617_, v___x_618_, v___x_619_, v___x_620_, v___x_621_, v___x_622_, v___x_623_, v___x_624_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; size_t v_sz_631_; lean_object* v___x_632_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_628_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_629_ = l_Lean_Elab_Command_mkState(v_a_626_, v___x_628_, v___x_618_);
v___x_630_ = lean_st_mk_ref(v___x_629_);
v_sz_631_ = lean_array_size(v_snd_614_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_612_, v_snd_614_, v_sz_631_, v___x_616_, v___x_621_, v___x_627_, v___x_630_);
lean_dec_ref(v___y_612_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v_messages_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_st_ref_get(v___x_630_);
lean_dec(v___x_630_);
v_messages_635_ = lean_ctor_get(v___x_634_, 1);
lean_inc_ref(v_messages_635_);
lean_dec(v___x_634_);
v___x_636_ = l_Lean_MessageLog_toList(v_messages_635_);
lean_dec_ref(v_messages_635_);
v___x_637_ = lean_box(0);
v___x_638_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_638_, 0);
lean_dec(v_unused_652_);
v___x_640_ = v___x_638_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_dec(v___x_638_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = l_main___boxed__const__1;
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l_main___boxed__const__2;
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_633_);
v_a_653_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_638_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_638_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v___x_630_);
v_a_661_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_632_, 1);
v___x_662_ = l_Lean_Exception_toMessageData(v_a_661_);
v___x_663_ = l_Lean_MessageData_toString(v___x_662_);
v___x_664_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_673_);
v___x_666_ = v___x_664_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_dec(v___x_664_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_main___boxed__const__3;
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_664_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_664_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v___y_612_);
v_a_682_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_625_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_625_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
v___jp_690_:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_main___closed__9));
v___x_693_ = lean_string_dec_eq(v___y_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_main___closed__10));
v___x_695_ = lean_string_dec_eq(v___y_691_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_main___closed__11));
v___x_697_ = lean_string_dec_eq(v___y_691_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = ((lean_object*)(l_main___closed__12));
v___x_699_ = lean_string_dec_eq(v___y_691_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_main___closed__13));
v___x_701_ = lean_string_dec_eq(v___y_691_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = ((lean_object*)(l_main___closed__14));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_702_;
v_snd_614_ = v___x_702_;
goto v___jp_611_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_main___closed__17));
v___x_704_ = ((lean_object*)(l_main___closed__50));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_703_;
v_snd_614_ = v___x_704_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_main___closed__17));
v___x_706_ = ((lean_object*)(l_main___closed__82));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_705_;
v_snd_614_ = v___x_706_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_main___closed__17));
v___x_708_ = ((lean_object*)(l_main___closed__116));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_707_;
v_snd_614_ = v___x_708_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_main___closed__17));
v___x_710_ = ((lean_object*)(l_main___closed__145));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_709_;
v_snd_614_ = v___x_710_;
goto v___jp_611_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_main___closed__150));
v___x_712_ = ((lean_object*)(l_main___closed__167));
v___y_612_ = v___y_691_;
v_fst_613_ = v___x_711_;
v_snd_614_ = v___x_712_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_args_602_);
v_a_715_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_610_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_610_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_args_602_);
v_a_723_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_609_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_609_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_args_602_);
v_a_731_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_606_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_606_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = _lean_main(v_args_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_742_, lean_object* v_as_x27_743_, lean_object* v_b_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_743_, v_b_744_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_748_, lean_object* v_as_x27_749_, lean_object* v_b_750_, lean_object* v_a_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_748_, v_as_x27_749_, v_b_750_, v_a_751_);
lean_dec(v_as_x27_749_);
lean_dec(v_as_748_);
return v_res_753_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NJC__ProofDriver(uint8_t builtin) {
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
  res = initialize_NJC__ProofDriver(1 /* builtin */);
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
