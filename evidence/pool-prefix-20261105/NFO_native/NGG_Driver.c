// Lean compiler output
// Module: NGG_Driver
// Imports: public import Init public meta import Init public import Lean public import NFR_WALKER public import NFR_MemoryLimit
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* l_NFO__MemoryLimit_set();
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
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "final"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_array_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_ctor_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_ctor_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__14_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_array_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__13_value),((lean_object*)&l_main___closed__15_value)}};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_ctor_object l_main___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__18_value_aux_0),((lean_object*)&l_main___closed__17_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_ctor_object l_main___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__20_value_aux_0),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_ctor_object l_main___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__22_value_aux_0),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__24_value_aux_0),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_ctor_object l_main___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__25_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__26_value_aux_0),((lean_object*)&l_main___closed__17_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_ctor_object l_main___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__28_value_aux_0),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_ctor_object l_main___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__29_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__30_value_aux_0),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_ctor_object l_main___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__31_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__32_value_aux_0),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_array_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__18_value),((lean_object*)&l_main___closed__20_value),((lean_object*)&l_main___closed__22_value),((lean_object*)&l_main___closed__24_value),((lean_object*)&l_main___closed__26_value),((lean_object*)&l_main___closed__28_value),((lean_object*)&l_main___closed__30_value),((lean_object*)&l_main___closed__32_value)}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFV_PoolReturnData"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_ctor_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__34_value),LEAN_SCALAR_PTR_LITERAL(213, 190, 254, 127, 158, 3, 109, 55)}};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NGG_Count"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_ctor_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(93, 233, 182, 34, 249, 101, 118, 192)}};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NGG_Loader"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_ctor_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 184, 99, 73, 240, 195, 188)}};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NGG_Compare"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_ctor_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(161, 93, 206, 222, 189, 157, 248, 51)}};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NGG_Metadata"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_ctor_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(92, 215, 214, 143, 250, 146, 74, 135)}};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NGG_Payer"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_ctor_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(38, 132, 132, 105, 203, 244, 180, 121)}};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NGG_Transport"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_ctor_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(4, 25, 146, 54, 115, 36, 170, 11)}};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_string_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NGG_Scalar"};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_ctor_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__48_value),LEAN_SCALAR_PTR_LITERAL(58, 71, 121, 160, 166, 237, 230, 4)}};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_string_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NGG_LayoutValue"};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_ctor_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__50_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 78, 131, 43, 206, 224, 181)}};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_string_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NGG_DecodePrefix"};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_ctor_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__52_value),LEAN_SCALAR_PTR_LITERAL(46, 115, 132, 234, 163, 86, 31, 208)}};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NGG_RequestLength"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_ctor_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(234, 152, 250, 219, 13, 69, 124, 250)}};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NGG_LayoutBounds"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_ctor_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(70, 233, 63, 79, 42, 179, 249, 156)}};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_string_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NGG_PaymentWindows"};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_ctor_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__58_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 204, 86, 55, 60, 53, 53)}};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NGG_EnvelopePrefix"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_ctor_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__60_value),LEAN_SCALAR_PTR_LITERAL(49, 37, 164, 112, 198, 185, 26, 95)}};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NGG_MarkerZero"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_ctor_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NGG_ErrorImage"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_ctor_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__64_value),LEAN_SCALAR_PTR_LITERAL(203, 39, 227, 93, 116, 70, 12, 8)}};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_array_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*16, .m_other = 0, .m_tag = 246}, .m_size = 16, .m_capacity = 16, .m_data = {((lean_object*)&l_main___closed__35_value),((lean_object*)&l_main___closed__37_value),((lean_object*)&l_main___closed__39_value),((lean_object*)&l_main___closed__41_value),((lean_object*)&l_main___closed__43_value),((lean_object*)&l_main___closed__45_value),((lean_object*)&l_main___closed__47_value),((lean_object*)&l_main___closed__49_value),((lean_object*)&l_main___closed__51_value),((lean_object*)&l_main___closed__53_value),((lean_object*)&l_main___closed__55_value),((lean_object*)&l_main___closed__57_value),((lean_object*)&l_main___closed__59_value),((lean_object*)&l_main___closed__61_value),((lean_object*)&l_main___closed__63_value),((lean_object*)&l_main___closed__65_value)}};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_string_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFR_ModelJoin"};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_string_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "same_emitted_settlement"};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_ctor_object l_main___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(116, 216, 64, 123, 238, 226, 19, 255)}};
static const lean_ctor_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__69_value_aux_0),((lean_object*)&l_main___closed__68_value),LEAN_SCALAR_PTR_LITERAL(124, 140, 82, 25, 74, 12, 227, 7)}};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_string_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_ctor_object l_main___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(93, 233, 182, 34, 249, 101, 118, 192)}};
static const lean_ctor_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__71_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(42, 115, 102, 125, 47, 55, 30, 56)}};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_ctor_object l_main___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 184, 99, 73, 240, 195, 188)}};
static const lean_ctor_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__72_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(245, 10, 241, 204, 148, 36, 150, 65)}};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_string_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ne"};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_ctor_object l_main___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(161, 93, 206, 222, 189, 157, 248, 51)}};
static const lean_ctor_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__74_value_aux_0),((lean_object*)&l_main___closed__73_value),LEAN_SCALAR_PTR_LITERAL(212, 200, 97, 40, 26, 158, 191, 242)}};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_string_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "verifier"};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_ctor_object l_main___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(92, 215, 214, 143, 250, 146, 74, 135)}};
static const lean_ctor_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__76_value_aux_0),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(56, 93, 71, 221, 55, 135, 150, 180)}};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_string_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_ctor_object l_main___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(92, 215, 214, 143, 250, 146, 74, 135)}};
static const lean_ctor_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__78_value_aux_0),((lean_object*)&l_main___closed__77_value),LEAN_SCALAR_PTR_LITERAL(186, 155, 40, 104, 218, 62, 187, 185)}};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_ctor_object l_main___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(38, 132, 132, 105, 203, 244, 180, 121)}};
static const lean_ctor_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__79_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(109, 56, 131, 81, 173, 245, 184, 124)}};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_ctor_object l_main___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(4, 25, 146, 54, 115, 36, 170, 11)}};
static const lean_ctor_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__80_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(247, 23, 235, 54, 161, 152, 74, 210)}};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_string_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wrapping_add"};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_ctor_object l_main___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__48_value),LEAN_SCALAR_PTR_LITERAL(58, 71, 121, 160, 166, 237, 230, 4)}};
static const lean_ctor_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_0),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(173, 163, 68, 6, 63, 208, 163, 153)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_string_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "checked_add"};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_ctor_object l_main___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__48_value),LEAN_SCALAR_PTR_LITERAL(58, 71, 121, 160, 166, 237, 230, 4)}};
static const lean_ctor_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_0),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(211, 54, 72, 130, 73, 184, 214, 34)}};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_string_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NGG_LayoutGTransfer"};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_ctor_object l_main___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__85_value),LEAN_SCALAR_PTR_LITERAL(176, 83, 106, 115, 224, 250, 14, 245)}};
static const lean_ctor_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__86_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(27, 180, 248, 235, 58, 212, 112, 244)}};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_string_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NGG_LayoutGWithdrawal"};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_ctor_object l_main___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(5, 116, 243, 102, 108, 212, 28, 25)}};
static const lean_ctor_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__88_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(98, 31, 120, 8, 192, 110, 241, 109)}};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_string_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NGG_LayoutRTransfer"};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_ctor_object l_main___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(133, 12, 107, 73, 134, 250, 146, 95)}};
static const lean_ctor_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__90_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(226, 145, 145, 29, 238, 7, 122, 191)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NGG_LayoutRWithdrawal"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_ctor_object l_main___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(88, 180, 117, 188, 156, 137, 142, 29)}};
static const lean_ctor_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(19, 36, 90, 78, 147, 171, 138, 34)}};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_ctor_object l_main___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__50_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 78, 131, 43, 206, 224, 181)}};
static const lean_ctor_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__93_value_aux_0),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(103, 193, 226, 87, 43, 43, 231, 145)}};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_string_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "metas"};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_ctor_object l_main___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(70, 233, 63, 79, 42, 179, 249, 156)}};
static const lean_ctor_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__95_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(214, 182, 56, 128, 204, 82, 7, 236)}};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_string_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "windows"};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_ctor_object l_main___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(70, 233, 63, 79, 42, 179, 249, 156)}};
static const lean_ctor_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_0),((lean_object*)&l_main___closed__96_value),LEAN_SCALAR_PTR_LITERAL(29, 173, 202, 155, 117, 63, 225, 33)}};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_string_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "resume_eq"};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_ctor_object l_main___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__52_value),LEAN_SCALAR_PTR_LITERAL(46, 115, 132, 234, 163, 86, 31, 208)}};
static const lean_ctor_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__99_value_aux_0),((lean_object*)&l_main___closed__98_value),LEAN_SCALAR_PTR_LITERAL(153, 1, 40, 122, 174, 97, 231, 150)}};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_string_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cut"};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_ctor_object l_main___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__52_value),LEAN_SCALAR_PTR_LITERAL(46, 115, 132, 234, 163, 86, 31, 208)}};
static const lean_ctor_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__101_value_aux_0),((lean_object*)&l_main___closed__100_value),LEAN_SCALAR_PTR_LITERAL(58, 244, 203, 157, 164, 66, 236, 23)}};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "decoder"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_ctor_object l_main___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(234, 152, 250, 219, 13, 69, 124, 250)}};
static const lean_ctor_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(140, 115, 232, 158, 157, 180, 69, 157)}};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_string_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "payload"};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_ctor_object l_main___closed__105_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(234, 152, 250, 219, 13, 69, 124, 250)}};
static const lean_ctor_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__105_value_aux_0),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(247, 201, 56, 41, 12, 106, 12, 62)}};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_string_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "point"};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_ctor_object l_main___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__58_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 204, 86, 55, 60, 53, 53)}};
static const lean_ctor_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__107_value_aux_0),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(187, 132, 19, 64, 163, 238, 157, 128)}};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_string_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "domain"};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_ctor_object l_main___closed__109_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__58_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 204, 86, 55, 60, 53, 53)}};
static const lean_ctor_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__109_value_aux_0),((lean_object*)&l_main___closed__108_value),LEAN_SCALAR_PTR_LITERAL(187, 240, 38, 191, 41, 51, 176, 211)}};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "asq8"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__60_value),LEAN_SCALAR_PTR_LITERAL(49, 37, 164, 112, 198, 185, 26, 95)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(132, 31, 72, 220, 35, 143, 81, 179)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "predicate"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_ctor_object l_main___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_ctor_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__113_value_aux_0),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(230, 143, 223, 239, 77, 231, 173, 115)}};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_string_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_ctor_object l_main___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_ctor_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__115_value_aux_0),((lean_object*)&l_main___closed__114_value),LEAN_SCALAR_PTR_LITERAL(225, 197, 28, 173, 242, 117, 15, 36)}};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_string_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bound"};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_ctor_object l_main___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_ctor_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__117_value_aux_0),((lean_object*)&l_main___closed__116_value),LEAN_SCALAR_PTR_LITERAL(183, 186, 204, 205, 254, 4, 224, 250)}};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "abort"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_ctor_object l_main___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(215, 221, 90, 234, 151, 21, 251, 199)}};
static const lean_ctor_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_0),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(164, 57, 87, 116, 27, 228, 243, 231)}};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_string_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "failure"};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_ctor_object l_main___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__64_value),LEAN_SCALAR_PTR_LITERAL(203, 39, 227, 93, 116, 70, 12, 8)}};
static const lean_ctor_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_0),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(247, 68, 134, 202, 127, 79, 255, 57)}};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_string_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "success"};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_ctor_object l_main___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__64_value),LEAN_SCALAR_PTR_LITERAL(203, 39, 227, 93, 116, 70, 12, 8)}};
static const lean_ctor_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__123_value_aux_0),((lean_object*)&l_main___closed__122_value),LEAN_SCALAR_PTR_LITERAL(236, 99, 234, 152, 31, 61, 78, 138)}};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_array_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*30, .m_other = 0, .m_tag = 246}, .m_size = 30, .m_capacity = 30, .m_data = {((lean_object*)&l_main___closed__69_value),((lean_object*)&l_main___closed__71_value),((lean_object*)&l_main___closed__72_value),((lean_object*)&l_main___closed__74_value),((lean_object*)&l_main___closed__76_value),((lean_object*)&l_main___closed__78_value),((lean_object*)&l_main___closed__79_value),((lean_object*)&l_main___closed__80_value),((lean_object*)&l_main___closed__82_value),((lean_object*)&l_main___closed__84_value),((lean_object*)&l_main___closed__86_value),((lean_object*)&l_main___closed__88_value),((lean_object*)&l_main___closed__90_value),((lean_object*)&l_main___closed__92_value),((lean_object*)&l_main___closed__93_value),((lean_object*)&l_main___closed__95_value),((lean_object*)&l_main___closed__97_value),((lean_object*)&l_main___closed__99_value),((lean_object*)&l_main___closed__101_value),((lean_object*)&l_main___closed__103_value),((lean_object*)&l_main___closed__105_value),((lean_object*)&l_main___closed__107_value),((lean_object*)&l_main___closed__109_value),((lean_object*)&l_main___closed__111_value),((lean_object*)&l_main___closed__113_value),((lean_object*)&l_main___closed__115_value),((lean_object*)&l_main___closed__117_value),((lean_object*)&l_main___closed__119_value),((lean_object*)&l_main___closed__121_value),((lean_object*)&l_main___closed__123_value)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
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
uint32_t v___x_478_; lean_object* v___x_479_; 
v___x_478_ = 0;
v___x_479_ = lean_box_uint32(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_480_; lean_object* v___x_481_; 
v___x_480_ = 1;
v___x_481_ = lean_box_uint32(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_482_; lean_object* v___x_483_; 
v___x_482_ = 2;
v___x_483_ = lean_box_uint32(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = l_NFO__MemoryLimit_set();
v___x_487_ = ((lean_object*)(l_main___closed__0));
v___x_488_ = l_Lean_findSysroot(v___x_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = lean_box(0);
v___x_491_ = l_Lean_initSearchPath(v_a_489_, v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___x_491_, 1);
v___x_492_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___y_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___y_573_; 
lean_dec_ref_known(v___x_492_, 1);
if (lean_obj_tag(v_args_484_) == 0)
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_main___closed__125));
v___y_573_ = v___x_583_;
goto v___jp_572_;
}
else
{
lean_object* v_head_584_; 
v_head_584_ = lean_ctor_get(v_args_484_, 0);
lean_inc(v_head_584_);
lean_dec_ref_known(v_args_484_, 2);
v___y_573_ = v_head_584_;
goto v___jp_572_;
}
v___jp_493_:
{
size_t v_sz_497_; size_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint32_t v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; uint8_t v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_sz_497_ = lean_array_size(v_fst_495_);
v___x_498_ = ((size_t)0ULL);
lean_inc_ref(v_fst_495_);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_497_, v___x_498_, v_fst_495_);
v___x_500_ = l_Lean_Options_empty;
v___x_501_ = 0;
v___x_502_ = ((lean_object*)(l_main___closed__1));
v___x_503_ = 0;
v___x_504_ = 1;
v___x_505_ = 2;
v___x_506_ = lean_box(1);
v___x_507_ = l_Lean_importModules(v___x_499_, v___x_500_, v___x_501_, v___x_502_, v___x_503_, v___x_504_, v___x_505_, v___x_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; size_t v_sz_513_; lean_object* v___x_514_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_510_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_511_ = l_Lean_Elab_Command_mkState(v_a_508_, v___x_510_, v___x_500_);
v___x_512_ = lean_st_mk_ref(v___x_511_);
v_sz_513_ = lean_array_size(v_snd_496_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_494_, v_snd_496_, v_sz_513_, v___x_498_, v___x_503_, v___x_509_, v___x_512_);
lean_dec_ref(v___y_494_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v_messages_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_st_ref_get(v___x_512_);
lean_dec(v___x_512_);
v_messages_517_ = lean_ctor_get(v___x_516_, 1);
lean_inc_ref(v_messages_517_);
lean_dec(v___x_516_);
v___x_518_ = l_Lean_MessageLog_toList(v_messages_517_);
lean_dec_ref(v_messages_517_);
v___x_519_ = lean_box(0);
v___x_520_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_533_; 
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v___x_520_, 0);
lean_dec(v_unused_534_);
v___x_522_ = v___x_520_;
v_isShared_523_ = v_isSharedCheck_533_;
goto v_resetjp_521_;
}
else
{
lean_dec(v___x_520_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_533_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = l_main___boxed__const__1;
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_525_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = l_main___boxed__const__2;
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_529_);
v___x_531_ = v___x_522_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_515_);
v_a_535_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_520_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_520_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_512_);
v_a_543_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_514_, 1);
v___x_544_ = l_Lean_Exception_toMessageData(v_a_543_);
v___x_545_ = l_Lean_MessageData_toString(v___x_544_);
v___x_546_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_546_, 0);
lean_dec(v_unused_555_);
v___x_548_ = v___x_546_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_dec(v___x_546_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = l_main___boxed__const__3;
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_546_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v___y_494_);
v_a_564_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_507_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_507_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = ((lean_object*)(l_main___closed__9));
v___x_575_ = lean_string_dec_eq(v___y_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l_main___closed__10));
v___x_577_ = lean_string_dec_eq(v___y_573_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_main___closed__11));
v___y_494_ = v___y_573_;
v_fst_495_ = v___x_578_;
v_snd_496_ = v___x_578_;
goto v___jp_493_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_main___closed__16));
v___x_580_ = ((lean_object*)(l_main___closed__33));
v___y_494_ = v___y_573_;
v_fst_495_ = v___x_579_;
v_snd_496_ = v___x_580_;
goto v___jp_493_;
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_main___closed__66));
v___x_582_ = ((lean_object*)(l_main___closed__124));
v___y_494_ = v___y_573_;
v_fst_495_ = v___x_581_;
v_snd_496_ = v___x_582_;
goto v___jp_493_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_args_484_);
v_a_585_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_492_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_492_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_args_484_);
v_a_593_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_491_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_491_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_args_484_);
v_a_601_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_488_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_488_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = _lean_main(v_args_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_612_, lean_object* v_as_x27_613_, lean_object* v_b_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_613_, v_b_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_618_, lean_object* v_as_x27_619_, lean_object* v_b_620_, lean_object* v_a_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_618_, v_as_x27_619_, v_b_620_, v_a_621_);
lean_dec(v_as_x27_619_);
lean_dec(v_as_618_);
return v_res_623_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFR__WALKER(uint8_t builtin);
lean_object* initialize_NFR__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NGG__Driver(uint8_t builtin) {
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
res = initialize_NFR__WALKER(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NFR__MemoryLimit(builtin);
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
  res = initialize_NGG__Driver(1 /* builtin */);
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
