// Lean compiler output
// Module: NHS_ProofDriver
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
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_String_toName(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
lean_object* l_NFA__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__3___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_main___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__7;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NHS_AUDIT_ROOTS.json"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "groups"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "proof group out of range"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_ctor_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__12_value)}};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_string_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NHS_COMBINED_IMPORT"};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_ctor_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__14_value),LEAN_SCALAR_PTR_LITERAL(221, 11, 110, 231, 249, 129, 253, 14)}};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_array_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__15_value)}};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid proof mode"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_ctor_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__17_value)}};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_ctor_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_ctor_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__21_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_array_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__20_value),((lean_object*)&l_main___closed__22_value)}};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_ctor_object l_main___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__25_value_aux_0),((lean_object*)&l_main___closed__24_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_ctor_object l_main___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__27_value_aux_0),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_ctor_object l_main___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__29_value_aux_0),((lean_object*)&l_main___closed__28_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_ctor_object l_main___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__31_value_aux_0),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_ctor_object l_main___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__32_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__33_value_aux_0),((lean_object*)&l_main___closed__24_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_ctor_object l_main___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__34_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__35_value_aux_0),((lean_object*)&l_main___closed__26_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_ctor_object l_main___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__37_value_aux_0),((lean_object*)&l_main___closed__28_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_ctor_object l_main___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__39_value_aux_0),((lean_object*)&l_main___closed__30_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_array_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__25_value),((lean_object*)&l_main___closed__27_value),((lean_object*)&l_main___closed__29_value),((lean_object*)&l_main___closed__31_value),((lean_object*)&l_main___closed__33_value),((lean_object*)&l_main___closed__35_value),((lean_object*)&l_main___closed__37_value),((lean_object*)&l_main___closed__39_value)}};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_string_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* l_main___boxed__const__3;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; lean_object* v___x_6_; lean_object* v_bs_x27_7_; lean_object* v___x_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; 
v_v_5_ = lean_array_uget(v_bs_3_, v_i_2_);
v___x_6_ = lean_unsigned_to_nat(0u);
v_bs_x27_7_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_6_);
v___x_8_ = l_String_toName(v_v_5_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_array_uset(v_bs_x27_7_, v_i_2_, v___x_8_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4___boxed(lean_object* v_sz_13_, lean_object* v_i_14_, lean_object* v_bs_15_){
_start:
{
size_t v_sz_boxed_16_; size_t v_i_boxed_17_; lean_object* v_res_18_; 
v_sz_boxed_16_ = lean_unbox_usize(v_sz_13_);
lean_dec(v_sz_13_);
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_boxed_16_, v_i_boxed_17_, v_bs_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v___y_32_, lean_object* v_as_33_, size_t v_sz_34_, size_t v_i_35_, uint8_t v_b_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_snd_41_; uint8_t v___x_46_; lean_object* v_a_48_; 
v___x_46_ = lean_usize_dec_lt(v_i_35_, v_sz_34_);
if (v___x_46_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(v_b_36_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Elab_Command_getRef___redArg(v___y_37_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v___x_64_, 1);
v___x_66_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_37_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_quotContext_x3f_67_; lean_object* v_a_68_; uint8_t v___x_69_; lean_object* v___x_70_; 
lean_dec_ref_known(v___x_66_, 1);
v_quotContext_x3f_67_ = lean_ctor_get(v___y_37_, 5);
v_a_68_ = lean_array_uget_borrowed(v_as_33_, v_i_35_);
v___x_69_ = 0;
v___x_70_ = l_Lean_SourceInfo_fromRef(v_a_65_, v___x_69_);
lean_dec(v_a_65_);
if (lean_obj_tag(v_quotContext_x3f_67_) == 0)
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_38_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_dec_ref_known(v___x_90_, 1);
goto v___jp_71_;
}
else
{
lean_object* v_a_91_; 
lean_dec(v___x_70_);
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v_a_48_ = v_a_91_;
goto v___jp_47_;
}
}
else
{
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_72_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__4));
v___x_73_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__5));
lean_inc_n(v___x_70_, 2);
v___x_74_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_70_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__6));
v___x_76_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_70_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
lean_inc(v_a_68_);
v___x_77_ = lean_mk_syntax_ident(v_a_68_);
v___x_78_ = l_Lean_Syntax_node3(v___x_70_, v___x_72_, v___x_74_, v___x_76_, v___x_77_);
v___x_79_ = l_Lean_Elab_Command_elabCommand(v___x_78_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref_known(v___x_79_, 1);
v___x_80_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__7));
v___x_81_ = lean_string_append(v___x_80_, v___y_32_);
v___x_82_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__8));
v___x_83_ = lean_string_append(v___x_81_, v___x_82_);
lean_inc_n(v_a_68_, 2);
v___x_84_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_68_, v___x_46_);
v___x_85_ = lean_string_append(v___x_83_, v___x_84_);
lean_dec_ref(v___x_84_);
v___x_86_ = l_NEP_audit(v_a_68_, v___x_85_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_87_; 
lean_dec_ref_known(v___x_86_, 1);
v___x_87_ = lean_box(v_b_36_);
v_snd_41_ = v___x_87_;
goto v___jp_40_;
}
else
{
lean_object* v_a_88_; 
v_a_88_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_86_, 1);
v_a_48_ = v_a_88_;
goto v___jp_47_;
}
}
else
{
lean_object* v_a_89_; 
v_a_89_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_79_, 1);
v_a_48_ = v_a_89_;
goto v___jp_47_;
}
}
}
else
{
lean_object* v_a_92_; 
lean_dec(v_a_65_);
v_a_92_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_66_, 1);
v_a_48_ = v_a_92_;
goto v___jp_47_;
}
}
else
{
lean_object* v_a_93_; 
v_a_93_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_64_, 1);
v_a_48_ = v_a_93_;
goto v___jp_47_;
}
}
v___jp_40_:
{
size_t v___x_42_; size_t v___x_43_; uint8_t v___x_44_; 
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_add(v_i_35_, v___x_42_);
v___x_44_ = lean_unbox(v_snd_41_);
lean_dec(v_snd_41_);
v_i_35_ = v___x_43_;
v_b_36_ = v___x_44_;
goto _start;
}
v___jp_47_:
{
uint8_t v___x_49_; 
v___x_49_ = l_Lean_Exception_isInterrupt(v_a_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = l_Lean_Exception_toMessageData(v_a_48_);
v___x_51_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_50_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_52_; 
lean_dec_ref_known(v___x_51_, 1);
v___x_52_ = lean_box(v___x_46_);
v_snd_41_ = v___x_52_;
goto v___jp_40_;
}
else
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_a_53_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_48_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v___y_94_, lean_object* v_as_95_, lean_object* v_sz_96_, lean_object* v_i_97_, lean_object* v_b_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
size_t v_sz_boxed_102_; size_t v_i_boxed_103_; uint8_t v_b_boxed_104_; lean_object* v_res_105_; 
v_sz_boxed_102_ = lean_unbox_usize(v_sz_96_);
lean_dec(v_sz_96_);
v_i_boxed_103_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_b_boxed_104_ = lean_unbox(v_b_98_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_94_, v_as_95_, v_sz_boxed_102_, v_i_boxed_103_, v_b_boxed_104_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec_ref(v_as_95_);
lean_dec_ref(v___y_94_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_106_, size_t v_i_107_, lean_object* v_bs_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_usize_dec_lt(v_i_107_, v_sz_106_);
if (v___x_109_ == 0)
{
return v_bs_108_;
}
else
{
lean_object* v_v_110_; lean_object* v___x_111_; lean_object* v_bs_x27_112_; uint8_t v___x_113_; lean_object* v___x_114_; size_t v___x_115_; size_t v___x_116_; lean_object* v___x_117_; 
v_v_110_ = lean_array_uget(v_bs_108_, v_i_107_);
v___x_111_ = lean_unsigned_to_nat(0u);
v_bs_x27_112_ = lean_array_uset(v_bs_108_, v_i_107_, v___x_111_);
v___x_113_ = 0;
v___x_114_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_114_, 0, v_v_110_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1, v___x_109_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1 + 1, v___x_109_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*1 + 2, v___x_113_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_add(v_i_107_, v___x_115_);
v___x_117_ = lean_array_uset(v_bs_x27_112_, v_i_107_, v___x_114_);
v_i_107_ = v___x_116_;
v_bs_108_ = v___x_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_119_, lean_object* v_i_120_, lean_object* v_bs_121_){
_start:
{
size_t v_sz_boxed_122_; size_t v_i_boxed_123_; lean_object* v_res_124_; 
v_sz_boxed_122_ = lean_unbox_usize(v_sz_119_);
lean_dec(v_sz_119_);
v_i_boxed_123_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_122_, v_i_boxed_123_, v_bs_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg(lean_object* v_as_x27_125_, lean_object* v_b_126_){
_start:
{
if (lean_obj_tag(v_as_x27_125_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v_b_126_);
return v___x_128_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v_data_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_head_129_ = lean_ctor_get(v_as_x27_125_, 0);
v_tail_130_ = lean_ctor_get(v_as_x27_125_, 1);
v_data_131_ = lean_ctor_get(v_head_129_, 4);
lean_inc(v_data_131_);
v___x_132_ = l_Lean_MessageData_toString(v_data_131_);
v___x_133_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; 
lean_dec_ref_known(v___x_133_, 1);
v___x_134_ = lean_box(0);
v_as_x27_125_ = v_tail_130_;
v_b_126_ = v___x_134_;
goto _start;
}
else
{
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(lean_object* v_as_x27_136_, lean_object* v_b_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_136_, v_b_137_);
lean_dec(v_as_x27_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4(size_t v_sz_140_, size_t v_i_141_, lean_object* v_bs_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = lean_usize_dec_lt(v_i_141_, v_sz_140_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_bs_142_);
return v___x_144_;
}
else
{
lean_object* v_v_145_; lean_object* v___x_146_; 
v_v_145_ = lean_array_uget_borrowed(v_bs_142_, v_i_141_);
lean_inc(v_v_145_);
v___x_146_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(v_v_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_bs_142_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v_bs_x27_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
v_a_155_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_146_, 1);
v___x_156_ = lean_unsigned_to_nat(0u);
v_bs_x27_157_ = lean_array_uset(v_bs_142_, v_i_141_, v___x_156_);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_141_, v___x_158_);
v___x_160_ = lean_array_uset(v_bs_x27_157_, v_i_141_, v_a_155_);
v_i_141_ = v___x_159_;
v_bs_142_ = v___x_160_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_162_, lean_object* v_i_163_, lean_object* v_bs_164_){
_start:
{
size_t v_sz_boxed_165_; size_t v_i_boxed_166_; lean_object* v_res_167_; 
v_sz_boxed_165_ = lean_unbox_usize(v_sz_162_);
lean_dec(v_sz_162_);
v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4(v_sz_boxed_165_, v_i_boxed_166_, v_bs_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3(lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 4)
{
lean_object* v_elems_171_; size_t v_sz_172_; size_t v___x_173_; lean_object* v___x_174_; 
v_elems_171_ = lean_ctor_get(v_x_170_, 0);
lean_inc_ref(v_elems_171_);
lean_dec_ref_known(v_x_170_, 1);
v_sz_172_ = lean_array_size(v_elems_171_);
v___x_173_ = ((size_t)0ULL);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3_spec__4(v_sz_172_, v___x_173_, v_elems_171_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_175_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__0));
v___x_176_ = lean_unsigned_to_nat(80u);
v___x_177_ = l_Lean_Json_pretty(v_x_170_, v___x_176_);
v___x_178_ = lean_string_append(v___x_175_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3___closed__1));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__3(lean_object* v_j_182_, lean_object* v_k_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = l_Lean_Json_getObjValD(v_j_182_, v_k_183_);
v___x_185_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00main_spec__3_spec__3(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__3___boxed(lean_object* v_j_186_, lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Json_getObjValAs_x3f___at___00main_spec__3(v_j_186_, v_k_187_);
lean_dec_ref(v_k_187_);
return v_res_188_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_main___closed__2));
v___x_194_ = l_Lean_FileMap_ofString(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_195_ = 0;
v___x_196_ = lean_box(0);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_box(0);
v___x_199_ = lean_box(0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_202_ = ((lean_object*)(l_main___closed__1));
v___x_203_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_200_);
lean_ctor_set(v___x_203_, 3, v___x_200_);
lean_ctor_set(v___x_203_, 4, v___x_199_);
lean_ctor_set(v___x_203_, 5, v___x_198_);
lean_ctor_set(v___x_203_, 6, v___x_197_);
lean_ctor_set(v___x_203_, 7, v___x_196_);
lean_ctor_set(v___x_203_, 8, v___x_198_);
lean_ctor_set(v___x_203_, 9, v___x_198_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*10, v___x_195_);
return v___x_203_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_unsigned_to_nat(32u);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
size_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_207_ = ((size_t)5ULL);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_unsigned_to_nat(32u);
v___x_210_ = lean_mk_empty_array_with_capacity(v___x_209_);
v___x_211_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_212_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_208_);
lean_ctor_set(v___x_212_, 3, v___x_208_);
lean_ctor_set_usize(v___x_212_, 4, v___x_207_);
return v___x_212_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_box(1);
v___x_214_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_296_; lean_object* v___x_297_; 
v___x_296_ = 0;
v___x_297_ = lean_box_uint32(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_298_; lean_object* v___x_299_; 
v___x_298_ = 1;
v___x_299_ = lean_box_uint32(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_300_; lean_object* v___x_301_; 
v___x_300_ = 2;
v___x_301_ = lean_box_uint32(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_302_){
_start:
{
lean_object* v___y_305_; lean_object* v_fst_306_; lean_object* v_snd_307_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = l_NFA__MemoryLimit_set();
v___x_384_ = ((lean_object*)(l_main___closed__8));
v___x_385_ = l_Lean_findSysroot(v___x_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_box(0);
v___x_388_ = l_Lean_initSearchPath(v_a_386_, v___x_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_389_; 
lean_dec_ref_known(v___x_388_, 1);
v___x_389_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___y_391_; 
lean_dec_ref_known(v___x_389_, 1);
if (lean_obj_tag(v_args_302_) == 0)
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_main___closed__41));
v___y_391_ = v___x_460_;
goto v___jp_390_;
}
else
{
lean_object* v_head_461_; 
v_head_461_ = lean_ctor_get(v_args_302_, 0);
lean_inc(v_head_461_);
lean_dec_ref_known(v_args_302_, 2);
v___y_391_ = v_head_461_;
goto v___jp_390_;
}
v___jp_390_:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l_main___closed__9));
v___x_393_ = lean_string_dec_eq(v___y_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_main___closed__10));
v___x_395_ = l_IO_FS_readFile(v___x_394_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v___x_397_ = l_Lean_Json_parse(v_a_396_);
v___x_398_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = ((lean_object*)(l_main___closed__11));
v___x_401_ = l_Lean_Json_getObjValAs_x3f___at___00main_spec__3(v_a_399_, v___x_400_);
v___x_402_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_433_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_433_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_433_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_433_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_407_ = lean_unsigned_to_nat(5u);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_string_utf8_byte_size(v___y_391_);
lean_inc_ref_n(v___y_391_, 2);
v___x_410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_410_, 0, v___y_391_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
v___x_411_ = l_String_Slice_Pos_nextn(v___x_410_, v___x_408_, v___x_407_);
lean_dec_ref_known(v___x_410_, 3);
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v___y_391_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
v___x_413_ = l_String_Slice_toString(v___x_412_);
lean_dec_ref_known(v___x_412_, 3);
v___x_414_ = lean_string_utf8_byte_size(v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_408_);
lean_ctor_set(v___x_415_, 2, v___x_414_);
v___x_416_ = l_String_Slice_toNat_x3f(v___x_415_);
lean_dec_ref_known(v___x_415_, 3);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_val_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = lean_array_get_size(v_a_403_);
v___x_419_ = lean_nat_dec_lt(v_val_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_422_; 
lean_dec(v_val_417_);
lean_dec(v_a_403_);
lean_dec_ref(v___y_391_);
v___x_420_ = ((lean_object*)(l_main___closed__13));
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_420_);
v___x_422_ = v___x_405_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; size_t v_sz_426_; size_t v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_405_);
v___x_424_ = lean_array_fget(v_a_403_, v_val_417_);
lean_dec(v_val_417_);
lean_dec(v_a_403_);
v___x_425_ = ((lean_object*)(l_main___closed__16));
v_sz_426_ = lean_array_size(v___x_424_);
v___x_427_ = ((size_t)0ULL);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_426_, v___x_427_, v___x_424_);
v___y_305_ = v___y_391_;
v_fst_306_ = v___x_425_;
v_snd_307_ = v___x_428_;
goto v___jp_304_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v___x_416_);
lean_dec(v_a_403_);
lean_dec_ref(v___y_391_);
v___x_429_ = ((lean_object*)(l_main___closed__18));
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_429_);
v___x_431_ = v___x_405_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v___y_391_);
v_a_434_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_402_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_402_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v___y_391_);
v_a_442_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_398_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_398_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v___y_391_);
v_a_450_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_395_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_395_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_main___closed__23));
v___x_459_ = ((lean_object*)(l_main___closed__40));
v___y_305_ = v___y_391_;
v_fst_306_ = v___x_458_;
v_snd_307_ = v___x_459_;
goto v___jp_304_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_args_302_);
v_a_462_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_389_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_389_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec(v_args_302_);
v_a_470_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_388_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_388_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v_args_302_);
v_a_478_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_385_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_385_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
v___jp_304_:
{
size_t v_sz_308_; size_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint32_t v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_sz_308_ = lean_array_size(v_fst_306_);
v___x_309_ = ((size_t)0ULL);
lean_inc_ref(v_fst_306_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_308_, v___x_309_, v_fst_306_);
v___x_311_ = l_Lean_Options_empty;
v___x_312_ = 0;
v___x_313_ = ((lean_object*)(l_main___closed__0));
v___x_314_ = 0;
v___x_315_ = 1;
v___x_316_ = 2;
v___x_317_ = lean_box(1);
v___x_318_ = l_Lean_importModules(v___x_310_, v___x_311_, v___x_312_, v___x_313_, v___x_314_, v___x_315_, v___x_316_, v___x_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; size_t v_sz_324_; lean_object* v___x_325_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_321_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_322_ = l_Lean_Elab_Command_mkState(v_a_319_, v___x_321_, v___x_311_);
v___x_323_ = lean_st_mk_ref(v___x_322_);
v_sz_324_ = lean_array_size(v_snd_307_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v___y_305_, v_snd_307_, v_sz_324_, v___x_309_, v___x_314_, v___x_320_, v___x_323_);
lean_dec_ref(v_snd_307_);
lean_dec_ref(v___y_305_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_messages_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = lean_st_ref_get(v___x_323_);
lean_dec(v___x_323_);
v_messages_328_ = lean_ctor_get(v___x_327_, 1);
lean_inc_ref(v_messages_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_MessageLog_toList(v_messages_328_);
lean_dec_ref(v_messages_328_);
v___x_330_ = lean_box(0);
v___x_331_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_344_; 
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v___x_331_, 0);
lean_dec(v_unused_345_);
v___x_333_ = v___x_331_;
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
else
{
lean_dec(v___x_331_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
uint8_t v___x_335_; 
v___x_335_ = lean_unbox(v_a_326_);
lean_dec(v_a_326_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = l_main___boxed__const__1;
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_main___boxed__const__2;
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_326_);
v_a_346_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_331_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_331_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v___x_323_);
v_a_354_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_325_, 1);
v___x_355_ = l_Lean_Exception_toMessageData(v_a_354_);
v___x_356_ = l_Lean_MessageData_toString(v___x_355_);
v___x_357_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_366_);
v___x_359_ = v___x_357_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_dec(v___x_357_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = l_main___boxed__const__3;
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
v_a_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_snd_307_);
lean_dec_ref(v___y_305_);
v_a_375_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_318_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_318_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = _lean_main(v_args_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2(lean_object* v_as_489_, lean_object* v_as_x27_490_, lean_object* v_b_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(v_as_x27_490_, v_b_491_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__2___boxed(lean_object* v_as_495_, lean_object* v_as_x27_496_, lean_object* v_b_497_, lean_object* v_a_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_List_forIn_x27_loop___at___00main_spec__2(v_as_495_, v_as_x27_496_, v_b_497_, v_a_498_);
lean_dec(v_as_x27_496_);
lean_dec(v_as_495_);
return v_res_500_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NHS__ProofDriver(uint8_t builtin) {
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
  res = initialize_NHS__ProofDriver(1 /* builtin */);
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
