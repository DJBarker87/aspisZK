// Lean compiler output
// Module: NMP_BM_ProofDriver
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Array_contains___at___00Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__3(lean_object*, lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_lines(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_NEP_audit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
lean_object* l_NFA__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_NER_referenceNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NER_referenceNames___closed__0 = (const lean_object*)&l_NER_referenceNames___closed__0_value;
LEAN_EXPORT lean_object* l_NER_referenceNames(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_NER_canonicalImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NER_canonicalImports___closed__0 = (const lean_object*)&l_NER_canonicalImports___closed__0_value;
LEAN_EXPORT lean_object* l_NER_canonicalImports(lean_object*);
LEAN_EXPORT lean_object* l_NER_canonicalImports___boxed(lean_object*);
LEAN_EXPORT uint8_t l_NER_importsMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NER_importsMatch___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "phase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "own_declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "loader_imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "imports_match"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dangling"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declarations"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edges"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NER_loadedScan(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NER_loadedScan___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00main_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00main_spec__5___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00main_spec__5___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00main_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00main_spec__5___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00main_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "queryscan"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "printAxioms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 183, 89, 85, 6, 216, 148, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "#print"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "axioms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "NEP_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NFN_SCAN_ZERO_DANGLING"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFN_SCAN_FAILED"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFN_LOADED_scan.jsonl"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "NFN_QUERY_LOADED_scan.jsonl"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "NFN_EXPECTED_IMPORTS.jsonl"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_string_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "NFN_QUERY_EXPECTED_IMPORTS.jsonl"};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static const lean_array_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "scan"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEP_Driver"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static lean_once_cell_t l_main___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__11;
static lean_once_cell_t l_main___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__12;
static lean_once_cell_t l_main___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__13;
static lean_once_cell_t l_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__14;
static lean_once_cell_t l_main___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__15;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NMP_BM_AUDIT_ROOTS.json"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "groups"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "proof group out of range"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_ctor_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__20_value)}};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "NMP_BM_AUDIT_MODULES.json"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "module group out of range"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__23_value)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid proof mode"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_ctor_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__25_value)}};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_ctor_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_ctor_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__29_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_array_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__28_value),((lean_object*)&l_main___closed__30_value)}};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_ctor_object l_main___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__33_value_aux_0),((lean_object*)&l_main___closed__32_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_ctor_object l_main___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__35_value_aux_0),((lean_object*)&l_main___closed__34_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_ctor_object l_main___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__37_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_ctor_object l_main___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__27_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__39_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_ctor_object l_main___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__40_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__41_value_aux_0),((lean_object*)&l_main___closed__32_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_ctor_object l_main___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__42_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__43_value_aux_0),((lean_object*)&l_main___closed__34_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_ctor_object l_main___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__44_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__45_value_aux_0),((lean_object*)&l_main___closed__36_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_ctor_object l_main___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__46_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__47_value_aux_0),((lean_object*)&l_main___closed__38_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_array_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__33_value),((lean_object*)&l_main___closed__35_value),((lean_object*)&l_main___closed__37_value),((lean_object*)&l_main___closed__39_value),((lean_object*)&l_main___closed__41_value),((lean_object*)&l_main___closed__43_value),((lean_object*)&l_main___closed__45_value),((lean_object*)&l_main___closed__47_value)}};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* l_main___boxed__const__3;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg(lean_object* v_as_x27_1_, lean_object* v_b_2_){
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg___boxed(lean_object* v_as_x27_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg(v_as_x27_11_, v_b_12_);
lean_dec(v_as_x27_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_NER_referenceNames(lean_object* v_c_16_){
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
v___x_52_ = ((lean_object*)(l_NER_referenceNames___closed__0));
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
v___x_49_ = l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg(v_rules_46_, v_refs_48_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0(lean_object* v_as_55_, lean_object* v_as_x27_56_, lean_object* v_b_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___redArg(v_as_x27_56_, v_b_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0___boxed(lean_object* v_as_60_, lean_object* v_as_x27_61_, lean_object* v_b_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_forIn_x27_loop___at___00NER_referenceNames_spec__0(v_as_60_, v_as_x27_61_, v_b_62_, v_a_63_);
lean_dec(v_as_x27_61_);
lean_dec(v_as_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0(lean_object* v_as_65_, size_t v_sz_66_, size_t v_i_67_, lean_object* v_b_68_){
_start:
{
lean_object* v_a_70_; uint8_t v___x_74_; 
v___x_74_ = lean_usize_dec_lt(v_i_67_, v_sz_66_);
if (v___x_74_ == 0)
{
return v_b_68_;
}
else
{
lean_object* v_a_75_; uint8_t v___x_76_; 
v_a_75_ = lean_array_uget_borrowed(v_as_65_, v_i_67_);
v___x_76_ = l_Array_contains___at___00Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__3(v_b_68_, v_a_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_inc(v_a_75_);
v___x_77_ = lean_array_push(v_b_68_, v_a_75_);
v_a_70_ = v___x_77_;
goto v___jp_69_;
}
else
{
v_a_70_ = v_b_68_;
goto v___jp_69_;
}
}
v___jp_69_:
{
size_t v___x_71_; size_t v___x_72_; 
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_add(v_i_67_, v___x_71_);
v_i_67_ = v___x_72_;
v_b_68_ = v_a_70_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0___boxed(lean_object* v_as_78_, lean_object* v_sz_79_, lean_object* v_i_80_, lean_object* v_b_81_){
_start:
{
size_t v_sz_boxed_82_; size_t v_i_boxed_83_; lean_object* v_res_84_; 
v_sz_boxed_82_ = lean_unbox_usize(v_sz_79_);
lean_dec(v_sz_79_);
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0(v_as_78_, v_sz_boxed_82_, v_i_boxed_83_, v_b_81_);
lean_dec_ref(v_as_78_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_NER_canonicalImports(lean_object* v_xs_87_){
_start:
{
lean_object* v_result_88_; size_t v_sz_89_; size_t v___x_90_; lean_object* v___x_91_; 
v_result_88_ = ((lean_object*)(l_NER_canonicalImports___closed__0));
v_sz_89_ = lean_array_size(v_xs_87_);
v___x_90_ = ((size_t)0ULL);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_canonicalImports_spec__0(v_xs_87_, v_sz_89_, v___x_90_, v_result_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_NER_canonicalImports___boxed(lean_object* v_xs_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_NER_canonicalImports(v_xs_92_);
lean_dec_ref(v_xs_92_);
return v_res_93_;
}
}
LEAN_EXPORT uint8_t l_NER_importsMatch(lean_object* v_actual_94_, lean_object* v_expected_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = l_NER_canonicalImports(v_actual_94_);
v___x_97_ = lean_array_get_size(v___x_96_);
v___x_98_ = lean_array_get_size(v_expected_95_);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec_ref(v___x_96_);
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v___x_96_, v_expected_95_, v___x_97_);
lean_dec_ref(v___x_96_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_NER_importsMatch___boxed(lean_object* v_actual_101_, lean_object* v_expected_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_NER_importsMatch(v_actual_101_, v_expected_102_);
lean_dec_ref(v_expected_102_);
lean_dec_ref(v_actual_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(lean_object* v_env_107_, lean_object* v_val_108_, lean_object* v_as_109_, size_t v_sz_110_, size_t v_i_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_a_115_; uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_lt(v_i_111_, v_sz_110_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v_env_107_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v_b_112_);
return v___x_120_;
}
else
{
lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_152_; 
v_fst_121_ = lean_ctor_get(v_b_112_, 0);
v_snd_122_ = lean_ctor_get(v_b_112_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_b_112_);
if (v_isSharedCheck_152_ == 0)
{
v___x_124_ = v_b_112_;
v_isShared_125_ = v_isSharedCheck_152_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_inc(v_fst_121_);
lean_dec(v_b_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_152_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_checked_126_; lean_object* v___x_127_; lean_object* v_a_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_checked_126_ = lean_ctor_get(v_env_107_, 2);
v___x_127_ = lean_unsigned_to_nat(1u);
v_a_128_ = lean_array_uget_borrowed(v_as_109_, v_i_111_);
v___x_129_ = lean_nat_add(v_snd_122_, v___x_127_);
lean_dec(v_snd_122_);
lean_inc_ref(v_checked_126_);
v___x_130_ = lean_task_get_own(v_checked_126_);
lean_inc(v_a_128_);
v___x_131_ = lean_environment_find(v___x_130_, v_a_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0));
v___x_133_ = l_Lean_ConstantInfo_name(v_val_108_);
v___x_134_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_133_, v___x_119_);
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_135_);
lean_ctor_set(v___x_124_, 0, v___x_132_);
v___x_137_ = v___x_124_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_148_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1));
lean_inc(v_a_128_);
v___x_139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_128_, v___x_119_);
v___x_140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_137_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = l_Lean_Json_mkObj(v___x_144_);
lean_dec_ref_known(v___x_144_, 2);
v___x_146_ = lean_array_push(v_fst_121_, v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_129_);
v_a_115_ = v___x_147_;
goto v___jp_114_;
}
}
else
{
lean_object* v___x_150_; 
lean_dec_ref_known(v___x_131_, 1);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_129_);
v___x_150_ = v___x_124_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_fst_121_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_129_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
v_a_115_ = v___x_150_;
goto v___jp_114_;
}
}
}
}
v___jp_114_:
{
size_t v___x_116_; size_t v___x_117_; 
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_111_, v___x_116_);
v_i_111_ = v___x_117_;
v_b_112_ = v_a_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___boxed(lean_object* v_env_153_, lean_object* v_val_154_, lean_object* v_as_155_, lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_b_158_, lean_object* v___y_159_){
_start:
{
size_t v_sz_boxed_160_; size_t v_i_boxed_161_; lean_object* v_res_162_; 
v_sz_boxed_160_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_161_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(v_env_153_, v_val_154_, v_as_155_, v_sz_boxed_160_, v_i_boxed_161_, v_b_158_);
lean_dec_ref(v_as_155_);
lean_dec_ref(v_val_154_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(lean_object* v_env_173_, lean_object* v_as_174_, size_t v_sz_175_, size_t v_i_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_a_180_; uint8_t v___x_184_; 
v___x_184_ = lean_usize_dec_lt(v_i_176_, v_sz_175_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_dec_ref(v_env_173_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_b_177_);
return v___x_185_;
}
else
{
lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_228_; 
v_fst_186_ = lean_ctor_get(v_b_177_, 0);
v_snd_187_ = lean_ctor_get(v_b_177_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_b_177_);
if (v_isSharedCheck_228_ == 0)
{
v___x_189_ = v_b_177_;
v_isShared_190_ = v_isSharedCheck_228_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snd_187_);
lean_inc(v_fst_186_);
lean_dec(v_b_177_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_228_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_checked_191_; lean_object* v_a_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_checked_191_ = lean_ctor_get(v_env_173_, 2);
v_a_192_ = lean_array_uget_borrowed(v_as_174_, v_i_176_);
lean_inc_ref(v_checked_191_);
v___x_193_ = lean_task_get_own(v_checked_191_);
v___x_194_ = l_Lean_ConstantInfo_name(v_a_192_);
lean_inc(v___x_194_);
v___x_195_ = lean_environment_find(v___x_193_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 1)
{
lean_object* v_val_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
lean_dec(v___x_194_);
v_val_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_n(v_val_196_, 2);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = l_NER_referenceNames(v_val_196_);
if (v_isShared_190_ == 0)
{
v___x_199_ = v___x_189_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_fst_186_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_snd_187_);
v___x_199_ = v_reuseFailAlloc_213_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
size_t v_sz_200_; size_t v___x_201_; lean_object* v___x_202_; 
v_sz_200_ = lean_array_size(v___x_197_);
v___x_201_ = ((size_t)0ULL);
lean_inc_ref(v_env_173_);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(v_env_173_, v_val_196_, v___x_197_, v_sz_200_, v___x_201_, v___x_199_);
lean_dec_ref(v___x_197_);
lean_dec(v_val_196_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_fst_204_; lean_object* v_snd_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_fst_204_ = lean_ctor_get(v_a_203_, 0);
v_snd_205_ = lean_ctor_get(v_a_203_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_203_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v_a_203_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_snd_205_);
lean_inc(v_fst_204_);
lean_dec(v_a_203_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_fst_204_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_snd_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_a_180_ = v___x_210_;
goto v___jp_179_;
}
}
}
else
{
lean_dec_ref(v_env_173_);
return v___x_202_;
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_dec(v___x_195_);
v___x_214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0));
v___x_215_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_194_, v___x_184_);
v___x_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_inc_ref(v___x_216_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_216_);
lean_ctor_set(v___x_189_, 0, v___x_214_);
v___x_218_ = v___x_189_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_227_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_219_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1));
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_216_);
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4));
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_218_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_Json_mkObj(v___x_223_);
lean_dec_ref_known(v___x_223_, 2);
v___x_225_ = lean_array_push(v_fst_186_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_snd_187_);
v_a_180_ = v___x_226_;
goto v___jp_179_;
}
}
}
}
v___jp_179_:
{
size_t v___x_181_; size_t v___x_182_; 
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_add(v_i_176_, v___x_181_);
v_i_176_ = v___x_182_;
v_b_177_ = v_a_180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___boxed(lean_object* v_env_229_, lean_object* v_as_230_, lean_object* v_sz_231_, lean_object* v_i_232_, lean_object* v_b_233_, lean_object* v___y_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_231_);
lean_dec(v_sz_231_);
v_i_boxed_236_ = lean_unbox_usize(v_i_232_);
lean_dec(v_i_232_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(v_env_229_, v_as_230_, v_sz_boxed_235_, v_i_boxed_236_, v_b_233_);
lean_dec_ref(v_as_230_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(size_t v_sz_238_, size_t v_i_239_, lean_object* v_bs_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_241_ == 0)
{
return v_bs_240_;
}
else
{
lean_object* v_v_242_; lean_object* v_module_243_; lean_object* v___x_244_; lean_object* v_bs_x27_245_; lean_object* v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; 
v_v_242_ = lean_array_uget_borrowed(v_bs_240_, v_i_239_);
v_module_243_ = lean_ctor_get(v_v_242_, 0);
lean_inc(v_module_243_);
v___x_244_ = lean_unsigned_to_nat(0u);
v_bs_x27_245_ = lean_array_uset(v_bs_240_, v_i_239_, v___x_244_);
v___x_246_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_243_, v___x_241_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_add(v_i_239_, v___x_247_);
v___x_249_ = lean_array_uset(v_bs_x27_245_, v_i_239_, v___x_246_);
v_i_239_ = v___x_248_;
v_bs_240_ = v___x_249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2___boxed(lean_object* v_sz_251_, lean_object* v_i_252_, lean_object* v_bs_253_){
_start:
{
size_t v_sz_boxed_254_; size_t v_i_boxed_255_; lean_object* v_res_256_; 
v_sz_boxed_254_ = lean_unbox_usize(v_sz_251_);
lean_dec(v_sz_251_);
v_i_boxed_255_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_res_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(v_sz_boxed_254_, v_i_boxed_255_, v_bs_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(lean_object* v___x_269_, lean_object* v_env_270_, lean_object* v___x_271_, lean_object* v_a_272_, lean_object* v_expected_273_, lean_object* v_range_274_, uint8_t v_b_275_, lean_object* v_i_276_){
_start:
{
lean_object* v_stop_278_; lean_object* v_step_279_; uint8_t v___x_280_; 
v_stop_278_ = lean_ctor_get(v_range_274_, 1);
v_step_279_ = lean_ctor_get(v_range_274_, 2);
v___x_280_ = lean_nat_dec_lt(v_i_276_, v_stop_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_i_276_);
lean_dec_ref(v_env_270_);
v___x_281_ = lean_box(v_b_275_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v_moduleData_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_imports_286_; lean_object* v_constants_287_; lean_object* v___x_288_; lean_object* v___x_289_; size_t v_sz_290_; size_t v___x_291_; lean_object* v___x_292_; 
v_moduleData_283_ = lean_ctor_get(v___x_269_, 6);
v___x_284_ = l_Lean_instInhabitedModuleData_default;
v___x_285_ = lean_array_get_borrowed(v___x_284_, v_moduleData_283_, v_i_276_);
v_imports_286_ = lean_ctor_get(v___x_285_, 0);
v_constants_287_ = lean_ctor_get(v___x_285_, 2);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__1));
v_sz_290_ = lean_array_size(v_constants_287_);
v___x_291_ = ((size_t)0ULL);
lean_inc_ref(v_env_270_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(v_env_270_, v_constants_287_, v_sz_290_, v___x_291_, v___x_289_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_365_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v_fst_294_ = lean_ctor_get(v_a_293_, 0);
v_snd_295_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_365_ == 0)
{
v___x_297_ = v_a_293_;
v_isShared_298_ = v_isSharedCheck_365_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snd_295_);
lean_inc(v_fst_294_);
lean_dec(v_a_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_365_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
uint8_t v_failed_299_; lean_object* v___x_300_; size_t v_sz_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___y_306_; uint8_t v_failed_307_; uint8_t v___y_356_; lean_object* v___x_359_; 
v_failed_299_ = 0;
v___x_300_ = lean_array_fget_borrowed(v___x_271_, v_i_276_);
v_sz_301_ = lean_array_size(v_imports_286_);
lean_inc_ref(v_imports_286_);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(v_sz_301_, v___x_291_, v_imports_286_);
v___x_303_ = l_NER_canonicalImports(v___x_302_);
lean_inc(v___x_300_);
v___x_304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_300_, v___x_280_);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_expected_273_, v___x_304_);
if (lean_obj_tag(v___x_359_) == 0)
{
v___y_356_ = v_failed_299_;
goto v___jp_355_;
}
else
{
lean_object* v_val_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_val_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_array_get_size(v___x_303_);
v___x_362_ = lean_array_get_size(v_val_360_);
v___x_363_ = lean_nat_dec_eq(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_val_360_);
v___y_356_ = v_failed_299_;
goto v___jp_355_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v___x_303_, v_val_360_, v___x_361_);
lean_dec(v_val_360_);
v___y_356_ = v___x_364_;
goto v___jp_355_;
}
}
v___jp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2));
v___x_309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_304_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_309_);
lean_ctor_set(v___x_297_, 0, v___x_308_);
v___x_311_ = v___x_297_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_354_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_312_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3));
v___x_313_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_303_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__4));
v___x_316_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_302_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__5));
v___x_319_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_319_, 0, v___y_306_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__6));
v___x_322_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_294_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__7));
v___x_325_ = lean_array_get_size(v_constants_287_);
v___x_326_ = l_Lean_JsonNumber_fromNat(v___x_325_);
v___x_327_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__8));
v___x_330_ = l_Lean_JsonNumber_fromNat(v_snd_295_);
v___x_331_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_328_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_323_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_320_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_317_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_314_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_311_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_Json_mkObj(v___x_340_);
lean_dec_ref_known(v___x_340_, 2);
v___x_342_ = l_Lean_Json_compress(v___x_341_);
v___x_343_ = l_IO_FS_Handle_putStrLn(v_a_272_, v___x_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_343_, 1);
v___x_344_ = lean_nat_add(v_i_276_, v_step_279_);
lean_dec(v_i_276_);
v_b_275_ = v_failed_307_;
v_i_276_ = v___x_344_;
goto _start;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_i_276_);
lean_dec_ref(v_env_270_);
v_a_346_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_343_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_343_);
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
}
v___jp_355_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_array_get_size(v_fst_294_);
v___x_358_ = lean_nat_dec_eq(v___x_357_, v___x_288_);
if (v___x_358_ == 0)
{
v___y_306_ = v___y_356_;
v_failed_307_ = v___x_280_;
goto v___jp_305_;
}
else
{
if (v___y_356_ == 0)
{
v___y_306_ = v___y_356_;
v_failed_307_ = v___x_280_;
goto v___jp_305_;
}
else
{
v___y_306_ = v___y_356_;
v_failed_307_ = v_b_275_;
goto v___jp_305_;
}
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_i_276_);
lean_dec_ref(v_env_270_);
v_a_366_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_292_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_292_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___boxed(lean_object* v___x_374_, lean_object* v_env_375_, lean_object* v___x_376_, lean_object* v_a_377_, lean_object* v_expected_378_, lean_object* v_range_379_, lean_object* v_b_380_, lean_object* v_i_381_, lean_object* v___y_382_){
_start:
{
uint8_t v_b_boxed_383_; lean_object* v_res_384_; 
v_b_boxed_383_ = lean_unbox(v_b_380_);
v_res_384_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_374_, v_env_375_, v___x_376_, v_a_377_, v_expected_378_, v_range_379_, v_b_boxed_383_, v_i_381_);
lean_dec_ref(v_range_379_);
lean_dec_ref(v_expected_378_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_376_);
lean_dec_ref(v___x_374_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_NER_loadedScan(lean_object* v_env_385_, lean_object* v_output_386_, lean_object* v_expected_387_){
_start:
{
uint8_t v___x_389_; lean_object* v___x_390_; 
v___x_389_ = 1;
v___x_390_ = lean_io_prim_handle_mk(v_output_386_, v___x_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; uint8_t v_failed_392_; lean_object* v_env_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v_failed_392_ = 0;
v_env_393_ = l_Lean_Environment_setExporting(v_env_385_, v_failed_392_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_Lean_Environment_header(v_env_393_);
lean_inc_ref(v___x_395_);
v___x_396_ = l_Lean_EnvironmentHeader_moduleNames(v___x_395_);
v___x_397_ = lean_array_get_size(v___x_396_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_394_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
v___x_400_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_395_, v_env_393_, v___x_396_, v_a_391_, v_expected_387_, v___x_399_, v_failed_392_, v___x_394_);
lean_dec_ref_known(v___x_399_, 3);
lean_dec(v_a_391_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v___x_395_);
return v___x_400_;
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_env_385_);
v_a_401_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_390_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NER_loadedScan___boxed(lean_object* v_env_409_, lean_object* v_output_410_, lean_object* v_expected_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_NER_loadedScan(v_env_409_, v_output_410_, v_expected_411_);
lean_dec_ref(v_expected_411_);
lean_dec_ref(v_output_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(lean_object* v___x_414_, lean_object* v_env_415_, lean_object* v___x_416_, lean_object* v_a_417_, lean_object* v_expected_418_, lean_object* v_range_419_, uint8_t v_b_420_, lean_object* v_i_421_, lean_object* v_hs_422_, lean_object* v_hl_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_414_, v_env_415_, v___x_416_, v_a_417_, v_expected_418_, v_range_419_, v_b_420_, v_i_421_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___boxed(lean_object* v___x_426_, lean_object* v_env_427_, lean_object* v___x_428_, lean_object* v_a_429_, lean_object* v_expected_430_, lean_object* v_range_431_, lean_object* v_b_432_, lean_object* v_i_433_, lean_object* v_hs_434_, lean_object* v_hl_435_, lean_object* v___y_436_){
_start:
{
uint8_t v_b_boxed_437_; lean_object* v_res_438_; 
v_b_boxed_437_ = lean_unbox(v_b_432_);
v_res_438_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(v___x_426_, v_env_427_, v___x_428_, v_a_429_, v_expected_430_, v_range_431_, v_b_boxed_437_, v_i_433_, v_hs_434_, v_hl_435_);
lean_dec_ref(v_range_431_);
lean_dec_ref(v_expected_430_);
lean_dec(v_a_429_);
lean_dec_ref(v___x_428_);
lean_dec_ref(v___x_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_bs_441_);
return v___x_443_;
}
else
{
lean_object* v_v_444_; lean_object* v___x_445_; 
v_v_444_ = lean_array_uget_borrowed(v_bs_441_, v_i_440_);
lean_inc(v_v_444_);
v___x_445_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(v_v_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_bs_441_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_455_; lean_object* v_bs_x27_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_a_454_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_445_, 1);
v___x_455_ = lean_unsigned_to_nat(0u);
v_bs_x27_456_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_455_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_440_, v___x_457_);
v___x_459_ = lean_array_uset(v_bs_x27_456_, v_i_440_, v_a_454_);
v_i_440_ = v___x_458_;
v_bs_441_ = v___x_459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5___boxed(lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_bs_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_465_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5(v_sz_boxed_464_, v_i_boxed_465_, v_bs_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00main_spec__5(lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 4)
{
lean_object* v_elems_470_; size_t v_sz_471_; size_t v___x_472_; lean_object* v___x_473_; 
v_elems_470_ = lean_ctor_get(v_x_469_, 0);
lean_inc_ref(v_elems_470_);
lean_dec_ref_known(v_x_469_, 1);
v_sz_471_ = lean_array_size(v_elems_470_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00main_spec__5_spec__5(v_sz_471_, v___x_472_, v_elems_470_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_474_ = ((lean_object*)(l_Array_fromJson_x3f___at___00main_spec__5___closed__0));
v___x_475_ = lean_unsigned_to_nat(80u);
v___x_476_ = l_Lean_Json_pretty(v_x_469_, v___x_475_);
v___x_477_ = lean_string_append(v___x_474_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l_Array_fromJson_x3f___at___00main_spec__5___closed__1));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__4(lean_object* v_j_481_, lean_object* v_k_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = l_Lean_Json_getObjValD(v_j_481_, v_k_482_);
v___x_484_ = l_Array_fromJson_x3f___at___00main_spec__5(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00main_spec__4___boxed(lean_object* v_j_485_, lean_object* v_k_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Json_getObjValAs_x3f___at___00main_spec__4(v_j_485_, v_k_486_);
lean_dec_ref(v_k_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_488_, size_t v_i_489_, lean_object* v_bs_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_491_ == 0)
{
return v_bs_490_;
}
else
{
lean_object* v_v_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; uint8_t v___x_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_v_492_ = lean_array_uget(v_bs_490_, v_i_489_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_490_, v_i_489_, v___x_493_);
v___x_495_ = 0;
v___x_496_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_496_, 0, v_v_492_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_491_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1 + 1, v___x_491_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1 + 2, v___x_495_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_489_, v___x_497_);
v___x_499_ = lean_array_uset(v_bs_x27_494_, v_i_489_, v___x_496_);
v_i_489_ = v___x_498_;
v_bs_490_ = v___x_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_505_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_504_, v_i_boxed_505_, v_bs_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_as_507_, size_t v_sz_508_, size_t v_i_509_, lean_object* v_b_510_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_509_, v_sz_508_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_b_510_);
return v___x_513_;
}
else
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_514_ = lean_array_uget_borrowed(v_as_507_, v_i_509_);
lean_inc(v_a_514_);
v___x_515_ = l_Lean_Json_parse(v_a_514_);
v___x_516_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc_n(v_a_517_, 2);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2));
v___x_519_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(v_a_517_, v___x_518_);
v___x_520_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3));
v___x_523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(v_a_517_, v___x_522_);
v___x_524_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_523_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; size_t v___x_527_; size_t v___x_528_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_b_510_, v_a_521_, v_a_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_509_, v___x_527_);
v_i_509_ = v___x_528_;
v_b_510_ = v___x_526_;
goto _start;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_521_);
lean_dec_ref(v_b_510_);
v_a_530_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_524_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_524_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_a_517_);
lean_dec_ref(v_b_510_);
v_a_538_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_520_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_520_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v_b_510_);
v_a_546_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_516_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_516_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_as_554_, lean_object* v_sz_555_, lean_object* v_i_556_, lean_object* v_b_557_, lean_object* v___y_558_){
_start:
{
size_t v_sz_boxed_559_; size_t v_i_boxed_560_; lean_object* v_res_561_; 
v_sz_boxed_559_ = lean_unbox_usize(v_sz_555_);
lean_dec(v_sz_555_);
v_i_boxed_560_ = lean_unbox_usize(v_i_556_);
lean_dec(v_i_556_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_as_554_, v_sz_boxed_559_, v_i_boxed_560_, v_b_557_);
lean_dec_ref(v_as_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_562_, lean_object* v_b_563_){
_start:
{
if (lean_obj_tag(v_as_x27_562_) == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_b_563_);
return v___x_565_;
}
else
{
lean_object* v_head_566_; lean_object* v_tail_567_; lean_object* v_data_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_head_566_ = lean_ctor_get(v_as_x27_562_, 0);
v_tail_567_ = lean_ctor_get(v_as_x27_562_, 1);
v_data_568_ = lean_ctor_get(v_head_566_, 4);
lean_inc(v_data_568_);
v___x_569_ = l_Lean_MessageData_toString(v_data_568_);
v___x_570_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; 
lean_dec_ref_known(v___x_570_, 1);
v___x_571_ = lean_box(0);
v_as_x27_562_ = v_tail_567_;
v_b_563_ = v___x_571_;
goto _start;
}
else
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_573_, lean_object* v_b_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_573_, v_b_574_);
lean_dec(v_as_x27_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6(size_t v_sz_577_, size_t v_i_578_, lean_object* v_bs_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_580_ == 0)
{
return v_bs_579_;
}
else
{
lean_object* v_v_581_; lean_object* v___x_582_; lean_object* v_bs_x27_583_; lean_object* v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v_v_581_ = lean_array_uget(v_bs_579_, v_i_578_);
v___x_582_ = lean_unsigned_to_nat(0u);
v_bs_x27_583_ = lean_array_uset(v_bs_579_, v_i_578_, v___x_582_);
v___x_584_ = l_String_toName(v_v_581_);
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_add(v_i_578_, v___x_585_);
v___x_587_ = lean_array_uset(v_bs_x27_583_, v_i_578_, v___x_584_);
v_i_578_ = v___x_586_;
v_bs_579_ = v___x_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6___boxed(lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_bs_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_593_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6(v_sz_boxed_592_, v_i_boxed_593_, v_bs_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object* v___y_609_, lean_object* v_as_610_, size_t v_sz_611_, size_t v_i_612_, uint8_t v_b_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_snd_618_; uint8_t v___x_623_; lean_object* v_a_625_; 
v___x_623_ = lean_usize_dec_lt(v_i_612_, v_sz_611_);
if (v___x_623_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(v_b_613_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Elab_Command_getRef___redArg(v___y_614_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_614_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_quotContext_x3f_644_; lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v_a_647_; lean_object* v___x_648_; 
lean_dec_ref_known(v___x_643_, 1);
v_quotContext_x3f_644_ = lean_ctor_get(v___y_614_, 5);
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_646_ = lean_string_dec_eq(v___y_609_, v___x_645_);
v_a_647_ = lean_array_uget_borrowed(v_as_610_, v_i_612_);
v___x_648_ = l_Lean_SourceInfo_fromRef(v_a_642_, v___x_646_);
lean_dec(v_a_642_);
if (lean_obj_tag(v_quotContext_x3f_644_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_615_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_dec_ref_known(v___x_668_, 1);
goto v___jp_649_;
}
else
{
lean_object* v_a_669_; 
lean_dec(v___x_648_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v_a_625_ = v_a_669_;
goto v___jp_624_;
}
}
else
{
goto v___jp_649_;
}
v___jp_649_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5));
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6));
lean_inc_n(v___x_648_, 2);
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_648_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7));
v___x_654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_648_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
lean_inc(v_a_647_);
v___x_655_ = lean_mk_syntax_ident(v_a_647_);
v___x_656_ = l_Lean_Syntax_node3(v___x_648_, v___x_650_, v___x_652_, v___x_654_, v___x_655_);
v___x_657_ = l_Lean_Elab_Command_elabCommand(v___x_656_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref_known(v___x_657_, 1);
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8));
v___x_659_ = lean_string_append(v___x_658_, v___y_609_);
v___x_660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
lean_inc_n(v_a_647_, 2);
v___x_662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_647_, v___x_623_);
v___x_663_ = lean_string_append(v___x_661_, v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = l_NEP_audit(v_a_647_, v___x_663_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; 
lean_dec_ref_known(v___x_664_, 1);
v___x_665_ = lean_box(v_b_613_);
v_snd_618_ = v___x_665_;
goto v___jp_617_;
}
else
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_664_, 1);
v_a_625_ = v_a_666_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_667_; 
v_a_667_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_657_, 1);
v_a_625_ = v_a_667_;
goto v___jp_624_;
}
}
}
else
{
lean_object* v_a_670_; 
lean_dec(v_a_642_);
v_a_670_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_643_, 1);
v_a_625_ = v_a_670_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_671_; 
v_a_671_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_641_, 1);
v_a_625_ = v_a_671_;
goto v___jp_624_;
}
}
v___jp_617_:
{
size_t v___x_619_; size_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_612_, v___x_619_);
v___x_621_ = lean_unbox(v_snd_618_);
lean_dec(v_snd_618_);
v_i_612_ = v___x_620_;
v_b_613_ = v___x_621_;
goto _start;
}
v___jp_624_:
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Exception_isInterrupt(v_a_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = l_Lean_Exception_toMessageData(v_a_625_);
v___x_628_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_627_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_629_; 
lean_dec_ref_known(v___x_628_, 1);
v___x_629_ = lean_box(v___x_623_);
v_snd_618_ = v___x_629_;
goto v___jp_617_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_628_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_628_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_a_625_);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object* v___y_672_, lean_object* v_as_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; uint8_t v_b_boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_681_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_b_boxed_682_ = lean_unbox(v_b_676_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_672_, v_as_673_, v_sz_boxed_680_, v_i_boxed_681_, v_b_boxed_682_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_as_673_);
lean_dec_ref(v___y_672_);
return v_res_683_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_unsigned_to_nat(16u);
v___x_690_ = lean_mk_array(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_main___closed__11(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_main___closed__10));
v___x_699_ = l_Lean_FileMap_ofString(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_main___closed__12(void){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_700_ = 0;
v___x_701_ = lean_box(0);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_box(0);
v___x_704_ = lean_box(0);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_obj_once(&l_main___closed__11, &l_main___closed__11_once, _init_l_main___closed__11);
v___x_707_ = ((lean_object*)(l_main___closed__9));
v___x_708_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_706_);
lean_ctor_set(v___x_708_, 2, v___x_705_);
lean_ctor_set(v___x_708_, 3, v___x_705_);
lean_ctor_set(v___x_708_, 4, v___x_704_);
lean_ctor_set(v___x_708_, 5, v___x_703_);
lean_ctor_set(v___x_708_, 6, v___x_702_);
lean_ctor_set(v___x_708_, 7, v___x_701_);
lean_ctor_set(v___x_708_, 8, v___x_703_);
lean_ctor_set(v___x_708_, 9, v___x_703_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*10, v___x_700_);
return v___x_708_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_unsigned_to_nat(32u);
v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
size_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_712_ = ((size_t)5ULL);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_unsigned_to_nat(32u);
v___x_715_ = lean_mk_empty_array_with_capacity(v___x_714_);
v___x_716_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_717_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_713_);
lean_ctor_set(v___x_717_, 3, v___x_713_);
lean_ctor_set_usize(v___x_717_, 4, v___x_712_);
return v___x_717_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(1);
v___x_719_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
v___x_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_ctor_set(v___x_720_, 2, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_798_; lean_object* v___x_799_; 
v___x_798_ = 1;
v___x_799_ = lean_box_uint32(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_800_; lean_object* v___x_801_; 
v___x_800_ = 0;
v___x_801_ = lean_box_uint32(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_802_; lean_object* v___x_803_; 
v___x_802_ = 2;
v___x_803_ = lean_box_uint32(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_804_){
_start:
{
uint8_t v___y_807_; uint32_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_833_; lean_object* v___y_834_; uint32_t v___y_835_; lean_object* v___y_836_; lean_object* v___y_853_; lean_object* v___y_854_; size_t v___y_855_; uint8_t v___y_856_; uint32_t v___y_857_; lean_object* v___y_858_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; size_t v___y_887_; uint32_t v___y_888_; lean_object* v___y_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = l_NFA__MemoryLimit_set();
v___x_980_ = ((lean_object*)(l_main___closed__16));
v___x_981_ = l_Lean_findSysroot(v___x_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = lean_box(0);
v___x_984_ = l_Lean_initSearchPath(v_a_982_, v___x_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; 
lean_dec_ref_known(v___x_984_, 1);
v___x_985_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___y_987_; 
lean_dec_ref_known(v___x_985_, 1);
if (lean_obj_tag(v_args_804_) == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = ((lean_object*)(l_main___closed__49));
v___y_987_ = v___x_1101_;
goto v___jp_986_;
}
else
{
lean_object* v_head_1102_; 
v_head_1102_ = lean_ctor_get(v_args_804_, 0);
lean_inc(v_head_1102_);
lean_dec_ref_known(v_args_804_, 2);
v___y_987_ = v_head_1102_;
goto v___jp_986_;
}
v___jp_986_:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = ((lean_object*)(l_main___closed__17));
v___x_989_ = lean_string_dec_eq(v___y_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_main___closed__18));
v___x_991_ = l_IO_FS_readFile(v___x_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_Json_parse(v_a_992_);
v___x_994_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = ((lean_object*)(l_main___closed__19));
v___x_997_ = l_Lean_Json_getObjValAs_x3f___at___00main_spec__4(v_a_995_, v___x_996_);
v___x_998_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1074_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1074_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1074_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1003_ = lean_unsigned_to_nat(5u);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_string_utf8_byte_size(v___y_987_);
lean_inc_ref_n(v___y_987_, 2);
v___x_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___y_987_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
v___x_1007_ = l_String_Slice_Pos_nextn(v___x_1006_, v___x_1004_, v___x_1003_);
lean_dec_ref_known(v___x_1006_, 3);
v___x_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___y_987_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
lean_ctor_set(v___x_1008_, 2, v___x_1005_);
v___x_1009_ = l_String_Slice_toString(v___x_1008_);
lean_dec_ref_known(v___x_1008_, 3);
v___x_1010_ = lean_string_utf8_byte_size(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1004_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
v___x_1012_ = l_String_Slice_toNat_x3f(v___x_1011_);
lean_dec_ref_known(v___x_1011_, 3);
if (lean_obj_tag(v___x_1012_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_val_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = lean_array_get_size(v_a_999_);
v___x_1015_ = lean_nat_dec_lt(v_val_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
lean_dec(v_val_1013_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v___x_1016_ = ((lean_object*)(l_main___closed__21));
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
lean_ctor_set(v___x_1001_, 0, v___x_1016_);
v___x_1018_ = v___x_1001_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_del_object(v___x_1001_);
v___x_1020_ = ((lean_object*)(l_main___closed__22));
v___x_1021_ = l_IO_FS_readFile(v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_Json_parse(v_a_1022_);
v___x_1024_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Array_fromJson_x3f___at___00main_spec__5(v_a_1025_);
v___x_1027_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1045_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1045_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1045_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_a_1028_);
v___x_1033_ = lean_nat_dec_lt(v_val_1013_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec(v_a_1028_);
lean_dec(v_val_1013_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v___x_1034_ = ((lean_object*)(l_main___closed__24));
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; size_t v_sz_1043_; lean_object* v___x_1044_; 
lean_del_object(v___x_1030_);
v___x_1038_ = lean_array_fget(v_a_999_, v_val_1013_);
lean_dec(v_a_999_);
v___x_1039_ = lean_array_fget(v_a_1028_, v_val_1013_);
lean_dec(v_val_1013_);
lean_dec(v_a_1028_);
v_sz_1040_ = lean_array_size(v___x_1039_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6(v_sz_1040_, v___x_1041_, v___x_1039_);
v_sz_1043_ = lean_array_size(v___x_1038_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__6(v_sz_1043_, v___x_1041_, v___x_1038_);
v___y_896_ = v___y_987_;
v_fst_897_ = v___x_1042_;
v_snd_898_ = v___x_1044_;
goto v___jp_895_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_val_1013_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v_a_1046_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1027_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1027_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_val_1013_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v_a_1054_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1024_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1024_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_val_1013_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v_a_1062_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1021_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1021_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec(v___x_1012_);
lean_dec(v_a_999_);
lean_dec_ref(v___y_987_);
v___x_1070_ = ((lean_object*)(l_main___closed__26));
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
lean_ctor_set(v___x_1001_, 0, v___x_1070_);
v___x_1072_ = v___x_1001_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v___y_987_);
v_a_1075_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_998_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_998_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v___y_987_);
v_a_1083_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_994_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_994_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___y_987_);
v_a_1091_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_991_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_991_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_main___closed__31));
v___x_1100_ = ((lean_object*)(l_main___closed__48));
v___y_896_ = v___y_987_;
v_fst_897_ = v___x_1099_;
v_snd_898_ = v___x_1100_;
goto v___jp_895_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_args_804_);
v_a_1103_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_985_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_985_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_args_804_);
v_a_1111_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_984_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_984_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_args_804_);
v_a_1119_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_981_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_981_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
v___jp_806_:
{
lean_object* v___x_810_; 
lean_inc_ref(v___y_809_);
v___x_810_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___y_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_810_, 0);
lean_dec(v_unused_823_);
v___x_812_ = v___x_810_;
v_isShared_813_ = v_isSharedCheck_822_;
goto v_resetjp_811_;
}
else
{
lean_dec(v___x_810_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_822_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (v___y_807_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_box_uint32(v___y_808_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = l_main___boxed__const__1;
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_818_);
v___x_820_ = v___x_812_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_810_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_810_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_837_; 
v___x_837_ = l_NER_loadedScan(v___y_834_, v___y_836_, v___y_833_);
lean_dec_ref(v___y_833_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = lean_unbox(v_a_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = ((lean_object*)(l_main___closed__0));
v___x_841_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
v___y_807_ = v___x_841_;
v___y_808_ = v___y_835_;
v___y_809_ = v___x_840_;
goto v___jp_806_;
}
else
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = ((lean_object*)(l_main___closed__1));
v___x_843_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
v___y_807_ = v___x_843_;
v___y_808_ = v___y_835_;
v___y_809_ = v___x_842_;
goto v___jp_806_;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_837_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_837_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
v___jp_852_:
{
lean_object* v___x_859_; 
v___x_859_ = l_IO_FS_lines(v___y_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; size_t v_sz_861_; lean_object* v___x_862_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v_sz_861_ = lean_array_size(v_a_860_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_a_860_, v_sz_861_, v___y_855_, v___y_854_);
lean_dec(v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
if (v___y_856_ == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = ((lean_object*)(l_main___closed__2));
v___y_833_ = v_a_863_;
v___y_834_ = v___y_853_;
v___y_835_ = v___y_857_;
v___y_836_ = v___x_864_;
goto v___jp_832_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_862_, 1);
v___x_866_ = ((lean_object*)(l_main___closed__3));
v___y_833_ = v_a_865_;
v___y_834_ = v___y_853_;
v___y_835_ = v___y_857_;
v___y_836_ = v___x_866_;
goto v___jp_832_;
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v___y_853_);
v_a_867_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_862_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_862_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
v_a_875_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_859_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_859_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
v___jp_883_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_889_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___y_884_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_892_ = lean_string_dec_eq(v___y_885_, v___x_891_);
lean_dec_ref(v___y_885_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = ((lean_object*)(l_main___closed__5));
v___y_853_ = v___y_886_;
v___y_854_ = v___x_890_;
v___y_855_ = v___y_887_;
v___y_856_ = v___x_892_;
v___y_857_ = v___y_888_;
v___y_858_ = v___x_893_;
goto v___jp_852_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = ((lean_object*)(l_main___closed__6));
v___y_853_ = v___y_886_;
v___y_854_ = v___x_890_;
v___y_855_ = v___y_887_;
v___y_856_ = v___x_892_;
v___y_857_ = v___y_888_;
v___y_858_ = v___x_894_;
goto v___jp_852_;
}
}
v___jp_895_:
{
size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint32_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_sz_899_ = lean_array_size(v_fst_897_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_899_, v___x_900_, v_fst_897_);
v___x_902_ = l_Lean_Options_empty;
v___x_903_ = 0;
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = ((lean_object*)(l_main___closed__7));
v___x_906_ = 0;
v___x_907_ = 1;
v___x_908_ = 2;
v___x_909_ = lean_box(1);
v___x_910_ = l_Lean_importModules(v___x_901_, v___x_902_, v___x_903_, v___x_905_, v___x_906_, v___x_907_, v___x_908_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = ((lean_object*)(l_main___closed__8));
v___x_913_ = lean_string_dec_eq(v___y_896_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_915_ = lean_string_dec_eq(v___y_896_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; lean_object* v___x_921_; 
v___x_916_ = lean_obj_once(&l_main___closed__12, &l_main___closed__12_once, _init_l_main___closed__12);
v___x_917_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
v___x_918_ = l_Lean_Elab_Command_mkState(v_a_911_, v___x_917_, v___x_902_);
v___x_919_ = lean_st_mk_ref(v___x_918_);
v_sz_920_ = lean_array_size(v_snd_898_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_896_, v_snd_898_, v_sz_920_, v___x_900_, v___x_906_, v___x_916_, v___x_919_);
lean_dec_ref(v_snd_898_);
lean_dec_ref(v___y_896_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v_messages_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = lean_st_ref_get(v___x_919_);
lean_dec(v___x_919_);
v_messages_924_ = lean_ctor_get(v___x_923_, 1);
lean_inc_ref(v_messages_924_);
lean_dec(v___x_923_);
v___x_925_ = l_Lean_MessageLog_toList(v_messages_924_);
lean_dec_ref(v_messages_924_);
v___x_926_ = lean_box(0);
v___x_927_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v___x_925_, v___x_926_);
lean_dec(v___x_925_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_941_);
v___x_929_ = v___x_927_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_927_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_a_922_);
lean_dec(v_a_922_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_main___boxed__const__2;
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_main___boxed__const__1;
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_922_);
v_a_942_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_927_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_927_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v___x_919_);
v_a_950_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_921_, 1);
v___x_951_ = l_Lean_Exception_toMessageData(v_a_950_);
v___x_952_ = l_Lean_MessageData_toString(v___x_951_);
v___x_953_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v___x_953_, 0);
lean_dec(v_unused_962_);
v___x_955_ = v___x_953_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_dec(v___x_953_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = l_main___boxed__const__3;
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_953_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_953_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
lean_dec_ref(v_snd_898_);
v___y_884_ = v___x_904_;
v___y_885_ = v___y_896_;
v___y_886_ = v_a_911_;
v___y_887_ = v___x_900_;
v___y_888_ = v___x_903_;
goto v___jp_883_;
}
}
else
{
lean_dec_ref(v_snd_898_);
v___y_884_ = v___x_904_;
v___y_885_ = v___y_896_;
v___y_886_ = v_a_911_;
v___y_887_ = v___x_900_;
v___y_888_ = v___x_903_;
goto v___jp_883_;
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_snd_898_);
lean_dec_ref(v___y_896_);
v_a_971_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_910_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_910_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = _lean_main(v_args_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_1130_, lean_object* v_as_x27_1131_, lean_object* v_b_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1131_, v_b_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_1136_, lean_object* v_as_x27_1137_, lean_object* v_b_1138_, lean_object* v_a_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_1136_, v_as_x27_1137_, v_b_1138_, v_a_1139_);
lean_dec(v_as_x27_1137_);
lean_dec(v_as_1136_);
return v_res_1141_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NMP__BM__ProofDriver(uint8_t builtin) {
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
  res = initialize_NMP__BM__ProofDriver(1 /* builtin */);
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
