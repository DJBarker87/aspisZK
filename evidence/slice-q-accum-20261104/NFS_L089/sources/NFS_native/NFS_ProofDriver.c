// Lean compiler output
// Module: NFS_ProofDriver
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_IO_FS_lines(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_NFA__MemoryLimit_set();
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_NEP_audit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_array_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "scan"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NEP_Driver"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static lean_once_cell_t l_main___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__12;
static lean_once_cell_t l_main___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__13;
static lean_once_cell_t l_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__14;
static lean_once_cell_t l_main___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__15;
static lean_once_cell_t l_main___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__16;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof0"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof1"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof2"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof3"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_string_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof4"};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_string_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof5"};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof6"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_string_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof7"};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof8"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_string_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof9"};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_string_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof10"};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof11"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
static const lean_string_object l_main___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof12"};
static const lean_object* l_main___closed__29 = (const lean_object*)&l_main___closed__29_value;
static const lean_string_object l_main___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof13"};
static const lean_object* l_main___closed__30 = (const lean_object*)&l_main___closed__30_value;
static const lean_string_object l_main___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof14"};
static const lean_object* l_main___closed__31 = (const lean_object*)&l_main___closed__31_value;
static const lean_string_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof15"};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_string_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof16"};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof17"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof18"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static const lean_string_object l_main___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof19"};
static const lean_object* l_main___closed__36 = (const lean_object*)&l_main___closed__36_value;
static const lean_string_object l_main___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof20"};
static const lean_object* l_main___closed__37 = (const lean_object*)&l_main___closed__37_value;
static const lean_string_object l_main___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof21"};
static const lean_object* l_main___closed__38 = (const lean_object*)&l_main___closed__38_value;
static const lean_string_object l_main___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof22"};
static const lean_object* l_main___closed__39 = (const lean_object*)&l_main___closed__39_value;
static const lean_string_object l_main___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof23"};
static const lean_object* l_main___closed__40 = (const lean_object*)&l_main___closed__40_value;
static const lean_string_object l_main___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof24"};
static const lean_object* l_main___closed__41 = (const lean_object*)&l_main___closed__41_value;
static const lean_string_object l_main___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof25"};
static const lean_object* l_main___closed__42 = (const lean_object*)&l_main___closed__42_value;
static const lean_string_object l_main___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof26"};
static const lean_object* l_main___closed__43 = (const lean_object*)&l_main___closed__43_value;
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_string_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_ctor_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__45_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_ctor_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__47_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_array_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__46_value),((lean_object*)&l_main___closed__48_value)}};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_string_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_ctor_object l_main___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__45_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__51_value_aux_0),((lean_object*)&l_main___closed__50_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_string_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_ctor_object l_main___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__45_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__53_value_aux_0),((lean_object*)&l_main___closed__52_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_ctor_object l_main___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__45_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__55_value_aux_0),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_ctor_object l_main___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__45_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__57_value_aux_0),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_string_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_ctor_object l_main___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__58_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__59_value_aux_0),((lean_object*)&l_main___closed__50_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_ctor_object l_main___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__60_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__61_value_aux_0),((lean_object*)&l_main___closed__52_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_ctor_object l_main___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__62_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__63_value_aux_0),((lean_object*)&l_main___closed__54_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_ctor_object l_main___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__64_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__65_value_aux_0),((lean_object*)&l_main___closed__56_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_array_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__51_value),((lean_object*)&l_main___closed__53_value),((lean_object*)&l_main___closed__55_value),((lean_object*)&l_main___closed__57_value),((lean_object*)&l_main___closed__59_value),((lean_object*)&l_main___closed__61_value),((lean_object*)&l_main___closed__63_value),((lean_object*)&l_main___closed__65_value)}};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_string_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFS_COMBINED_IMPORT"};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_ctor_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__67_value),LEAN_SCALAR_PTR_LITERAL(212, 189, 165, 130, 177, 217, 150, 88)}};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_array_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__68_value)}};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_string_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_string_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFM_Cuts"};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_string_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abort_prefix"};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_ctor_object l_main___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__73_value_aux_0),((lean_object*)&l_main___closed__71_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__73_value_aux_1),((lean_object*)&l_main___closed__72_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 251, 208, 222, 37, 175, 67)}};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_string_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFG_PushRoot"};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_string_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "private_result"};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_ctor_object l_main___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__76_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(85, 13, 2, 171, 254, 60, 240, 22)}};
static const lean_ctor_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__76_value_aux_1),((lean_object*)&l_main___closed__75_value),LEAN_SCALAR_PTR_LITERAL(155, 139, 182, 186, 62, 49, 38, 31)}};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_string_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public_result"};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_ctor_object l_main___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__78_value_aux_0),((lean_object*)&l_main___closed__74_value),LEAN_SCALAR_PTR_LITERAL(85, 13, 2, 171, 254, 60, 240, 22)}};
static const lean_ctor_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__78_value_aux_1),((lean_object*)&l_main___closed__77_value),LEAN_SCALAR_PTR_LITERAL(49, 51, 175, 173, 11, 29, 130, 140)}};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_array_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__73_value),((lean_object*)&l_main___closed__76_value),((lean_object*)&l_main___closed__78_value)}};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_string_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_TraceBack"};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_string_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "erased"};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_ctor_object l_main___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_0),((lean_object*)&l_main___closed__80_value),LEAN_SCALAR_PTR_LITERAL(228, 208, 177, 232, 3, 41, 145, 13)}};
static const lean_ctor_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__82_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(6, 201, 57, 224, 163, 102, 168, 215)}};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_string_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_TraceFront"};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_ctor_object l_main___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_0),((lean_object*)&l_main___closed__83_value),LEAN_SCALAR_PTR_LITERAL(228, 60, 113, 141, 82, 197, 154, 61)}};
static const lean_ctor_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__84_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(6, 109, 36, 76, 116, 231, 56, 91)}};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_string_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_TraceHead"};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_ctor_object l_main___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__86_value_aux_0),((lean_object*)&l_main___closed__85_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 13, 36, 107, 160, 118, 25)}};
static const lean_ctor_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__86_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(111, 172, 169, 230, 75, 204, 193, 246)}};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_string_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_TraceTypes"};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_string_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pure_result"};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_ctor_object l_main___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__89_value_aux_0),((lean_object*)&l_main___closed__87_value),LEAN_SCALAR_PTR_LITERAL(131, 69, 159, 108, 193, 225, 136, 106)}};
static const lean_ctor_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__89_value_aux_1),((lean_object*)&l_main___closed__88_value),LEAN_SCALAR_PTR_LITERAL(36, 152, 130, 186, 254, 125, 235, 214)}};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_array_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__82_value),((lean_object*)&l_main___closed__84_value),((lean_object*)&l_main___closed__86_value),((lean_object*)&l_main___closed__89_value)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFP_Resume"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_string_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tx2"};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_ctor_object l_main___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__93_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 155, 253, 196, 128, 147, 219)}};
static const lean_ctor_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__93_value_aux_1),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(164, 212, 12, 61, 21, 155, 255, 214)}};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_string_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_ReturnCuts"};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_ctor_object l_main___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__95_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(101, 95, 58, 219, 88, 245, 49, 54)}};
static const lean_ctor_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__95_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(27, 66, 29, 186, 36, 232, 197, 61)}};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_string_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "continuation"};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_ctor_object l_main___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__97_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_0),((lean_object*)&l_main___closed__94_value),LEAN_SCALAR_PTR_LITERAL(101, 95, 58, 219, 88, 245, 49, 54)}};
static const lean_ctor_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__97_value_aux_1),((lean_object*)&l_main___closed__96_value),LEAN_SCALAR_PTR_LITERAL(164, 56, 190, 19, 92, 227, 64, 20)}};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_string_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_SuffixCuts"};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_string_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_ctor_object l_main___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_0),((lean_object*)&l_main___closed__98_value),LEAN_SCALAR_PTR_LITERAL(65, 23, 102, 118, 189, 152, 124, 107)}};
static const lean_ctor_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(127, 234, 223, 104, 109, 168, 128, 242)}};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_array_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__93_value),((lean_object*)&l_main___closed__95_value),((lean_object*)&l_main___closed__97_value),((lean_object*)&l_main___closed__100_value)}};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_string_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_QueryCuts"};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_ctor_object l_main___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_0),((lean_object*)&l_main___closed__102_value),LEAN_SCALAR_PTR_LITERAL(186, 77, 88, 39, 124, 223, 121, 161)}};
static const lean_ctor_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__103_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(152, 36, 48, 173, 235, 7, 28, 79)}};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_string_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFP_RejectionTrace"};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_string_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "guard"};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_ctor_object l_main___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_0),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(218, 18, 186, 94, 233, 180, 60, 161)}};
static const lean_ctor_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__106_value_aux_1),((lean_object*)&l_main___closed__105_value),LEAN_SCALAR_PTR_LITERAL(190, 249, 137, 76, 151, 14, 71, 208)}};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_string_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "rejected_prefix"};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_ctor_object l_main___closed__108_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__108_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__108_value_aux_0),((lean_object*)&l_main___closed__104_value),LEAN_SCALAR_PTR_LITERAL(218, 18, 186, 94, 233, 180, 60, 161)}};
static const lean_ctor_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__108_value_aux_1),((lean_object*)&l_main___closed__107_value),LEAN_SCALAR_PTR_LITERAL(73, 159, 29, 119, 29, 229, 38, 90)}};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_string_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tx1"};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_ctor_object l_main___closed__110_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__110_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__110_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 155, 253, 196, 128, 147, 219)}};
static const lean_ctor_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__110_value_aux_1),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(193, 89, 191, 135, 34, 89, 82, 193)}};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_array_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__103_value),((lean_object*)&l_main___closed__106_value),((lean_object*)&l_main___closed__108_value),((lean_object*)&l_main___closed__110_value)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_ProductLaw"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_string_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "emitted"};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_ctor_object l_main___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__114_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__114_value_aux_0),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(82, 99, 204, 19, 159, 121, 29, 12)}};
static const lean_ctor_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__114_value_aux_1),((lean_object*)&l_main___closed__113_value),LEAN_SCALAR_PTR_LITERAL(147, 167, 163, 146, 188, 84, 216, 226)}};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_string_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_ctor_object l_main___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__116_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__116_value_aux_0),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(82, 99, 204, 19, 159, 121, 29, 12)}};
static const lean_ctor_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__116_value_aux_1),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(253, 61, 135, 74, 12, 214, 122, 116)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_string_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFP_QueryAdvance"};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "accepted"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_ctor_object l_main___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(252, 24, 77, 116, 29, 133, 154, 64)}};
static const lean_ctor_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__119_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(244, 82, 166, 211, 18, 187, 196, 181)}};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_string_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_ctor_object l_main___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_0),((lean_object*)&l_main___closed__117_value),LEAN_SCALAR_PTR_LITERAL(252, 24, 77, 116, 29, 133, 154, 64)}};
static const lean_ctor_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__121_value_aux_1),((lean_object*)&l_main___closed__120_value),LEAN_SCALAR_PTR_LITERAL(234, 88, 84, 215, 168, 32, 254, 33)}};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_array_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__114_value),((lean_object*)&l_main___closed__116_value),((lean_object*)&l_main___closed__119_value),((lean_object*)&l_main___closed__121_value)}};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_string_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFP_NodeDictionary"};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_ctor_object l_main___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__124_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__124_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__124_value_aux_1),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(108, 195, 202, 172, 5, 134, 119, 176)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFP_ObserverErasure"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_string_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "query"};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_ctor_object l_main___closed__127_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__127_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__127_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__127_value_aux_1),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(99, 92, 185, 58, 113, 121, 218, 190)}};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_ctor_object l_main___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__128_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__128_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 21, 20, 52, 233, 15, 11, 167)}};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_string_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_ctor_object l_main___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_1),((lean_object*)&l_main___closed__129_value),LEAN_SCALAR_PTR_LITERAL(235, 153, 248, 117, 174, 251, 56, 187)}};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_array_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__124_value),((lean_object*)&l_main___closed__127_value),((lean_object*)&l_main___closed__128_value),((lean_object*)&l_main___closed__130_value)}};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_string_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_NatBase"};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_string_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_ctor_object l_main___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__134_value_aux_0),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__134_value_aux_1),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(201, 220, 6, 88, 194, 28, 147, 123)}};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_string_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "product"};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_ctor_object l_main___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__136_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__136_value_aux_1),((lean_object*)&l_main___closed__135_value),LEAN_SCALAR_PTR_LITERAL(201, 162, 245, 140, 25, 206, 167, 18)}};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_string_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_ctor_object l_main___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__138_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__138_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__138_value_aux_1),((lean_object*)&l_main___closed__137_value),LEAN_SCALAR_PTR_LITERAL(238, 169, 201, 8, 87, 117, 100, 21)}};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_ctor_object l_main___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__139_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__139_value_aux_1),((lean_object*)&l_main___closed__133_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 31, 192, 139, 25, 153, 132)}};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_array_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__134_value),((lean_object*)&l_main___closed__136_value),((lean_object*)&l_main___closed__138_value),((lean_object*)&l_main___closed__139_value)}};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_string_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFP_LoopTerminals"};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_string_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "diverged"};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_ctor_object l_main___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__143_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__143_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__143_value_aux_1),((lean_object*)&l_main___closed__142_value),LEAN_SCALAR_PTR_LITERAL(122, 15, 102, 113, 216, 62, 46, 226)}};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_string_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFP_LoopTransport"};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_string_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "child"};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_ctor_object l_main___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__146_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_0),((lean_object*)&l_main___closed__144_value),LEAN_SCALAR_PTR_LITERAL(39, 227, 16, 37, 232, 157, 112, 26)}};
static const lean_ctor_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_1),((lean_object*)&l_main___closed__145_value),LEAN_SCALAR_PTR_LITERAL(204, 255, 184, 193, 155, 231, 255, 204)}};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_string_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sub_word"};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_ctor_object l_main___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__148_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_0),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__148_value_aux_1),((lean_object*)&l_main___closed__147_value),LEAN_SCALAR_PTR_LITERAL(207, 79, 41, 175, 58, 149, 134, 117)}};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_ctor_object l_main___closed__149_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__149_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__149_value_aux_0),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__149_value_aux_1),((lean_object*)&l_main___closed__137_value),LEAN_SCALAR_PTR_LITERAL(146, 182, 100, 241, 87, 145, 21, 110)}};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_array_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__143_value),((lean_object*)&l_main___closed__146_value),((lean_object*)&l_main___closed__148_value),((lean_object*)&l_main___closed__149_value)}};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_string_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_ctor_object l_main___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__152_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__152_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__152_value_aux_1),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(25, 49, 207, 98, 169, 197, 196, 117)}};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_string_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "stopped"};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_ctor_object l_main___closed__154_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__154_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__154_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__154_value_aux_1),((lean_object*)&l_main___closed__153_value),LEAN_SCALAR_PTR_LITERAL(101, 61, 76, 16, 24, 87, 120, 145)}};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_string_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rejected"};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_ctor_object l_main___closed__156_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__156_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__156_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__156_value_aux_1),((lean_object*)&l_main___closed__155_value),LEAN_SCALAR_PTR_LITERAL(33, 9, 143, 213, 185, 100, 247, 183)}};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_string_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_ctor_object l_main___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__158_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__158_value_aux_0),((lean_object*)&l_main___closed__141_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__158_value_aux_1),((lean_object*)&l_main___closed__157_value),LEAN_SCALAR_PTR_LITERAL(123, 217, 188, 18, 12, 151, 22, 194)}};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_array_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__152_value),((lean_object*)&l_main___closed__154_value),((lean_object*)&l_main___closed__156_value),((lean_object*)&l_main___closed__158_value)}};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_string_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_HeadDomain"};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_string_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reached"};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_ctor_object l_main___closed__162_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__162_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_0),((lean_object*)&l_main___closed__160_value),LEAN_SCALAR_PTR_LITERAL(54, 156, 46, 216, 87, 232, 209, 148)}};
static const lean_ctor_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__162_value_aux_1),((lean_object*)&l_main___closed__161_value),LEAN_SCALAR_PTR_LITERAL(252, 53, 106, 13, 197, 125, 193, 40)}};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_string_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_LoopBudget"};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_ctor_object l_main___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__164_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_0),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_1),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(215, 32, 253, 208, 7, 40, 225, 30)}};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_ctor_object l_main___closed__165_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__165_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__165_value_aux_0),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__165_value_aux_1),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(58, 60, 42, 170, 54, 246, 3, 65)}};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_string_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "maximum"};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_ctor_object l_main___closed__167_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__167_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__167_value_aux_0),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__167_value_aux_1),((lean_object*)&l_main___closed__166_value),LEAN_SCALAR_PTR_LITERAL(130, 237, 83, 249, 24, 24, 197, 67)}};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_array_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__162_value),((lean_object*)&l_main___closed__164_value),((lean_object*)&l_main___closed__165_value),((lean_object*)&l_main___closed__167_value)}};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_string_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_DotInstall"};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_string_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dot_result"};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_ctor_object l_main___closed__171_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__171_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__171_value_aux_0),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(24, 118, 1, 221, 143, 165, 20, 107)}};
static const lean_ctor_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__171_value_aux_1),((lean_object*)&l_main___closed__170_value),LEAN_SCALAR_PTR_LITERAL(155, 210, 244, 116, 168, 80, 94, 36)}};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_string_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_ctor_object l_main___closed__173_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__173_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__173_value_aux_0),((lean_object*)&l_main___closed__169_value),LEAN_SCALAR_PTR_LITERAL(24, 118, 1, 221, 143, 165, 20, 107)}};
static const lean_ctor_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__173_value_aux_1),((lean_object*)&l_main___closed__172_value),LEAN_SCALAR_PTR_LITERAL(136, 117, 249, 217, 14, 238, 209, 212)}};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_string_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFP_FrameExt"};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_string_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_ctor_object l_main___closed__176_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__176_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__176_value_aux_0),((lean_object*)&l_main___closed__174_value),LEAN_SCALAR_PTR_LITERAL(183, 89, 81, 47, 10, 120, 51, 245)}};
static const lean_ctor_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__176_value_aux_1),((lean_object*)&l_main___closed__175_value),LEAN_SCALAR_PTR_LITERAL(220, 145, 195, 127, 154, 20, 177, 165)}};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_string_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFP_GeometryDomains"};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_string_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reads"};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_ctor_object l_main___closed__179_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__179_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__179_value_aux_0),((lean_object*)&l_main___closed__177_value),LEAN_SCALAR_PTR_LITERAL(86, 86, 2, 155, 143, 134, 85, 221)}};
static const lean_ctor_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__179_value_aux_1),((lean_object*)&l_main___closed__178_value),LEAN_SCALAR_PTR_LITERAL(195, 76, 148, 244, 79, 46, 204, 67)}};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_array_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__171_value),((lean_object*)&l_main___closed__173_value),((lean_object*)&l_main___closed__176_value),((lean_object*)&l_main___closed__179_value)}};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_string_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_Carrier"};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_string_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_ctor_object l_main___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__183_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__183_value_aux_0),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__183_value_aux_1),((lean_object*)&l_main___closed__182_value),LEAN_SCALAR_PTR_LITERAL(30, 159, 83, 66, 130, 43, 155, 199)}};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_string_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_DotCaller"};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_string_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tail"};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_ctor_object l_main___closed__186_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__186_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__186_value_aux_0),((lean_object*)&l_main___closed__184_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 230, 43, 184, 60, 163, 4)}};
static const lean_ctor_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__186_value_aux_1),((lean_object*)&l_main___closed__185_value),LEAN_SCALAR_PTR_LITERAL(244, 235, 7, 207, 6, 168, 116, 243)}};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_ctor_object l_main___closed__187_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__187_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__187_value_aux_0),((lean_object*)&l_main___closed__184_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 230, 43, 184, 60, 163, 4)}};
static const lean_ctor_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__187_value_aux_1),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(208, 111, 192, 28, 125, 232, 238, 170)}};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_string_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_DotDomains"};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_string_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "returned"};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_ctor_object l_main___closed__190_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__190_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_0),((lean_object*)&l_main___closed__188_value),LEAN_SCALAR_PTR_LITERAL(176, 127, 218, 117, 196, 215, 101, 155)}};
static const lean_ctor_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_1),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(234, 245, 209, 227, 196, 227, 67, 7)}};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_array_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__183_value),((lean_object*)&l_main___closed__186_value),((lean_object*)&l_main___closed__187_value),((lean_object*)&l_main___closed__190_value)}};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_string_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_Advance"};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_ctor_object l_main___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__193_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_0),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(180, 104, 145, 38, 238, 42, 79, 101)}};
static const lean_ctor_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_1),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(220, 148, 186, 0, 139, 212, 2, 228)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_string_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "from_to"};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_ctor_object l_main___closed__195_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__195_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__195_value_aux_0),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__195_value_aux_1),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(226, 146, 35, 10, 11, 120, 251, 192)}};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_string_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "to_from"};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_ctor_object l_main___closed__197_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__197_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__197_value_aux_0),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__197_value_aux_1),((lean_object*)&l_main___closed__196_value),LEAN_SCALAR_PTR_LITERAL(76, 50, 240, 31, 131, 133, 75, 212)}};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_string_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "words"};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_ctor_object l_main___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__199_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__199_value_aux_0),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__199_value_aux_1),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(186, 109, 129, 71, 129, 137, 136, 22)}};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_array_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__193_value),((lean_object*)&l_main___closed__195_value),((lean_object*)&l_main___closed__197_value),((lean_object*)&l_main___closed__199_value)}};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_string_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFS_PacketRoot"};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_string_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "geometry"};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_ctor_object l_main___closed__203_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__203_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__203_value_aux_0),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__203_value_aux_1),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(251, 42, 19, 196, 180, 170, 191, 231)}};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_ctor_object l_main___closed__204_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__204_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_0),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_1),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(158, 14, 237, 102, 203, 93, 125, 53)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_ctor_object l_main___closed__205_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__205_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__205_value_aux_0),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__205_value_aux_1),((lean_object*)&l_main___closed__126_value),LEAN_SCALAR_PTR_LITERAL(178, 72, 196, 43, 173, 72, 86, 148)}};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
static const lean_string_object l_main___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "loop"};
static const lean_object* l_main___closed__206 = (const lean_object*)&l_main___closed__206_value;
static const lean_ctor_object l_main___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__207_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__207_value_aux_0),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__207_value_aux_1),((lean_object*)&l_main___closed__206_value),LEAN_SCALAR_PTR_LITERAL(141, 132, 113, 147, 92, 201, 135, 255)}};
static const lean_object* l_main___closed__207 = (const lean_object*)&l_main___closed__207_value;
static const lean_array_object l_main___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__203_value),((lean_object*)&l_main___closed__204_value),((lean_object*)&l_main___closed__205_value),((lean_object*)&l_main___closed__207_value)}};
static const lean_object* l_main___closed__208 = (const lean_object*)&l_main___closed__208_value;
static const lean_string_object l_main___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_LoopTraceDefs"};
static const lean_object* l_main___closed__209 = (const lean_object*)&l_main___closed__209_value;
static const lean_string_object l_main___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_main___closed__210 = (const lean_object*)&l_main___closed__210_value;
static const lean_ctor_object l_main___closed__211_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__211_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__211_value_aux_0),((lean_object*)&l_main___closed__209_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__211_value_aux_1),((lean_object*)&l_main___closed__210_value),LEAN_SCALAR_PTR_LITERAL(169, 234, 208, 78, 95, 236, 196, 236)}};
static const lean_object* l_main___closed__211 = (const lean_object*)&l_main___closed__211_value;
static const lean_ctor_object l_main___closed__212_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__212_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__212_value_aux_0),((lean_object*)&l_main___closed__209_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__212_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(17, 195, 30, 85, 240, 70, 48, 233)}};
static const lean_object* l_main___closed__212 = (const lean_object*)&l_main___closed__212_value;
static const lean_string_object l_main___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_LoopTrace"};
static const lean_object* l_main___closed__213 = (const lean_object*)&l_main___closed__213_value;
static const lean_string_object l_main___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "erase_fixed"};
static const lean_object* l_main___closed__214 = (const lean_object*)&l_main___closed__214_value;
static const lean_ctor_object l_main___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__215_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(101, 42, 121, 192, 38, 118, 224, 12)}};
static const lean_ctor_object l_main___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__215_value_aux_1),((lean_object*)&l_main___closed__214_value),LEAN_SCALAR_PTR_LITERAL(181, 107, 11, 202, 159, 42, 150, 134)}};
static const lean_object* l_main___closed__215 = (const lean_object*)&l_main___closed__215_value;
static const lean_ctor_object l_main___closed__216_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__216_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__216_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(101, 42, 121, 192, 38, 118, 224, 12)}};
static const lean_ctor_object l_main___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__216_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(115, 156, 93, 121, 123, 14, 171, 242)}};
static const lean_object* l_main___closed__216 = (const lean_object*)&l_main___closed__216_value;
static const lean_array_object l_main___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__211_value),((lean_object*)&l_main___closed__212_value),((lean_object*)&l_main___closed__215_value),((lean_object*)&l_main___closed__216_value)}};
static const lean_object* l_main___closed__217 = (const lean_object*)&l_main___closed__217_value;
static const lean_string_object l_main___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_QueryLoopRoot"};
static const lean_object* l_main___closed__218 = (const lean_object*)&l_main___closed__218_value;
static const lean_string_object l_main___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l_main___closed__219 = (const lean_object*)&l_main___closed__219_value;
static const lean_ctor_object l_main___closed__220_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__220_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__220_value_aux_0),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__220_value_aux_1),((lean_object*)&l_main___closed__219_value),LEAN_SCALAR_PTR_LITERAL(129, 74, 21, 149, 61, 8, 167, 72)}};
static const lean_object* l_main___closed__220 = (const lean_object*)&l_main___closed__220_value;
static const lean_ctor_object l_main___closed__221_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__221_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__221_value_aux_0),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__221_value_aux_1),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(97, 16, 233, 56, 121, 162, 34, 112)}};
static const lean_object* l_main___closed__221 = (const lean_object*)&l_main___closed__221_value;
static const lean_ctor_object l_main___closed__222_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__222_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__222_value_aux_0),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__222_value_aux_1),((lean_object*)&l_main___closed__92_value),LEAN_SCALAR_PTR_LITERAL(4, 179, 97, 82, 34, 4, 43, 67)}};
static const lean_object* l_main___closed__222 = (const lean_object*)&l_main___closed__222_value;
static const lean_string_object l_main___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bind_congr"};
static const lean_object* l_main___closed__223 = (const lean_object*)&l_main___closed__223_value;
static const lean_ctor_object l_main___closed__224_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__224_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_0),((lean_object*)&l_main___closed__209_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_1),((lean_object*)&l_main___closed__223_value),LEAN_SCALAR_PTR_LITERAL(5, 191, 87, 227, 85, 209, 236, 108)}};
static const lean_object* l_main___closed__224 = (const lean_object*)&l_main___closed__224_value;
static const lean_array_object l_main___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__220_value),((lean_object*)&l_main___closed__221_value),((lean_object*)&l_main___closed__222_value),((lean_object*)&l_main___closed__224_value)}};
static const lean_object* l_main___closed__225 = (const lean_object*)&l_main___closed__225_value;
static const lean_string_object l_main___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_CallerDomains"};
static const lean_object* l_main___closed__226 = (const lean_object*)&l_main___closed__226_value;
static const lean_string_object l_main___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fields"};
static const lean_object* l_main___closed__227 = (const lean_object*)&l_main___closed__227_value;
static const lean_ctor_object l_main___closed__228_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__228_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(106, 66, 153, 72, 176, 209, 0, 124)}};
static const lean_object* l_main___closed__228 = (const lean_object*)&l_main___closed__228_value;
static const lean_string_object l_main___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dots"};
static const lean_object* l_main___closed__229 = (const lean_object*)&l_main___closed__229_value;
static const lean_ctor_object l_main___closed__230_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__230_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__230_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__230_value_aux_1),((lean_object*)&l_main___closed__229_value),LEAN_SCALAR_PTR_LITERAL(205, 219, 48, 229, 27, 236, 61, 253)}};
static const lean_object* l_main___closed__230 = (const lean_object*)&l_main___closed__230_value;
static const lean_string_object l_main___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "folds"};
static const lean_object* l_main___closed__231 = (const lean_object*)&l_main___closed__231_value;
static const lean_ctor_object l_main___closed__232_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__232_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__232_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__232_value_aux_1),((lean_object*)&l_main___closed__231_value),LEAN_SCALAR_PTR_LITERAL(121, 169, 113, 215, 237, 144, 115, 89)}};
static const lean_object* l_main___closed__232 = (const lean_object*)&l_main___closed__232_value;
static const lean_string_object l_main___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finite"};
static const lean_object* l_main___closed__233 = (const lean_object*)&l_main___closed__233_value;
static const lean_ctor_object l_main___closed__234_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__234_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__234_value_aux_0),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__234_value_aux_1),((lean_object*)&l_main___closed__233_value),LEAN_SCALAR_PTR_LITERAL(80, 60, 137, 67, 228, 235, 218, 32)}};
static const lean_object* l_main___closed__234 = (const lean_object*)&l_main___closed__234_value;
static const lean_array_object l_main___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__228_value),((lean_object*)&l_main___closed__230_value),((lean_object*)&l_main___closed__232_value),((lean_object*)&l_main___closed__234_value)}};
static const lean_object* l_main___closed__235 = (const lean_object*)&l_main___closed__235_value;
static const lean_string_object l_main___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFS_QueryInvariant"};
static const lean_object* l_main___closed__236 = (const lean_object*)&l_main___closed__236_value;
static const lean_string_object l_main___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_main___closed__237 = (const lean_object*)&l_main___closed__237_value;
static const lean_ctor_object l_main___closed__238_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__238_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__238_value_aux_0),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__238_value_aux_1),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(96, 172, 209, 234, 213, 248, 166, 12)}};
static const lean_object* l_main___closed__238 = (const lean_object*)&l_main___closed__238_value;
static const lean_string_object l_main___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "no_seed"};
static const lean_object* l_main___closed__239 = (const lean_object*)&l_main___closed__239_value;
static const lean_ctor_object l_main___closed__240_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__240_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__240_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__240_value_aux_1),((lean_object*)&l_main___closed__239_value),LEAN_SCALAR_PTR_LITERAL(224, 255, 155, 13, 54, 4, 141, 127)}};
static const lean_object* l_main___closed__240 = (const lean_object*)&l_main___closed__240_value;
static const lean_string_object l_main___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "loop_property"};
static const lean_object* l_main___closed__241 = (const lean_object*)&l_main___closed__241_value;
static const lean_ctor_object l_main___closed__242_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__242_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__242_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__242_value_aux_1),((lean_object*)&l_main___closed__241_value),LEAN_SCALAR_PTR_LITERAL(88, 57, 108, 119, 140, 136, 28, 30)}};
static const lean_object* l_main___closed__242 = (const lean_object*)&l_main___closed__242_value;
static const lean_string_object l_main___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "array_property"};
static const lean_object* l_main___closed__243 = (const lean_object*)&l_main___closed__243_value;
static const lean_ctor_object l_main___closed__244_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__244_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_0),((lean_object*)&l_main___closed__226_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_1),((lean_object*)&l_main___closed__243_value),LEAN_SCALAR_PTR_LITERAL(101, 136, 184, 95, 1, 228, 235, 150)}};
static const lean_object* l_main___closed__244 = (const lean_object*)&l_main___closed__244_value;
static const lean_array_object l_main___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__238_value),((lean_object*)&l_main___closed__240_value),((lean_object*)&l_main___closed__242_value),((lean_object*)&l_main___closed__244_value)}};
static const lean_object* l_main___closed__245 = (const lean_object*)&l_main___closed__245_value;
static const lean_string_object l_main___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_ReadCanonical"};
static const lean_object* l_main___closed__246 = (const lean_object*)&l_main___closed__246_value;
static const lean_string_object l_main___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "field"};
static const lean_object* l_main___closed__247 = (const lean_object*)&l_main___closed__247_value;
static const lean_ctor_object l_main___closed__248_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__248_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__248_value_aux_0),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__248_value_aux_1),((lean_object*)&l_main___closed__247_value),LEAN_SCALAR_PTR_LITERAL(152, 63, 110, 14, 253, 180, 222, 122)}};
static const lean_object* l_main___closed__248 = (const lean_object*)&l_main___closed__248_value;
static const lean_string_object l_main___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "read_canonical"};
static const lean_object* l_main___closed__249 = (const lean_object*)&l_main___closed__249_value;
static const lean_ctor_object l_main___closed__250_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__250_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__250_value_aux_0),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__250_value_aux_1),((lean_object*)&l_main___closed__249_value),LEAN_SCALAR_PTR_LITERAL(141, 227, 30, 159, 85, 203, 221, 33)}};
static const lean_object* l_main___closed__250 = (const lean_object*)&l_main___closed__250_value;
static const lean_string_object l_main___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "form"};
static const lean_object* l_main___closed__251 = (const lean_object*)&l_main___closed__251_value;
static const lean_ctor_object l_main___closed__252_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__252_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__252_value_aux_0),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__252_value_aux_1),((lean_object*)&l_main___closed__251_value),LEAN_SCALAR_PTR_LITERAL(211, 122, 96, 177, 138, 34, 8, 171)}};
static const lean_object* l_main___closed__252 = (const lean_object*)&l_main___closed__252_value;
static const lean_string_object l_main___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* l_main___closed__253 = (const lean_object*)&l_main___closed__253_value;
static const lean_ctor_object l_main___closed__254_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__254_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__254_value_aux_0),((lean_object*)&l_main___closed__236_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__254_value_aux_1),((lean_object*)&l_main___closed__253_value),LEAN_SCALAR_PTR_LITERAL(230, 205, 73, 150, 123, 187, 99, 151)}};
static const lean_object* l_main___closed__254 = (const lean_object*)&l_main___closed__254_value;
static const lean_array_object l_main___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__248_value),((lean_object*)&l_main___closed__250_value),((lean_object*)&l_main___closed__252_value),((lean_object*)&l_main___closed__254_value)}};
static const lean_object* l_main___closed__255 = (const lean_object*)&l_main___closed__255_value;
static const lean_string_object l_main___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFS_QueryValuesPacket"};
static const lean_object* l_main___closed__256 = (const lean_object*)&l_main___closed__256_value;
static const lean_ctor_object l_main___closed__257_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__257_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__257_value_aux_0),((lean_object*)&l_main___closed__256_value),LEAN_SCALAR_PTR_LITERAL(247, 250, 32, 148, 237, 159, 228, 95)}};
static const lean_ctor_object l_main___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__257_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(25, 8, 178, 77, 87, 107, 39, 49)}};
static const lean_object* l_main___closed__257 = (const lean_object*)&l_main___closed__257_value;
static const lean_string_object l_main___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_main___closed__258 = (const lean_object*)&l_main___closed__258_value;
static const lean_ctor_object l_main___closed__259_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__259_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_0),((lean_object*)&l_main___closed__256_value),LEAN_SCALAR_PTR_LITERAL(247, 250, 32, 148, 237, 159, 228, 95)}};
static const lean_ctor_object l_main___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_1),((lean_object*)&l_main___closed__258_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 135, 160, 98, 177, 143, 131)}};
static const lean_object* l_main___closed__259 = (const lean_object*)&l_main___closed__259_value;
static const lean_string_object l_main___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "limbs"};
static const lean_object* l_main___closed__260 = (const lean_object*)&l_main___closed__260_value;
static const lean_ctor_object l_main___closed__261_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__261_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__261_value_aux_0),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__261_value_aux_1),((lean_object*)&l_main___closed__260_value),LEAN_SCALAR_PTR_LITERAL(38, 146, 191, 16, 0, 63, 126, 115)}};
static const lean_object* l_main___closed__261 = (const lean_object*)&l_main___closed__261_value;
static const lean_string_object l_main___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bytes"};
static const lean_object* l_main___closed__262 = (const lean_object*)&l_main___closed__262_value;
static const lean_ctor_object l_main___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_0),((lean_object*)&l_main___closed__246_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_1),((lean_object*)&l_main___closed__262_value),LEAN_SCALAR_PTR_LITERAL(89, 95, 44, 163, 159, 126, 215, 101)}};
static const lean_object* l_main___closed__263 = (const lean_object*)&l_main___closed__263_value;
static const lean_array_object l_main___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__257_value),((lean_object*)&l_main___closed__259_value),((lean_object*)&l_main___closed__261_value),((lean_object*)&l_main___closed__263_value)}};
static const lean_object* l_main___closed__264 = (const lean_object*)&l_main___closed__264_value;
static const lean_string_object l_main___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_TraceBack"};
static const lean_object* l_main___closed__265 = (const lean_object*)&l_main___closed__265_value;
static const lean_string_object l_main___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "model_congr"};
static const lean_object* l_main___closed__266 = (const lean_object*)&l_main___closed__266_value;
static const lean_ctor_object l_main___closed__267_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__267_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__267_value_aux_0),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__267_value_aux_1),((lean_object*)&l_main___closed__266_value),LEAN_SCALAR_PTR_LITERAL(203, 249, 62, 153, 186, 69, 85, 220)}};
static const lean_object* l_main___closed__267 = (const lean_object*)&l_main___closed__267_value;
static const lean_ctor_object l_main___closed__268_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__268_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__268_value_aux_0),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__268_value_aux_1),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(29, 105, 172, 160, 20, 107, 110, 96)}};
static const lean_object* l_main___closed__268 = (const lean_object*)&l_main___closed__268_value;
static const lean_string_object l_main___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "installed"};
static const lean_object* l_main___closed__269 = (const lean_object*)&l_main___closed__269_value;
static const lean_ctor_object l_main___closed__270_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__270_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__270_value_aux_0),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__270_value_aux_1),((lean_object*)&l_main___closed__269_value),LEAN_SCALAR_PTR_LITERAL(106, 200, 194, 224, 10, 226, 64, 45)}};
static const lean_object* l_main___closed__270 = (const lean_object*)&l_main___closed__270_value;
static const lean_string_object l_main___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFS_DotTrace"};
static const lean_object* l_main___closed__271 = (const lean_object*)&l_main___closed__271_value;
static const lean_ctor_object l_main___closed__272_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__272_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__272_value_aux_0),((lean_object*)&l_main___closed__271_value),LEAN_SCALAR_PTR_LITERAL(17, 29, 204, 0, 187, 63, 52, 210)}};
static const lean_ctor_object l_main___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__272_value_aux_1),((lean_object*)&l_main___closed__172_value),LEAN_SCALAR_PTR_LITERAL(117, 223, 73, 201, 180, 97, 17, 191)}};
static const lean_object* l_main___closed__272 = (const lean_object*)&l_main___closed__272_value;
static const lean_array_object l_main___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__267_value),((lean_object*)&l_main___closed__268_value),((lean_object*)&l_main___closed__270_value),((lean_object*)&l_main___closed__272_value)}};
static const lean_object* l_main___closed__273 = (const lean_object*)&l_main___closed__273_value;
static const lean_string_object l_main___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFS_FoldInstall"};
static const lean_object* l_main___closed__274 = (const lean_object*)&l_main___closed__274_value;
static const lean_string_object l_main___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_main___closed__275 = (const lean_object*)&l_main___closed__275_value;
static const lean_ctor_object l_main___closed__276_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__276_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__276_value_aux_0),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__276_value_aux_1),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(136, 240, 145, 127, 138, 114, 215, 62)}};
static const lean_object* l_main___closed__276 = (const lean_object*)&l_main___closed__276_value;
static const lean_string_object l_main___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "circle"};
static const lean_object* l_main___closed__277 = (const lean_object*)&l_main___closed__277_value;
static const lean_ctor_object l_main___closed__278_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__278_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_0),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(97, 30, 198, 122, 173, 41, 15, 28)}};
static const lean_object* l_main___closed__278 = (const lean_object*)&l_main___closed__278_value;
static const lean_string_object l_main___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "domains"};
static const lean_object* l_main___closed__279 = (const lean_object*)&l_main___closed__279_value;
static const lean_ctor_object l_main___closed__280_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__280_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__280_value_aux_0),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__280_value_aux_1),((lean_object*)&l_main___closed__279_value),LEAN_SCALAR_PTR_LITERAL(184, 79, 219, 149, 95, 90, 67, 223)}};
static const lean_object* l_main___closed__280 = (const lean_object*)&l_main___closed__280_value;
static const lean_string_object l_main___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eval_bind"};
static const lean_object* l_main___closed__281 = (const lean_object*)&l_main___closed__281_value;
static const lean_ctor_object l_main___closed__282_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__282_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__282_value_aux_0),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__282_value_aux_1),((lean_object*)&l_main___closed__281_value),LEAN_SCALAR_PTR_LITERAL(122, 228, 175, 221, 213, 9, 16, 133)}};
static const lean_object* l_main___closed__282 = (const lean_object*)&l_main___closed__282_value;
static const lean_array_object l_main___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__276_value),((lean_object*)&l_main___closed__278_value),((lean_object*)&l_main___closed__280_value),((lean_object*)&l_main___closed__282_value)}};
static const lean_object* l_main___closed__283 = (const lean_object*)&l_main___closed__283_value;
static const lean_string_object l_main___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFS_QueryOps"};
static const lean_object* l_main___closed__284 = (const lean_object*)&l_main___closed__284_value;
static const lean_string_object l_main___closed__285_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "accumulation"};
static const lean_object* l_main___closed__285 = (const lean_object*)&l_main___closed__285_value;
static const lean_ctor_object l_main___closed__286_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__286_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__286_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(102, 198, 20, 13, 250, 208, 119, 140)}};
static const lean_ctor_object l_main___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__286_value_aux_1),((lean_object*)&l_main___closed__285_value),LEAN_SCALAR_PTR_LITERAL(60, 122, 195, 2, 176, 249, 55, 90)}};
static const lean_object* l_main___closed__286 = (const lean_object*)&l_main___closed__286_value;
static const lean_string_object l_main___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_QueryBack"};
static const lean_object* l_main___closed__287 = (const lean_object*)&l_main___closed__287_value;
static const lean_ctor_object l_main___closed__288_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__288_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__288_value_aux_0),((lean_object*)&l_main___closed__287_value),LEAN_SCALAR_PTR_LITERAL(186, 135, 93, 118, 73, 139, 105, 68)}};
static const lean_ctor_object l_main___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__288_value_aux_1),((lean_object*)&l_main___closed__269_value),LEAN_SCALAR_PTR_LITERAL(15, 51, 151, 113, 201, 174, 217, 81)}};
static const lean_object* l_main___closed__288 = (const lean_object*)&l_main___closed__288_value;
static const lean_string_object l_main___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "rows"};
static const lean_object* l_main___closed__289 = (const lean_object*)&l_main___closed__289_value;
static const lean_ctor_object l_main___closed__290_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__290_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__290_value_aux_0),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__290_value_aux_1),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(131, 37, 110, 78, 11, 107, 144, 121)}};
static const lean_object* l_main___closed__290 = (const lean_object*)&l_main___closed__290_value;
static const lean_string_object l_main___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "map_map"};
static const lean_object* l_main___closed__291 = (const lean_object*)&l_main___closed__291_value;
static const lean_ctor_object l_main___closed__292_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__292_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_0),((lean_object*)&l_main___closed__274_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__292_value_aux_1),((lean_object*)&l_main___closed__291_value),LEAN_SCALAR_PTR_LITERAL(106, 82, 149, 195, 128, 208, 229, 242)}};
static const lean_object* l_main___closed__292 = (const lean_object*)&l_main___closed__292_value;
static const lean_array_object l_main___closed__293_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__286_value),((lean_object*)&l_main___closed__288_value),((lean_object*)&l_main___closed__290_value),((lean_object*)&l_main___closed__292_value)}};
static const lean_object* l_main___closed__293 = (const lean_object*)&l_main___closed__293_value;
static const lean_string_object l_main___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFS_AccumDomain"};
static const lean_object* l_main___closed__294 = (const lean_object*)&l_main___closed__294_value;
static const lean_ctor_object l_main___closed__295_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__295_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__295_value_aux_0),((lean_object*)&l_main___closed__294_value),LEAN_SCALAR_PTR_LITERAL(43, 36, 186, 92, 53, 224, 23, 154)}};
static const lean_ctor_object l_main___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__295_value_aux_1),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(93, 187, 209, 163, 181, 20, 108, 91)}};
static const lean_object* l_main___closed__295 = (const lean_object*)&l_main___closed__295_value;
static const lean_string_object l_main___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "domain"};
static const lean_object* l_main___closed__296 = (const lean_object*)&l_main___closed__296_value;
static const lean_ctor_object l_main___closed__297_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__297_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__297_value_aux_0),((lean_object*)&l_main___closed__294_value),LEAN_SCALAR_PTR_LITERAL(43, 36, 186, 92, 53, 224, 23, 154)}};
static const lean_ctor_object l_main___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__297_value_aux_1),((lean_object*)&l_main___closed__296_value),LEAN_SCALAR_PTR_LITERAL(26, 11, 133, 116, 22, 88, 154, 255)}};
static const lean_object* l_main___closed__297 = (const lean_object*)&l_main___closed__297_value;
static const lean_string_object l_main___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFS_AccumInstall"};
static const lean_object* l_main___closed__298 = (const lean_object*)&l_main___closed__298_value;
static const lean_ctor_object l_main___closed__299_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__299_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__299_value_aux_0),((lean_object*)&l_main___closed__298_value),LEAN_SCALAR_PTR_LITERAL(198, 195, 235, 195, 29, 24, 238, 158)}};
static const lean_ctor_object l_main___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__299_value_aux_1),((lean_object*)&l_main___closed__269_value),LEAN_SCALAR_PTR_LITERAL(155, 184, 204, 22, 19, 124, 109, 247)}};
static const lean_object* l_main___closed__299 = (const lean_object*)&l_main___closed__299_value;
static const lean_ctor_object l_main___closed__300_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__300_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__300_value_aux_0),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(102, 198, 20, 13, 250, 208, 119, 140)}};
static const lean_ctor_object l_main___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__300_value_aux_1),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(180, 90, 234, 96, 10, 196, 189, 233)}};
static const lean_object* l_main___closed__300 = (const lean_object*)&l_main___closed__300_value;
static const lean_array_object l_main___closed__301_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__295_value),((lean_object*)&l_main___closed__297_value),((lean_object*)&l_main___closed__299_value),((lean_object*)&l_main___closed__300_value)}};
static const lean_object* l_main___closed__301 = (const lean_object*)&l_main___closed__301_value;
static const lean_string_object l_main___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFG_QueryLoopSource"};
static const lean_object* l_main___closed__302 = (const lean_object*)&l_main___closed__302_value;
static const lean_string_object l_main___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l_main___closed__303 = (const lean_object*)&l_main___closed__303_value;
static const lean_ctor_object l_main___closed__304_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__304_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__304_value_aux_0),((lean_object*)&l_main___closed__302_value),LEAN_SCALAR_PTR_LITERAL(88, 59, 114, 222, 81, 236, 187, 161)}};
static const lean_ctor_object l_main___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__304_value_aux_1),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(35, 213, 149, 102, 87, 98, 239, 70)}};
static const lean_object* l_main___closed__304 = (const lean_object*)&l_main___closed__304_value;
static const lean_string_object l_main___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "NFN_NFB_GeometryComposed"};
static const lean_object* l_main___closed__305 = (const lean_object*)&l_main___closed__305_value;
static const lean_string_object l_main___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "result_state_effects"};
static const lean_object* l_main___closed__306 = (const lean_object*)&l_main___closed__306_value;
static const lean_ctor_object l_main___closed__307_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__305_value),LEAN_SCALAR_PTR_LITERAL(79, 80, 161, 152, 193, 207, 152, 79)}};
static const lean_ctor_object l_main___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_0),((lean_object*)&l_main___closed__306_value),LEAN_SCALAR_PTR_LITERAL(109, 4, 254, 8, 96, 138, 107, 119)}};
static const lean_object* l_main___closed__307 = (const lean_object*)&l_main___closed__307_value;
static const lean_string_object l_main___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_QueryTrace"};
static const lean_object* l_main___closed__308 = (const lean_object*)&l_main___closed__308_value;
static const lean_ctor_object l_main___closed__309_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__309_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__309_value_aux_0),((lean_object*)&l_main___closed__308_value),LEAN_SCALAR_PTR_LITERAL(108, 15, 4, 107, 176, 191, 20, 201)}};
static const lean_ctor_object l_main___closed__309_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__309_value_aux_1),((lean_object*)&l_main___closed__81_value),LEAN_SCALAR_PTR_LITERAL(222, 123, 151, 176, 80, 200, 161, 235)}};
static const lean_object* l_main___closed__309 = (const lean_object*)&l_main___closed__309_value;
static const lean_ctor_object l_main___closed__310_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__310_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__310_value_aux_0),((lean_object*)&l_main___closed__144_value),LEAN_SCALAR_PTR_LITERAL(39, 227, 16, 37, 232, 157, 112, 26)}};
static const lean_ctor_object l_main___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__310_value_aux_1),((lean_object*)&l_main___closed__303_value),LEAN_SCALAR_PTR_LITERAL(200, 42, 120, 75, 52, 0, 78, 174)}};
static const lean_object* l_main___closed__310 = (const lean_object*)&l_main___closed__310_value;
static const lean_array_object l_main___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__304_value),((lean_object*)&l_main___closed__307_value),((lean_object*)&l_main___closed__309_value),((lean_object*)&l_main___closed__310_value)}};
static const lean_object* l_main___closed__311 = (const lean_object*)&l_main___closed__311_value;
static const lean_string_object l_main___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "NFS_NEV_AccumulateComplete"};
static const lean_object* l_main___closed__312 = (const lean_object*)&l_main___closed__312_value;
static const lean_string_object l_main___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "native"};
static const lean_object* l_main___closed__313 = (const lean_object*)&l_main___closed__313_value;
static const lean_ctor_object l_main___closed__314_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__312_value),LEAN_SCALAR_PTR_LITERAL(33, 61, 229, 173, 207, 253, 39, 17)}};
static const lean_ctor_object l_main___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__314_value_aux_0),((lean_object*)&l_main___closed__313_value),LEAN_SCALAR_PTR_LITERAL(178, 236, 206, 186, 163, 193, 147, 152)}};
static const lean_object* l_main___closed__314 = (const lean_object*)&l_main___closed__314_value;
static const lean_string_object l_main___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RPx_Deployed"};
static const lean_object* l_main___closed__315 = (const lean_object*)&l_main___closed__315_value;
static const lean_string_object l_main___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deployed"};
static const lean_object* l_main___closed__316 = (const lean_object*)&l_main___closed__316_value;
static const lean_ctor_object l_main___closed__317_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__317_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__317_value_aux_0),((lean_object*)&l_main___closed__315_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 132, 221, 229, 11, 19, 160)}};
static const lean_ctor_object l_main___closed__317_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__317_value_aux_1),((lean_object*)&l_main___closed__316_value),LEAN_SCALAR_PTR_LITERAL(170, 12, 223, 81, 221, 8, 194, 27)}};
static const lean_object* l_main___closed__317 = (const lean_object*)&l_main___closed__317_value;
static const lean_string_object l_main___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFM_ProductInstance"};
static const lean_object* l_main___closed__318 = (const lean_object*)&l_main___closed__318_value;
static const lean_ctor_object l_main___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__319_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_0),((lean_object*)&l_main___closed__318_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_1),((lean_object*)&l_main___closed__269_value),LEAN_SCALAR_PTR_LITERAL(49, 64, 12, 130, 97, 100, 181, 138)}};
static const lean_object* l_main___closed__319 = (const lean_object*)&l_main___closed__319_value;
static const lean_string_object l_main___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wrapper"};
static const lean_object* l_main___closed__320 = (const lean_object*)&l_main___closed__320_value;
static const lean_ctor_object l_main___closed__321_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__70_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__321_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_0),((lean_object*)&l_main___closed__318_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_1),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(173, 78, 168, 213, 70, 99, 52, 197)}};
static const lean_object* l_main___closed__321 = (const lean_object*)&l_main___closed__321_value;
static const lean_array_object l_main___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__314_value),((lean_object*)&l_main___closed__317_value),((lean_object*)&l_main___closed__319_value),((lean_object*)&l_main___closed__321_value)}};
static const lean_object* l_main___closed__322 = (const lean_object*)&l_main___closed__322_value;
static const lean_string_object l_main___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFS_NEV_AccumPacket"};
static const lean_object* l_main___closed__323 = (const lean_object*)&l_main___closed__323_value;
static const lean_string_object l_main___closed__324_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "raw_length"};
static const lean_object* l_main___closed__324 = (const lean_object*)&l_main___closed__324_value;
static const lean_ctor_object l_main___closed__325_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__323_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__325_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__325_value_aux_0),((lean_object*)&l_main___closed__324_value),LEAN_SCALAR_PTR_LITERAL(47, 26, 123, 75, 83, 151, 136, 28)}};
static const lean_object* l_main___closed__325 = (const lean_object*)&l_main___closed__325_value;
static const lean_ctor_object l_main___closed__326_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__323_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__326_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__326_value_aux_0),((lean_object*)&l_main___closed__306_value),LEAN_SCALAR_PTR_LITERAL(225, 84, 179, 156, 73, 95, 72, 85)}};
static const lean_object* l_main___closed__326 = (const lean_object*)&l_main___closed__326_value;
static const lean_string_object l_main___closed__327_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "no_base_dependency"};
static const lean_object* l_main___closed__327 = (const lean_object*)&l_main___closed__327_value;
static const lean_ctor_object l_main___closed__328_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__323_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__328_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__328_value_aux_0),((lean_object*)&l_main___closed__327_value),LEAN_SCALAR_PTR_LITERAL(170, 191, 181, 162, 0, 4, 56, 69)}};
static const lean_object* l_main___closed__328 = (const lean_object*)&l_main___closed__328_value;
static const lean_string_object l_main___closed__329_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reference"};
static const lean_object* l_main___closed__329 = (const lean_object*)&l_main___closed__329_value;
static const lean_ctor_object l_main___closed__330_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__312_value),LEAN_SCALAR_PTR_LITERAL(33, 61, 229, 173, 207, 253, 39, 17)}};
static const lean_ctor_object l_main___closed__330_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__330_value_aux_0),((lean_object*)&l_main___closed__329_value),LEAN_SCALAR_PTR_LITERAL(33, 110, 209, 209, 192, 49, 240, 77)}};
static const lean_object* l_main___closed__330 = (const lean_object*)&l_main___closed__330_value;
static const lean_array_object l_main___closed__331_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__325_value),((lean_object*)&l_main___closed__326_value),((lean_object*)&l_main___closed__328_value),((lean_object*)&l_main___closed__330_value)}};
static const lean_object* l_main___closed__331 = (const lean_object*)&l_main___closed__331_value;
static const lean_string_object l_main___closed__332_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__332 = (const lean_object*)&l_main___closed__332_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
return v_bs_441_;
}
else
{
lean_object* v_v_443_; lean_object* v___x_444_; lean_object* v_bs_x27_445_; uint8_t v___x_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_443_ = lean_array_uget(v_bs_441_, v_i_440_);
v___x_444_ = lean_unsigned_to_nat(0u);
v_bs_x27_445_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_444_);
v___x_446_ = 0;
v___x_447_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_447_, 0, v_v_443_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1, v___x_442_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1 + 1, v___x_442_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1 + 2, v___x_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_440_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_445_, v_i_440_, v___x_447_);
v_i_440_ = v___x_449_;
v_bs_441_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_b_461_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_a_465_ = lean_array_uget_borrowed(v_as_458_, v_i_460_);
lean_inc(v_a_465_);
v___x_466_ = l_Lean_Json_parse(v_a_465_);
v___x_467_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_n(v_a_468_, 2);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__2));
v___x_470_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(v_a_468_, v___x_469_);
v___x_471_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___closed__3));
v___x_474_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(v_a_468_, v___x_473_);
v___x_475_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; size_t v___x_478_; size_t v___x_479_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_b_461_, v_a_472_, v_a_476_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_460_, v___x_478_);
v_i_460_ = v___x_479_;
v_b_461_ = v___x_477_;
goto _start;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_a_472_);
lean_dec_ref(v_b_461_);
v_a_481_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_475_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_475_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_a_468_);
lean_dec_ref(v_b_461_);
v_a_489_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_471_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_471_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_b_461_);
v_a_497_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_467_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_467_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_as_505_, lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_){
_start:
{
size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_sz_boxed_510_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_511_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_as_505_, v_sz_boxed_510_, v_i_boxed_511_, v_b_508_);
lean_dec_ref(v_as_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_513_, lean_object* v_b_514_){
_start:
{
if (lean_obj_tag(v_as_x27_513_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_514_);
return v___x_516_;
}
else
{
lean_object* v_head_517_; lean_object* v_tail_518_; lean_object* v_data_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_head_517_ = lean_ctor_get(v_as_x27_513_, 0);
v_tail_518_ = lean_ctor_get(v_as_x27_513_, 1);
v_data_519_ = lean_ctor_get(v_head_517_, 4);
lean_inc(v_data_519_);
v___x_520_ = l_Lean_MessageData_toString(v_data_519_);
v___x_521_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
lean_dec_ref_known(v___x_521_, 1);
v___x_522_ = lean_box(0);
v_as_x27_513_ = v_tail_518_;
v_b_514_ = v___x_522_;
goto _start;
}
else
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_524_, lean_object* v_b_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_524_, v_b_525_);
lean_dec(v_as_x27_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object* v___y_542_, lean_object* v_as_543_, size_t v_sz_544_, size_t v_i_545_, uint8_t v_b_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_snd_551_; uint8_t v___x_556_; lean_object* v_a_558_; 
v___x_556_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_556_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(v_b_546_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Elab_Command_getRef___redArg(v___y_547_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_547_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_quotContext_x3f_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v_a_580_; lean_object* v___x_581_; 
lean_dec_ref_known(v___x_576_, 1);
v_quotContext_x3f_577_ = lean_ctor_get(v___y_547_, 5);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_579_ = lean_string_dec_eq(v___y_542_, v___x_578_);
v_a_580_ = lean_array_uget_borrowed(v_as_543_, v_i_545_);
v___x_581_ = l_Lean_SourceInfo_fromRef(v_a_575_, v___x_579_);
lean_dec(v_a_575_);
if (lean_obj_tag(v_quotContext_x3f_577_) == 0)
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_548_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_dec_ref_known(v___x_601_, 1);
goto v___jp_582_;
}
else
{
lean_object* v_a_602_; 
lean_dec(v___x_581_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_a_558_ = v_a_602_;
goto v___jp_557_;
}
}
else
{
goto v___jp_582_;
}
v___jp_582_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5));
v___x_584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6));
lean_inc_n(v___x_581_, 2);
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7));
v___x_587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_581_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_inc(v_a_580_);
v___x_588_ = lean_mk_syntax_ident(v_a_580_);
v___x_589_ = l_Lean_Syntax_node3(v___x_581_, v___x_583_, v___x_585_, v___x_587_, v___x_588_);
v___x_590_ = l_Lean_Elab_Command_elabCommand(v___x_589_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref_known(v___x_590_, 1);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8));
v___x_592_ = lean_string_append(v___x_591_, v___y_542_);
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9));
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
lean_inc_n(v_a_580_, 2);
v___x_595_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_580_, v___x_556_);
v___x_596_ = lean_string_append(v___x_594_, v___x_595_);
lean_dec_ref(v___x_595_);
v___x_597_ = l_NEP_audit(v_a_580_, v___x_596_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; 
lean_dec_ref_known(v___x_597_, 1);
v___x_598_ = lean_box(v_b_546_);
v_snd_551_ = v___x_598_;
goto v___jp_550_;
}
else
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_597_, 1);
v_a_558_ = v_a_599_;
goto v___jp_557_;
}
}
else
{
lean_object* v_a_600_; 
v_a_600_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_590_, 1);
v_a_558_ = v_a_600_;
goto v___jp_557_;
}
}
}
else
{
lean_object* v_a_603_; 
lean_dec(v_a_575_);
v_a_603_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_576_, 1);
v_a_558_ = v_a_603_;
goto v___jp_557_;
}
}
else
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_574_, 1);
v_a_558_ = v_a_604_;
goto v___jp_557_;
}
}
v___jp_550_:
{
size_t v___x_552_; size_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_add(v_i_545_, v___x_552_);
v___x_554_ = lean_unbox(v_snd_551_);
lean_dec(v_snd_551_);
v_i_545_ = v___x_553_;
v_b_546_ = v___x_554_;
goto _start;
}
v___jp_557_:
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_Exception_isInterrupt(v_a_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_Exception_toMessageData(v_a_558_);
v___x_561_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_560_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_562_ = lean_box(v___x_556_);
v_snd_551_ = v___x_562_;
goto v___jp_550_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_561_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v_a_558_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object* v___y_605_, lean_object* v_as_606_, lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; uint8_t v_b_boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_614_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_b_boxed_615_ = lean_unbox(v_b_609_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_605_, v_as_606_, v_sz_boxed_613_, v_i_boxed_614_, v_b_boxed_615_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec_ref(v_as_606_);
lean_dec_ref(v___y_605_);
return v_res_616_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_box(0);
v___x_622_ = lean_unsigned_to_nat(16u);
v___x_623_ = lean_mk_array(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l_main___closed__12(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_main___closed__11));
v___x_633_ = l_Lean_FileMap_ofString(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_634_ = 0;
v___x_635_ = lean_box(0);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_box(0);
v___x_638_ = lean_box(0);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_obj_once(&l_main___closed__12, &l_main___closed__12_once, _init_l_main___closed__12);
v___x_641_ = ((lean_object*)(l_main___closed__10));
v___x_642_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
lean_ctor_set(v___x_642_, 2, v___x_639_);
lean_ctor_set(v___x_642_, 3, v___x_639_);
lean_ctor_set(v___x_642_, 4, v___x_638_);
lean_ctor_set(v___x_642_, 5, v___x_637_);
lean_ctor_set(v___x_642_, 6, v___x_636_);
lean_ctor_set(v___x_642_, 7, v___x_635_);
lean_ctor_set(v___x_642_, 8, v___x_637_);
lean_ctor_set(v___x_642_, 9, v___x_637_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*10, v___x_634_);
return v___x_642_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_unsigned_to_nat(32u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
size_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = ((size_t)5ULL);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_unsigned_to_nat(32u);
v___x_649_ = lean_mk_empty_array_with_capacity(v___x_648_);
v___x_650_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
v___x_651_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_647_);
lean_ctor_set(v___x_651_, 3, v___x_647_);
lean_ctor_set_usize(v___x_651_, 4, v___x_646_);
return v___x_651_;
}
}
static lean_object* _init_l_main___closed__16(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box(1);
v___x_653_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
v___x_654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
lean_ctor_set(v___x_654_, 2, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = 1;
v___x_1572_ = lean_box_uint32(v___x_1571_);
return v___x_1572_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = 0;
v___x_1574_ = lean_box_uint32(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = 2;
v___x_1576_ = lean_box_uint32(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1577_){
_start:
{
uint32_t v___y_1580_; uint8_t v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1606_; uint32_t v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1626_; lean_object* v___y_1627_; size_t v___y_1628_; uint32_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; size_t v___y_1657_; lean_object* v___y_1658_; uint32_t v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = l_NFA__MemoryLimit_set();
v___x_1669_ = ((lean_object*)(l_main___closed__7));
v___x_1670_ = l_Lean_findSysroot(v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_initSearchPath(v_a_1671_, v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1673_, 1);
v___x_1674_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v___y_1676_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___y_1760_; 
lean_dec_ref_known(v___x_1674_, 1);
if (lean_obj_tag(v_args_1577_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = ((lean_object*)(l_main___closed__332));
v___y_1760_ = v___x_1874_;
goto v___jp_1759_;
}
else
{
lean_object* v_head_1875_; 
v_head_1875_ = lean_ctor_get(v_args_1577_, 0);
lean_inc(v_head_1875_);
lean_dec_ref_known(v_args_1577_, 2);
v___y_1760_ = v_head_1875_;
goto v___jp_1759_;
}
v___jp_1675_:
{
size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint32_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; uint8_t v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_sz_1679_ = lean_array_size(v_fst_1677_);
v___x_1680_ = ((size_t)0ULL);
lean_inc_ref(v_fst_1677_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_1679_, v___x_1680_, v_fst_1677_);
v___x_1682_ = l_Lean_Options_empty;
v___x_1683_ = 0;
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = ((lean_object*)(l_main___closed__8));
v___x_1686_ = 0;
v___x_1687_ = 1;
v___x_1688_ = 2;
v___x_1689_ = lean_box(1);
v___x_1690_ = l_Lean_importModules(v___x_1681_, v___x_1682_, v___x_1683_, v___x_1685_, v___x_1686_, v___x_1687_, v___x_1688_, v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = ((lean_object*)(l_main___closed__9));
v___x_1693_ = lean_string_dec_eq(v___y_1676_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_1695_ = lean_string_dec_eq(v___y_1676_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; size_t v_sz_1700_; lean_object* v___x_1701_; 
v___x_1696_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_1697_ = lean_obj_once(&l_main___closed__16, &l_main___closed__16_once, _init_l_main___closed__16);
v___x_1698_ = l_Lean_Elab_Command_mkState(v_a_1691_, v___x_1697_, v___x_1682_);
v___x_1699_ = lean_st_mk_ref(v___x_1698_);
v_sz_1700_ = lean_array_size(v_snd_1678_);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_1676_, v_snd_1678_, v_sz_1700_, v___x_1680_, v___x_1686_, v___x_1696_, v___x_1699_);
lean_dec_ref(v___y_1676_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v_messages_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_st_ref_get(v___x_1699_);
lean_dec(v___x_1699_);
v_messages_1704_ = lean_ctor_get(v___x_1703_, 1);
lean_inc_ref(v_messages_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = l_Lean_MessageLog_toList(v_messages_1704_);
lean_dec_ref(v_messages_1704_);
v___x_1706_ = lean_box(0);
v___x_1707_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v___x_1705_, v___x_1706_);
lean_dec(v___x_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1720_; 
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1721_);
v___x_1709_ = v___x_1707_;
v_isShared_1710_ = v_isSharedCheck_1720_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v___x_1707_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1720_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = l_main___boxed__const__2;
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_main___boxed__const__1;
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1716_);
v___x_1718_ = v___x_1709_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1702_);
v_a_1722_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1707_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1707_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v___x_1699_);
v_a_1730_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1731_ = l_Lean_Exception_toMessageData(v_a_1730_);
v___x_1732_ = l_Lean_MessageData_toString(v___x_1731_);
v___x_1733_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1732_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1742_);
v___x_1735_ = v___x_1733_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v___x_1733_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = l_main___boxed__const__3;
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_a_1743_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1733_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1733_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
else
{
v___y_1657_ = v___x_1680_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___x_1683_;
v___y_1660_ = v_a_1691_;
v___y_1661_ = v___x_1684_;
goto v___jp_1656_;
}
}
else
{
v___y_1657_ = v___x_1680_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___x_1683_;
v___y_1660_ = v_a_1691_;
v___y_1661_ = v___x_1684_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v___y_1676_);
v_a_1751_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1690_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1690_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
v___jp_1759_:
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_main___closed__17));
v___x_1762_ = lean_string_dec_eq(v___y_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_main___closed__18));
v___x_1764_ = lean_string_dec_eq(v___y_1760_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = ((lean_object*)(l_main___closed__19));
v___x_1766_ = lean_string_dec_eq(v___y_1760_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_main___closed__20));
v___x_1768_ = lean_string_dec_eq(v___y_1760_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_main___closed__21));
v___x_1770_ = lean_string_dec_eq(v___y_1760_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_main___closed__22));
v___x_1772_ = lean_string_dec_eq(v___y_1760_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = ((lean_object*)(l_main___closed__23));
v___x_1774_ = lean_string_dec_eq(v___y_1760_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_main___closed__24));
v___x_1776_ = lean_string_dec_eq(v___y_1760_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_main___closed__25));
v___x_1778_ = lean_string_dec_eq(v___y_1760_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_main___closed__26));
v___x_1780_ = lean_string_dec_eq(v___y_1760_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_main___closed__27));
v___x_1782_ = lean_string_dec_eq(v___y_1760_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_main___closed__28));
v___x_1784_ = lean_string_dec_eq(v___y_1760_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_main___closed__29));
v___x_1786_ = lean_string_dec_eq(v___y_1760_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_main___closed__30));
v___x_1788_ = lean_string_dec_eq(v___y_1760_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_main___closed__31));
v___x_1790_ = lean_string_dec_eq(v___y_1760_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_main___closed__32));
v___x_1792_ = lean_string_dec_eq(v___y_1760_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_main___closed__33));
v___x_1794_ = lean_string_dec_eq(v___y_1760_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_main___closed__34));
v___x_1796_ = lean_string_dec_eq(v___y_1760_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_main___closed__35));
v___x_1798_ = lean_string_dec_eq(v___y_1760_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_main___closed__36));
v___x_1800_ = lean_string_dec_eq(v___y_1760_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_main___closed__37));
v___x_1802_ = lean_string_dec_eq(v___y_1760_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_main___closed__38));
v___x_1804_ = lean_string_dec_eq(v___y_1760_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_main___closed__39));
v___x_1806_ = lean_string_dec_eq(v___y_1760_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_main___closed__40));
v___x_1808_ = lean_string_dec_eq(v___y_1760_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_main___closed__41));
v___x_1810_ = lean_string_dec_eq(v___y_1760_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_main___closed__42));
v___x_1812_ = lean_string_dec_eq(v___y_1760_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_main___closed__43));
v___x_1814_ = lean_string_dec_eq(v___y_1760_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_main___closed__44));
v___x_1816_ = lean_string_dec_eq(v___y_1760_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l_NER_referenceNames___closed__0));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1817_;
v_snd_1678_ = v___x_1817_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_main___closed__49));
v___x_1819_ = ((lean_object*)(l_main___closed__66));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1818_;
v_snd_1678_ = v___x_1819_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_main___closed__69));
v___x_1821_ = ((lean_object*)(l_main___closed__79));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1820_;
v_snd_1678_ = v___x_1821_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_main___closed__69));
v___x_1823_ = ((lean_object*)(l_main___closed__90));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1822_;
v_snd_1678_ = v___x_1823_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_main___closed__69));
v___x_1825_ = ((lean_object*)(l_main___closed__101));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1824_;
v_snd_1678_ = v___x_1825_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = ((lean_object*)(l_main___closed__69));
v___x_1827_ = ((lean_object*)(l_main___closed__111));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1826_;
v_snd_1678_ = v___x_1827_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l_main___closed__69));
v___x_1829_ = ((lean_object*)(l_main___closed__122));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1828_;
v_snd_1678_ = v___x_1829_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_main___closed__69));
v___x_1831_ = ((lean_object*)(l_main___closed__131));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1830_;
v_snd_1678_ = v___x_1831_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_main___closed__69));
v___x_1833_ = ((lean_object*)(l_main___closed__140));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1832_;
v_snd_1678_ = v___x_1833_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_main___closed__69));
v___x_1835_ = ((lean_object*)(l_main___closed__150));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1834_;
v_snd_1678_ = v___x_1835_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_main___closed__69));
v___x_1837_ = ((lean_object*)(l_main___closed__159));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1836_;
v_snd_1678_ = v___x_1837_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_main___closed__69));
v___x_1839_ = ((lean_object*)(l_main___closed__168));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1838_;
v_snd_1678_ = v___x_1839_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_main___closed__69));
v___x_1841_ = ((lean_object*)(l_main___closed__180));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1840_;
v_snd_1678_ = v___x_1841_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_main___closed__69));
v___x_1843_ = ((lean_object*)(l_main___closed__191));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1842_;
v_snd_1678_ = v___x_1843_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_main___closed__69));
v___x_1845_ = ((lean_object*)(l_main___closed__200));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1844_;
v_snd_1678_ = v___x_1845_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_main___closed__69));
v___x_1847_ = ((lean_object*)(l_main___closed__208));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1846_;
v_snd_1678_ = v___x_1847_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_main___closed__69));
v___x_1849_ = ((lean_object*)(l_main___closed__217));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1848_;
v_snd_1678_ = v___x_1849_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_main___closed__69));
v___x_1851_ = ((lean_object*)(l_main___closed__225));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1850_;
v_snd_1678_ = v___x_1851_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_main___closed__69));
v___x_1853_ = ((lean_object*)(l_main___closed__235));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1852_;
v_snd_1678_ = v___x_1853_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_main___closed__69));
v___x_1855_ = ((lean_object*)(l_main___closed__245));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1854_;
v_snd_1678_ = v___x_1855_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_main___closed__69));
v___x_1857_ = ((lean_object*)(l_main___closed__255));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1856_;
v_snd_1678_ = v___x_1857_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_main___closed__69));
v___x_1859_ = ((lean_object*)(l_main___closed__264));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1858_;
v_snd_1678_ = v___x_1859_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_main___closed__69));
v___x_1861_ = ((lean_object*)(l_main___closed__273));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1860_;
v_snd_1678_ = v___x_1861_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_main___closed__69));
v___x_1863_ = ((lean_object*)(l_main___closed__283));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1862_;
v_snd_1678_ = v___x_1863_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_main___closed__69));
v___x_1865_ = ((lean_object*)(l_main___closed__293));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1864_;
v_snd_1678_ = v___x_1865_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_main___closed__69));
v___x_1867_ = ((lean_object*)(l_main___closed__301));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1866_;
v_snd_1678_ = v___x_1867_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l_main___closed__69));
v___x_1869_ = ((lean_object*)(l_main___closed__311));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1868_;
v_snd_1678_ = v___x_1869_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_main___closed__69));
v___x_1871_ = ((lean_object*)(l_main___closed__322));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1870_;
v_snd_1678_ = v___x_1871_;
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_main___closed__69));
v___x_1873_ = ((lean_object*)(l_main___closed__331));
v___y_1676_ = v___y_1760_;
v_fst_1677_ = v___x_1872_;
v_snd_1678_ = v___x_1873_;
goto v___jp_1675_;
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_args_1577_);
v_a_1876_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1674_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1674_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_args_1577_);
v_a_1884_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1673_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1673_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_args_1577_);
v_a_1892_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1670_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1670_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
v___jp_1579_:
{
lean_object* v___x_1583_; 
lean_inc_ref(v___y_1582_);
v___x_1583_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___y_1582_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1583_, 0);
lean_dec(v_unused_1596_);
v___x_1585_ = v___x_1583_;
v_isShared_1586_ = v_isSharedCheck_1595_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v___x_1583_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1595_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
if (v___y_1581_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = lean_box_uint32(v___y_1580_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1587_);
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_main___boxed__const__1;
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1591_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1583_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1583_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1605_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_NER_loadedScan(v___y_1608_, v___y_1609_, v___y_1606_);
lean_dec_ref(v___y_1606_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; uint8_t v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = lean_unbox(v_a_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_main___closed__0));
v___x_1614_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
v___y_1580_ = v___y_1607_;
v___y_1581_ = v___x_1614_;
v___y_1582_ = v___x_1613_;
goto v___jp_1579_;
}
else
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_main___closed__1));
v___x_1616_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
v___y_1580_ = v___y_1607_;
v___y_1581_ = v___x_1616_;
v___y_1582_ = v___x_1615_;
goto v___jp_1579_;
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1610_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1610_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1625_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_IO_FS_lines(v___y_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; size_t v_sz_1634_; lean_object* v___x_1635_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v_sz_1634_ = lean_array_size(v_a_1633_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_a_1633_, v_sz_1634_, v___y_1628_, v___y_1627_);
lean_dec(v_a_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
if (v___y_1626_ == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = ((lean_object*)(l_main___closed__2));
v___y_1606_ = v_a_1636_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___y_1630_;
v___y_1609_ = v___x_1637_;
goto v___jp_1605_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1639_ = ((lean_object*)(l_main___closed__3));
v___y_1606_ = v_a_1638_;
v___y_1607_ = v___y_1629_;
v___y_1608_ = v___y_1630_;
v___y_1609_ = v___x_1639_;
goto v___jp_1605_;
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___y_1630_);
v_a_1640_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1635_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1627_);
v_a_1648_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1632_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1632_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
v___jp_1656_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1662_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___y_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_1665_ = lean_string_dec_eq(v___y_1658_, v___x_1664_);
lean_dec_ref(v___y_1658_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_main___closed__5));
v___y_1626_ = v___x_1665_;
v___y_1627_ = v___x_1663_;
v___y_1628_ = v___y_1657_;
v___y_1629_ = v___y_1659_;
v___y_1630_ = v___y_1660_;
v___y_1631_ = v___x_1666_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_main___closed__6));
v___y_1626_ = v___x_1665_;
v___y_1627_ = v___x_1663_;
v___y_1628_ = v___y_1657_;
v___y_1629_ = v___y_1659_;
v___y_1630_ = v___y_1660_;
v___y_1631_ = v___x_1667_;
goto v___jp_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = _lean_main(v_args_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_1903_, lean_object* v_as_x27_1904_, lean_object* v_b_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1904_, v_b_1905_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_1909_, lean_object* v_as_x27_1910_, lean_object* v_b_1911_, lean_object* v_a_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_1909_, v_as_x27_1910_, v_b_1911_, v_a_1912_);
lean_dec(v_as_x27_1910_);
lean_dec(v_as_1909_);
return v_res_1914_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFS__ProofDriver(uint8_t builtin) {
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
  res = initialize_NFS__ProofDriver(1 /* builtin */);
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
