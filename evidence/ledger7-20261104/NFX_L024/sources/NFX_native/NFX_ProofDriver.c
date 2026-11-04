// Lean compiler output
// Module: NFX_ProofDriver
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
static const lean_string_object l_main___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof27"};
static const lean_object* l_main___closed__44 = (const lean_object*)&l_main___closed__44_value;
static const lean_string_object l_main___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof28"};
static const lean_object* l_main___closed__45 = (const lean_object*)&l_main___closed__45_value;
static const lean_string_object l_main___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof29"};
static const lean_object* l_main___closed__46 = (const lean_object*)&l_main___closed__46_value;
static const lean_string_object l_main___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof30"};
static const lean_object* l_main___closed__47 = (const lean_object*)&l_main___closed__47_value;
static const lean_string_object l_main___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof31"};
static const lean_object* l_main___closed__48 = (const lean_object*)&l_main___closed__48_value;
static const lean_string_object l_main___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof32"};
static const lean_object* l_main___closed__49 = (const lean_object*)&l_main___closed__49_value;
static const lean_string_object l_main___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof33"};
static const lean_object* l_main___closed__50 = (const lean_object*)&l_main___closed__50_value;
static const lean_string_object l_main___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof34"};
static const lean_object* l_main___closed__51 = (const lean_object*)&l_main___closed__51_value;
static const lean_string_object l_main___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof35"};
static const lean_object* l_main___closed__52 = (const lean_object*)&l_main___closed__52_value;
static const lean_string_object l_main___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof36"};
static const lean_object* l_main___closed__53 = (const lean_object*)&l_main___closed__53_value;
static const lean_string_object l_main___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof37"};
static const lean_object* l_main___closed__54 = (const lean_object*)&l_main___closed__54_value;
static const lean_string_object l_main___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof38"};
static const lean_object* l_main___closed__55 = (const lean_object*)&l_main___closed__55_value;
static const lean_string_object l_main___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof39"};
static const lean_object* l_main___closed__56 = (const lean_object*)&l_main___closed__56_value;
static const lean_string_object l_main___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof40"};
static const lean_object* l_main___closed__57 = (const lean_object*)&l_main___closed__57_value;
static const lean_string_object l_main___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof41"};
static const lean_object* l_main___closed__58 = (const lean_object*)&l_main___closed__58_value;
static const lean_string_object l_main___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof42"};
static const lean_object* l_main___closed__59 = (const lean_object*)&l_main___closed__59_value;
static const lean_string_object l_main___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof43"};
static const lean_object* l_main___closed__60 = (const lean_object*)&l_main___closed__60_value;
static const lean_string_object l_main___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof44"};
static const lean_object* l_main___closed__61 = (const lean_object*)&l_main___closed__61_value;
static const lean_string_object l_main___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof45"};
static const lean_object* l_main___closed__62 = (const lean_object*)&l_main___closed__62_value;
static const lean_string_object l_main___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof46"};
static const lean_object* l_main___closed__63 = (const lean_object*)&l_main___closed__63_value;
static const lean_string_object l_main___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof47"};
static const lean_object* l_main___closed__64 = (const lean_object*)&l_main___closed__64_value;
static const lean_string_object l_main___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof48"};
static const lean_object* l_main___closed__65 = (const lean_object*)&l_main___closed__65_value;
static const lean_string_object l_main___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof49"};
static const lean_object* l_main___closed__66 = (const lean_object*)&l_main___closed__66_value;
static const lean_string_object l_main___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof50"};
static const lean_object* l_main___closed__67 = (const lean_object*)&l_main___closed__67_value;
static const lean_string_object l_main___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof51"};
static const lean_object* l_main___closed__68 = (const lean_object*)&l_main___closed__68_value;
static const lean_string_object l_main___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof52"};
static const lean_object* l_main___closed__69 = (const lean_object*)&l_main___closed__69_value;
static const lean_string_object l_main___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof53"};
static const lean_object* l_main___closed__70 = (const lean_object*)&l_main___closed__70_value;
static const lean_string_object l_main___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof54"};
static const lean_object* l_main___closed__71 = (const lean_object*)&l_main___closed__71_value;
static const lean_string_object l_main___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof55"};
static const lean_object* l_main___closed__72 = (const lean_object*)&l_main___closed__72_value;
static const lean_string_object l_main___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof56"};
static const lean_object* l_main___closed__73 = (const lean_object*)&l_main___closed__73_value;
static const lean_string_object l_main___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof57"};
static const lean_object* l_main___closed__74 = (const lean_object*)&l_main___closed__74_value;
static const lean_string_object l_main___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof58"};
static const lean_object* l_main___closed__75 = (const lean_object*)&l_main___closed__75_value;
static const lean_string_object l_main___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof59"};
static const lean_object* l_main___closed__76 = (const lean_object*)&l_main___closed__76_value;
static const lean_string_object l_main___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof60"};
static const lean_object* l_main___closed__77 = (const lean_object*)&l_main___closed__77_value;
static const lean_string_object l_main___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof61"};
static const lean_object* l_main___closed__78 = (const lean_object*)&l_main___closed__78_value;
static const lean_string_object l_main___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof62"};
static const lean_object* l_main___closed__79 = (const lean_object*)&l_main___closed__79_value;
static const lean_string_object l_main___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof63"};
static const lean_object* l_main___closed__80 = (const lean_object*)&l_main___closed__80_value;
static const lean_string_object l_main___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof64"};
static const lean_object* l_main___closed__81 = (const lean_object*)&l_main___closed__81_value;
static const lean_string_object l_main___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proof65"};
static const lean_object* l_main___closed__82 = (const lean_object*)&l_main___closed__82_value;
static const lean_string_object l_main___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixtures"};
static const lean_object* l_main___closed__83 = (const lean_object*)&l_main___closed__83_value;
static const lean_string_object l_main___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__84 = (const lean_object*)&l_main___closed__84_value;
static const lean_ctor_object l_main___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__85 = (const lean_object*)&l_main___closed__85_value;
static const lean_string_object l_main___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__86 = (const lean_object*)&l_main___closed__86_value;
static const lean_ctor_object l_main___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__86_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__87 = (const lean_object*)&l_main___closed__87_value;
static const lean_array_object l_main___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__85_value),((lean_object*)&l_main___closed__87_value)}};
static const lean_object* l_main___closed__88 = (const lean_object*)&l_main___closed__88_value;
static const lean_string_object l_main___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "matcher"};
static const lean_object* l_main___closed__89 = (const lean_object*)&l_main___closed__89_value;
static const lean_ctor_object l_main___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__90_value_aux_0),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(253, 181, 2, 131, 135, 118, 135, 6)}};
static const lean_object* l_main___closed__90 = (const lean_object*)&l_main___closed__90_value;
static const lean_string_object l_main___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "viaPrivate"};
static const lean_object* l_main___closed__91 = (const lean_object*)&l_main___closed__91_value;
static const lean_ctor_object l_main___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__92_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(35, 130, 62, 22, 1, 121, 183, 4)}};
static const lean_object* l_main___closed__92 = (const lean_object*)&l_main___closed__92_value;
static const lean_string_object l_main___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l_main___closed__93 = (const lean_object*)&l_main___closed__93_value;
static const lean_ctor_object l_main___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__94_value_aux_0),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(7, 238, 250, 90, 115, 235, 69, 48)}};
static const lean_object* l_main___closed__94 = (const lean_object*)&l_main___closed__94_value;
static const lean_string_object l_main___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "viaAux"};
static const lean_object* l_main___closed__95 = (const lean_object*)&l_main___closed__95_value;
static const lean_ctor_object l_main___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__84_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_ctor_object l_main___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__96_value_aux_0),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(167, 202, 141, 203, 144, 120, 32, 232)}};
static const lean_object* l_main___closed__96 = (const lean_object*)&l_main___closed__96_value;
static const lean_string_object l_main___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateMatch"};
static const lean_object* l_main___closed__97 = (const lean_object*)&l_main___closed__97_value;
static const lean_ctor_object l_main___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__97_value),LEAN_SCALAR_PTR_LITERAL(239, 255, 4, 243, 213, 192, 165, 245)}};
static const lean_ctor_object l_main___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__98_value_aux_0),((lean_object*)&l_main___closed__89_value),LEAN_SCALAR_PTR_LITERAL(250, 175, 228, 189, 54, 79, 90, 26)}};
static const lean_object* l_main___closed__98 = (const lean_object*)&l_main___closed__98_value;
static const lean_string_object l_main___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEP_MutatePrivate"};
static const lean_object* l_main___closed__99 = (const lean_object*)&l_main___closed__99_value;
static const lean_ctor_object l_main___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__99_value),LEAN_SCALAR_PTR_LITERAL(28, 155, 74, 33, 174, 250, 36, 233)}};
static const lean_ctor_object l_main___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__100_value_aux_0),((lean_object*)&l_main___closed__91_value),LEAN_SCALAR_PTR_LITERAL(235, 43, 53, 185, 48, 156, 219, 12)}};
static const lean_object* l_main___closed__100 = (const lean_object*)&l_main___closed__100_value;
static const lean_string_object l_main___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NEP_MutateProof"};
static const lean_object* l_main___closed__101 = (const lean_object*)&l_main___closed__101_value;
static const lean_ctor_object l_main___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__101_value),LEAN_SCALAR_PTR_LITERAL(148, 171, 94, 1, 237, 235, 188, 117)}};
static const lean_ctor_object l_main___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__102_value_aux_0),((lean_object*)&l_main___closed__93_value),LEAN_SCALAR_PTR_LITERAL(103, 160, 4, 235, 138, 80, 29, 174)}};
static const lean_object* l_main___closed__102 = (const lean_object*)&l_main___closed__102_value;
static const lean_string_object l_main___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_MutateAux"};
static const lean_object* l_main___closed__103 = (const lean_object*)&l_main___closed__103_value;
static const lean_ctor_object l_main___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__103_value),LEAN_SCALAR_PTR_LITERAL(39, 73, 55, 51, 55, 251, 91, 228)}};
static const lean_ctor_object l_main___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__104_value_aux_0),((lean_object*)&l_main___closed__95_value),LEAN_SCALAR_PTR_LITERAL(184, 32, 86, 198, 95, 60, 4, 116)}};
static const lean_object* l_main___closed__104 = (const lean_object*)&l_main___closed__104_value;
static const lean_array_object l_main___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 246}, .m_size = 8, .m_capacity = 8, .m_data = {((lean_object*)&l_main___closed__90_value),((lean_object*)&l_main___closed__92_value),((lean_object*)&l_main___closed__94_value),((lean_object*)&l_main___closed__96_value),((lean_object*)&l_main___closed__98_value),((lean_object*)&l_main___closed__100_value),((lean_object*)&l_main___closed__102_value),((lean_object*)&l_main___closed__104_value)}};
static const lean_object* l_main___closed__105 = (const lean_object*)&l_main___closed__105_value;
static const lean_string_object l_main___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFX_COMBINED_IMPORT"};
static const lean_object* l_main___closed__106 = (const lean_object*)&l_main___closed__106_value;
static const lean_ctor_object l_main___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__106_value),LEAN_SCALAR_PTR_LITERAL(210, 149, 221, 142, 63, 79, 252, 163)}};
static const lean_object* l_main___closed__107 = (const lean_object*)&l_main___closed__107_value;
static const lean_array_object l_main___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__107_value)}};
static const lean_object* l_main___closed__108 = (const lean_object*)&l_main___closed__108_value;
static const lean_string_object l_main___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFS_NEV_AccumPacket"};
static const lean_object* l_main___closed__109 = (const lean_object*)&l_main___closed__109_value;
static const lean_string_object l_main___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "result_state_effects"};
static const lean_object* l_main___closed__110 = (const lean_object*)&l_main___closed__110_value;
static const lean_ctor_object l_main___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__111_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(225, 84, 179, 156, 73, 95, 72, 85)}};
static const lean_object* l_main___closed__111 = (const lean_object*)&l_main___closed__111_value;
static const lean_string_object l_main___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "NFS_NEV_AccumulateComplete"};
static const lean_object* l_main___closed__112 = (const lean_object*)&l_main___closed__112_value;
static const lean_string_object l_main___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "native"};
static const lean_object* l_main___closed__113 = (const lean_object*)&l_main___closed__113_value;
static const lean_ctor_object l_main___closed__114_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(33, 61, 229, 173, 207, 253, 39, 17)}};
static const lean_ctor_object l_main___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__114_value_aux_0),((lean_object*)&l_main___closed__113_value),LEAN_SCALAR_PTR_LITERAL(178, 236, 206, 186, 163, 193, 147, 152)}};
static const lean_object* l_main___closed__114 = (const lean_object*)&l_main___closed__114_value;
static const lean_string_object l_main___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reference"};
static const lean_object* l_main___closed__115 = (const lean_object*)&l_main___closed__115_value;
static const lean_ctor_object l_main___closed__116_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__112_value),LEAN_SCALAR_PTR_LITERAL(33, 61, 229, 173, 207, 253, 39, 17)}};
static const lean_ctor_object l_main___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__116_value_aux_0),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(33, 110, 209, 209, 192, 49, 240, 77)}};
static const lean_object* l_main___closed__116 = (const lean_object*)&l_main___closed__116_value;
static const lean_array_object l_main___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_main___closed__111_value),((lean_object*)&l_main___closed__114_value),((lean_object*)&l_main___closed__116_value)}};
static const lean_object* l_main___closed__117 = (const lean_object*)&l_main___closed__117_value;
static const lean_string_object l_main___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFQ_WideGetters"};
static const lean_object* l_main___closed__118 = (const lean_object*)&l_main___closed__118_value;
static const lean_string_object l_main___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "c0"};
static const lean_object* l_main___closed__119 = (const lean_object*)&l_main___closed__119_value;
static const lean_ctor_object l_main___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 28, 12, 81, 208, 231, 58)}};
static const lean_ctor_object l_main___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__120_value_aux_0),((lean_object*)&l_main___closed__119_value),LEAN_SCALAR_PTR_LITERAL(119, 106, 9, 6, 223, 253, 134, 91)}};
static const lean_object* l_main___closed__120 = (const lean_object*)&l_main___closed__120_value;
static const lean_string_object l_main___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "c1"};
static const lean_object* l_main___closed__121 = (const lean_object*)&l_main___closed__121_value;
static const lean_ctor_object l_main___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__118_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 28, 12, 81, 208, 231, 58)}};
static const lean_ctor_object l_main___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__122_value_aux_0),((lean_object*)&l_main___closed__121_value),LEAN_SCALAR_PTR_LITERAL(186, 188, 212, 233, 2, 145, 223, 80)}};
static const lean_object* l_main___closed__122 = (const lean_object*)&l_main___closed__122_value;
static const lean_string_object l_main___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "no_base_dependency"};
static const lean_object* l_main___closed__123 = (const lean_object*)&l_main___closed__123_value;
static const lean_ctor_object l_main___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__124_value_aux_0),((lean_object*)&l_main___closed__123_value),LEAN_SCALAR_PTR_LITERAL(170, 191, 181, 162, 0, 4, 56, 69)}};
static const lean_object* l_main___closed__124 = (const lean_object*)&l_main___closed__124_value;
static const lean_string_object l_main___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "raw_length"};
static const lean_object* l_main___closed__125 = (const lean_object*)&l_main___closed__125_value;
static const lean_ctor_object l_main___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__109_value),LEAN_SCALAR_PTR_LITERAL(43, 26, 189, 228, 139, 64, 51, 104)}};
static const lean_ctor_object l_main___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__126_value_aux_0),((lean_object*)&l_main___closed__125_value),LEAN_SCALAR_PTR_LITERAL(47, 26, 123, 75, 83, 151, 136, 28)}};
static const lean_object* l_main___closed__126 = (const lean_object*)&l_main___closed__126_value;
static const lean_array_object l_main___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__120_value),((lean_object*)&l_main___closed__122_value),((lean_object*)&l_main___closed__124_value),((lean_object*)&l_main___closed__126_value)}};
static const lean_object* l_main___closed__127 = (const lean_object*)&l_main___closed__127_value;
static const lean_string_object l_main___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFQ_StatementLaws"};
static const lean_object* l_main___closed__128 = (const lean_object*)&l_main___closed__128_value;
static const lean_string_object l_main___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "limbs_reference"};
static const lean_object* l_main___closed__129 = (const lean_object*)&l_main___closed__129_value;
static const lean_ctor_object l_main___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__128_value),LEAN_SCALAR_PTR_LITERAL(206, 161, 199, 128, 175, 150, 227, 224)}};
static const lean_ctor_object l_main___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__130_value_aux_0),((lean_object*)&l_main___closed__129_value),LEAN_SCALAR_PTR_LITERAL(187, 219, 185, 171, 191, 183, 17, 88)}};
static const lean_object* l_main___closed__130 = (const lean_object*)&l_main___closed__130_value;
static const lean_string_object l_main___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFQ_Transport"};
static const lean_object* l_main___closed__131 = (const lean_object*)&l_main___closed__131_value;
static const lean_string_object l_main___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "checkpoint_size_reference"};
static const lean_object* l_main___closed__132 = (const lean_object*)&l_main___closed__132_value;
static const lean_ctor_object l_main___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__131_value),LEAN_SCALAR_PTR_LITERAL(252, 209, 218, 202, 21, 125, 88, 29)}};
static const lean_ctor_object l_main___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__133_value_aux_0),((lean_object*)&l_main___closed__132_value),LEAN_SCALAR_PTR_LITERAL(133, 5, 214, 44, 194, 77, 223, 228)}};
static const lean_object* l_main___closed__133 = (const lean_object*)&l_main___closed__133_value;
static const lean_string_object l_main___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "final_len_reference"};
static const lean_object* l_main___closed__134 = (const lean_object*)&l_main___closed__134_value;
static const lean_ctor_object l_main___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__131_value),LEAN_SCALAR_PTR_LITERAL(252, 209, 218, 202, 21, 125, 88, 29)}};
static const lean_ctor_object l_main___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__135_value_aux_0),((lean_object*)&l_main___closed__134_value),LEAN_SCALAR_PTR_LITERAL(109, 196, 44, 190, 198, 20, 2, 61)}};
static const lean_object* l_main___closed__135 = (const lean_object*)&l_main___closed__135_value;
static const lean_string_object l_main___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "folds_reference"};
static const lean_object* l_main___closed__136 = (const lean_object*)&l_main___closed__136_value;
static const lean_ctor_object l_main___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__131_value),LEAN_SCALAR_PTR_LITERAL(252, 209, 218, 202, 21, 125, 88, 29)}};
static const lean_ctor_object l_main___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__137_value_aux_0),((lean_object*)&l_main___closed__136_value),LEAN_SCALAR_PTR_LITERAL(74, 66, 187, 148, 134, 128, 162, 42)}};
static const lean_object* l_main___closed__137 = (const lean_object*)&l_main___closed__137_value;
static const lean_array_object l_main___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__130_value),((lean_object*)&l_main___closed__133_value),((lean_object*)&l_main___closed__135_value),((lean_object*)&l_main___closed__137_value)}};
static const lean_object* l_main___closed__138 = (const lean_object*)&l_main___closed__138_value;
static const lean_string_object l_main___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFQ_RowShape"};
static const lean_object* l_main___closed__139 = (const lean_object*)&l_main___closed__139_value;
static const lean_string_object l_main___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "compact_reference"};
static const lean_object* l_main___closed__140 = (const lean_object*)&l_main___closed__140_value;
static const lean_ctor_object l_main___closed__141_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__139_value),LEAN_SCALAR_PTR_LITERAL(122, 68, 235, 42, 201, 209, 233, 190)}};
static const lean_ctor_object l_main___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__141_value_aux_0),((lean_object*)&l_main___closed__140_value),LEAN_SCALAR_PTR_LITERAL(46, 221, 252, 8, 126, 49, 233, 223)}};
static const lean_object* l_main___closed__141 = (const lean_object*)&l_main___closed__141_value;
static const lean_ctor_object l_main___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__139_value),LEAN_SCALAR_PTR_LITERAL(122, 68, 235, 42, 201, 209, 233, 190)}};
static const lean_ctor_object l_main___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__142_value_aux_0),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(126, 79, 145, 78, 147, 246, 150, 218)}};
static const lean_object* l_main___closed__142 = (const lean_object*)&l_main___closed__142_value;
static const lean_string_object l_main___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "copied_reference"};
static const lean_object* l_main___closed__143 = (const lean_object*)&l_main___closed__143_value;
static const lean_ctor_object l_main___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__128_value),LEAN_SCALAR_PTR_LITERAL(206, 161, 199, 128, 175, 150, 227, 224)}};
static const lean_ctor_object l_main___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__144_value_aux_0),((lean_object*)&l_main___closed__143_value),LEAN_SCALAR_PTR_LITERAL(160, 240, 83, 241, 118, 81, 245, 140)}};
static const lean_object* l_main___closed__144 = (const lean_object*)&l_main___closed__144_value;
static const lean_string_object l_main___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected_reference"};
static const lean_object* l_main___closed__145 = (const lean_object*)&l_main___closed__145_value;
static const lean_ctor_object l_main___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__128_value),LEAN_SCALAR_PTR_LITERAL(206, 161, 199, 128, 175, 150, 227, 224)}};
static const lean_ctor_object l_main___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__146_value_aux_0),((lean_object*)&l_main___closed__145_value),LEAN_SCALAR_PTR_LITERAL(191, 192, 224, 95, 37, 181, 188, 83)}};
static const lean_object* l_main___closed__146 = (const lean_object*)&l_main___closed__146_value;
static const lean_array_object l_main___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__141_value),((lean_object*)&l_main___closed__142_value),((lean_object*)&l_main___closed__144_value),((lean_object*)&l_main___closed__146_value)}};
static const lean_object* l_main___closed__147 = (const lean_object*)&l_main___closed__147_value;
static const lean_string_object l_main___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFQ_FieldLaws"};
static const lean_object* l_main___closed__148 = (const lean_object*)&l_main___closed__148_value;
static const lean_string_object l_main___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "qm_reference"};
static const lean_object* l_main___closed__149 = (const lean_object*)&l_main___closed__149_value;
static const lean_ctor_object l_main___closed__150_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 214, 188, 156, 223, 128, 12)}};
static const lean_ctor_object l_main___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__150_value_aux_0),((lean_object*)&l_main___closed__149_value),LEAN_SCALAR_PTR_LITERAL(80, 122, 145, 48, 27, 72, 232, 99)}};
static const lean_object* l_main___closed__150 = (const lean_object*)&l_main___closed__150_value;
static const lean_string_object l_main___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NFQ_PreparedMultiplier"};
static const lean_object* l_main___closed__151 = (const lean_object*)&l_main___closed__151_value;
static const lean_string_object l_main___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_main___closed__152 = (const lean_object*)&l_main___closed__152_value;
static const lean_ctor_object l_main___closed__153_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__151_value),LEAN_SCALAR_PTR_LITERAL(53, 155, 177, 105, 178, 204, 3, 29)}};
static const lean_ctor_object l_main___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__153_value_aux_0),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(131, 203, 233, 206, 224, 130, 72, 124)}};
static const lean_object* l_main___closed__153 = (const lean_object*)&l_main___closed__153_value;
static const lean_string_object l_main___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFQ_Readonly"};
static const lean_object* l_main___closed__154 = (const lean_object*)&l_main___closed__154_value;
static const lean_ctor_object l_main___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__154_value),LEAN_SCALAR_PTR_LITERAL(168, 71, 70, 125, 21, 244, 245, 28)}};
static const lean_ctor_object l_main___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__155_value_aux_0),((lean_object*)&l_main___closed__115_value),LEAN_SCALAR_PTR_LITERAL(100, 176, 154, 101, 105, 13, 157, 231)}};
static const lean_object* l_main___closed__155 = (const lean_object*)&l_main___closed__155_value;
static const lean_string_object l_main___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFQ_Reduce"};
static const lean_object* l_main___closed__156 = (const lean_object*)&l_main___closed__156_value;
static const lean_ctor_object l_main___closed__157_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__156_value),LEAN_SCALAR_PTR_LITERAL(229, 54, 236, 173, 226, 64, 172, 40)}};
static const lean_ctor_object l_main___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__157_value_aux_0),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(243, 45, 58, 240, 220, 155, 246, 23)}};
static const lean_object* l_main___closed__157 = (const lean_object*)&l_main___closed__157_value;
static const lean_array_object l_main___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__150_value),((lean_object*)&l_main___closed__153_value),((lean_object*)&l_main___closed__155_value),((lean_object*)&l_main___closed__157_value)}};
static const lean_object* l_main___closed__158 = (const lean_object*)&l_main___closed__158_value;
static const lean_string_object l_main___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFN_PhaseTransport"};
static const lean_object* l_main___closed__159 = (const lean_object*)&l_main___closed__159_value;
static const lean_string_object l_main___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "owner_roundtrip"};
static const lean_object* l_main___closed__160 = (const lean_object*)&l_main___closed__160_value;
static const lean_ctor_object l_main___closed__161_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(191, 47, 115, 195, 48, 235, 220, 99)}};
static const lean_ctor_object l_main___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__161_value_aux_0),((lean_object*)&l_main___closed__160_value),LEAN_SCALAR_PTR_LITERAL(238, 0, 98, 228, 93, 166, 193, 186)}};
static const lean_object* l_main___closed__161 = (const lean_object*)&l_main___closed__161_value;
static const lean_string_object l_main___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFN_ReserveOwner"};
static const lean_object* l_main___closed__162 = (const lean_object*)&l_main___closed__162_value;
static const lean_string_object l_main___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "error_owner"};
static const lean_object* l_main___closed__163 = (const lean_object*)&l_main___closed__163_value;
static const lean_ctor_object l_main___closed__164_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__162_value),LEAN_SCALAR_PTR_LITERAL(103, 63, 80, 96, 152, 30, 17, 210)}};
static const lean_ctor_object l_main___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__164_value_aux_0),((lean_object*)&l_main___closed__163_value),LEAN_SCALAR_PTR_LITERAL(206, 23, 19, 171, 253, 101, 57, 1)}};
static const lean_object* l_main___closed__164 = (const lean_object*)&l_main___closed__164_value;
static const lean_string_object l_main___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "cm_reference"};
static const lean_object* l_main___closed__165 = (const lean_object*)&l_main___closed__165_value;
static const lean_ctor_object l_main___closed__166_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 214, 188, 156, 223, 128, 12)}};
static const lean_ctor_object l_main___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__166_value_aux_0),((lean_object*)&l_main___closed__165_value),LEAN_SCALAR_PTR_LITERAL(226, 235, 192, 53, 39, 161, 120, 161)}};
static const lean_object* l_main___closed__166 = (const lean_object*)&l_main___closed__166_value;
static const lean_string_object l_main___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "neg_value"};
static const lean_object* l_main___closed__167 = (const lean_object*)&l_main___closed__167_value;
static const lean_ctor_object l_main___closed__168_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__148_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 214, 188, 156, 223, 128, 12)}};
static const lean_ctor_object l_main___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__168_value_aux_0),((lean_object*)&l_main___closed__167_value),LEAN_SCALAR_PTR_LITERAL(41, 159, 90, 185, 134, 119, 156, 44)}};
static const lean_object* l_main___closed__168 = (const lean_object*)&l_main___closed__168_value;
static const lean_array_object l_main___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__161_value),((lean_object*)&l_main___closed__164_value),((lean_object*)&l_main___closed__166_value),((lean_object*)&l_main___closed__168_value)}};
static const lean_object* l_main___closed__169 = (const lean_object*)&l_main___closed__169_value;
static const lean_string_object l_main___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NFN_NFB_GeometryInstall"};
static const lean_object* l_main___closed__170 = (const lean_object*)&l_main___closed__170_value;
static const lean_string_object l_main___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_main___closed__171 = (const lean_object*)&l_main___closed__171_value;
static const lean_ctor_object l_main___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__170_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 153, 0, 98, 205, 76, 177)}};
static const lean_ctor_object l_main___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__172_value_aux_0),((lean_object*)&l_main___closed__171_value),LEAN_SCALAR_PTR_LITERAL(144, 189, 230, 30, 19, 76, 2, 109)}};
static const lean_object* l_main___closed__172 = (const lean_object*)&l_main___closed__172_value;
static const lean_string_object l_main___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "legacy_roundtrip"};
static const lean_object* l_main___closed__173 = (const lean_object*)&l_main___closed__173_value;
static const lean_ctor_object l_main___closed__174_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(191, 47, 115, 195, 48, 235, 220, 99)}};
static const lean_ctor_object l_main___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__174_value_aux_0),((lean_object*)&l_main___closed__173_value),LEAN_SCALAR_PTR_LITERAL(81, 124, 164, 101, 84, 16, 41, 47)}};
static const lean_object* l_main___closed__174 = (const lean_object*)&l_main___closed__174_value;
static const lean_string_object l_main___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "observer_none"};
static const lean_object* l_main___closed__175 = (const lean_object*)&l_main___closed__175_value;
static const lean_ctor_object l_main___closed__176_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(191, 47, 115, 195, 48, 235, 220, 99)}};
static const lean_ctor_object l_main___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__176_value_aux_0),((lean_object*)&l_main___closed__175_value),LEAN_SCALAR_PTR_LITERAL(90, 6, 238, 207, 70, 207, 229, 31)}};
static const lean_object* l_main___closed__176 = (const lean_object*)&l_main___closed__176_value;
static const lean_string_object l_main___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "observer_some"};
static const lean_object* l_main___closed__177 = (const lean_object*)&l_main___closed__177_value;
static const lean_ctor_object l_main___closed__178_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__159_value),LEAN_SCALAR_PTR_LITERAL(191, 47, 115, 195, 48, 235, 220, 99)}};
static const lean_ctor_object l_main___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__178_value_aux_0),((lean_object*)&l_main___closed__177_value),LEAN_SCALAR_PTR_LITERAL(249, 241, 146, 66, 143, 66, 199, 94)}};
static const lean_object* l_main___closed__178 = (const lean_object*)&l_main___closed__178_value;
static const lean_array_object l_main___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__172_value),((lean_object*)&l_main___closed__174_value),((lean_object*)&l_main___closed__176_value),((lean_object*)&l_main___closed__178_value)}};
static const lean_object* l_main___closed__179 = (const lean_object*)&l_main___closed__179_value;
static const lean_string_object l_main___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "NFN_NFB_GeometryComposed"};
static const lean_object* l_main___closed__180 = (const lean_object*)&l_main___closed__180_value;
static const lean_string_object l_main___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "accepted_physical"};
static const lean_object* l_main___closed__181 = (const lean_object*)&l_main___closed__181_value;
static const lean_ctor_object l_main___closed__182_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__180_value),LEAN_SCALAR_PTR_LITERAL(79, 80, 161, 152, 193, 207, 152, 79)}};
static const lean_ctor_object l_main___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__182_value_aux_0),((lean_object*)&l_main___closed__181_value),LEAN_SCALAR_PTR_LITERAL(184, 170, 73, 254, 222, 102, 23, 251)}};
static const lean_object* l_main___closed__182 = (const lean_object*)&l_main___closed__182_value;
static const lean_ctor_object l_main___closed__183_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__180_value),LEAN_SCALAR_PTR_LITERAL(79, 80, 161, 152, 193, 207, 152, 79)}};
static const lean_ctor_object l_main___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__183_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(109, 4, 254, 8, 96, 138, 107, 119)}};
static const lean_object* l_main___closed__183 = (const lean_object*)&l_main___closed__183_value;
static const lean_string_object l_main___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "loop"};
static const lean_object* l_main___closed__184 = (const lean_object*)&l_main___closed__184_value;
static const lean_ctor_object l_main___closed__185_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__170_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 153, 0, 98, 205, 76, 177)}};
static const lean_ctor_object l_main___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__185_value_aux_0),((lean_object*)&l_main___closed__184_value),LEAN_SCALAR_PTR_LITERAL(60, 193, 63, 111, 12, 236, 1, 71)}};
static const lean_object* l_main___closed__185 = (const lean_object*)&l_main___closed__185_value;
static const lean_string_object l_main___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "standard"};
static const lean_object* l_main___closed__186 = (const lean_object*)&l_main___closed__186_value;
static const lean_ctor_object l_main___closed__187_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__170_value),LEAN_SCALAR_PTR_LITERAL(104, 7, 153, 0, 98, 205, 76, 177)}};
static const lean_ctor_object l_main___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__187_value_aux_0),((lean_object*)&l_main___closed__186_value),LEAN_SCALAR_PTR_LITERAL(190, 167, 47, 143, 215, 91, 200, 187)}};
static const lean_object* l_main___closed__187 = (const lean_object*)&l_main___closed__187_value;
static const lean_array_object l_main___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__182_value),((lean_object*)&l_main___closed__183_value),((lean_object*)&l_main___closed__185_value),((lean_object*)&l_main___closed__187_value)}};
static const lean_object* l_main___closed__188 = (const lean_object*)&l_main___closed__188_value;
static const lean_string_object l_main___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NEX_Exact"};
static const lean_object* l_main___closed__189 = (const lean_object*)&l_main___closed__189_value;
static const lean_ctor_object l_main___closed__190_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__189_value),LEAN_SCALAR_PTR_LITERAL(91, 40, 73, 16, 247, 126, 207, 236)}};
static const lean_ctor_object l_main___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__190_value_aux_0),((lean_object*)&l_main___closed__110_value),LEAN_SCALAR_PTR_LITERAL(113, 217, 35, 165, 210, 193, 253, 86)}};
static const lean_object* l_main___closed__190 = (const lean_object*)&l_main___closed__190_value;
static const lean_string_object l_main___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFG_InversePanic"};
static const lean_object* l_main___closed__191 = (const lean_object*)&l_main___closed__191_value;
static const lean_string_object l_main___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_main___closed__192 = (const lean_object*)&l_main___closed__192_value;
static const lean_ctor_object l_main___closed__193_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__191_value),LEAN_SCALAR_PTR_LITERAL(240, 161, 69, 22, 154, 111, 25, 64)}};
static const lean_ctor_object l_main___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__193_value_aux_0),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(188, 135, 170, 201, 63, 194, 39, 69)}};
static const lean_object* l_main___closed__193 = (const lean_object*)&l_main___closed__193_value;
static const lean_string_object l_main___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFG_InverseZeroDomain"};
static const lean_object* l_main___closed__194 = (const lean_object*)&l_main___closed__194_value;
static const lean_string_object l_main___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unique"};
static const lean_object* l_main___closed__195 = (const lean_object*)&l_main___closed__195_value;
static const lean_ctor_object l_main___closed__196_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__194_value),LEAN_SCALAR_PTR_LITERAL(174, 137, 27, 223, 242, 173, 186, 14)}};
static const lean_ctor_object l_main___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__196_value_aux_0),((lean_object*)&l_main___closed__195_value),LEAN_SCALAR_PTR_LITERAL(112, 68, 232, 65, 158, 34, 125, 181)}};
static const lean_object* l_main___closed__196 = (const lean_object*)&l_main___closed__196_value;
static const lean_string_object l_main___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "NFN_NEW_GeometryComplete"};
static const lean_object* l_main___closed__197 = (const lean_object*)&l_main___closed__197_value;
static const lean_string_object l_main___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l_main___closed__198 = (const lean_object*)&l_main___closed__198_value;
static const lean_ctor_object l_main___closed__199_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__197_value),LEAN_SCALAR_PTR_LITERAL(199, 70, 141, 125, 235, 114, 115, 108)}};
static const lean_ctor_object l_main___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__199_value_aux_0),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(232, 201, 204, 108, 227, 37, 146, 140)}};
static const lean_object* l_main___closed__199 = (const lean_object*)&l_main___closed__199_value;
static const lean_array_object l_main___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__190_value),((lean_object*)&l_main___closed__193_value),((lean_object*)&l_main___closed__196_value),((lean_object*)&l_main___closed__199_value)}};
static const lean_object* l_main___closed__200 = (const lean_object*)&l_main___closed__200_value;
static const lean_string_object l_main___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "AspisR1"};
static const lean_object* l_main___closed__201 = (const lean_object*)&l_main___closed__201_value;
static const lean_string_object l_main___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RPx_Deployed"};
static const lean_object* l_main___closed__202 = (const lean_object*)&l_main___closed__202_value;
static const lean_string_object l_main___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deployed"};
static const lean_object* l_main___closed__203 = (const lean_object*)&l_main___closed__203_value;
static const lean_ctor_object l_main___closed__204_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__204_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_0),((lean_object*)&l_main___closed__202_value),LEAN_SCALAR_PTR_LITERAL(63, 71, 132, 221, 229, 11, 19, 160)}};
static const lean_ctor_object l_main___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__204_value_aux_1),((lean_object*)&l_main___closed__203_value),LEAN_SCALAR_PTR_LITERAL(170, 12, 223, 81, 221, 8, 194, 27)}};
static const lean_object* l_main___closed__204 = (const lean_object*)&l_main___closed__204_value;
static const lean_string_object l_main___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NEQ_UnwrapDomains"};
static const lean_object* l_main___closed__205 = (const lean_object*)&l_main___closed__205_value;
static const lean_string_object l_main___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "err_result_state_effects"};
static const lean_object* l_main___closed__206 = (const lean_object*)&l_main___closed__206_value;
static const lean_ctor_object l_main___closed__207_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__205_value),LEAN_SCALAR_PTR_LITERAL(79, 110, 24, 49, 63, 241, 87, 216)}};
static const lean_ctor_object l_main___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__207_value_aux_0),((lean_object*)&l_main___closed__206_value),LEAN_SCALAR_PTR_LITERAL(18, 47, 168, 6, 35, 63, 153, 153)}};
static const lean_object* l_main___closed__207 = (const lean_object*)&l_main___closed__207_value;
static const lean_string_object l_main___closed__208_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fixed_read_packet"};
static const lean_object* l_main___closed__208 = (const lean_object*)&l_main___closed__208_value;
static const lean_ctor_object l_main___closed__209_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__205_value),LEAN_SCALAR_PTR_LITERAL(79, 110, 24, 49, 63, 241, 87, 216)}};
static const lean_ctor_object l_main___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__209_value_aux_0),((lean_object*)&l_main___closed__208_value),LEAN_SCALAR_PTR_LITERAL(239, 191, 101, 47, 175, 57, 15, 235)}};
static const lean_object* l_main___closed__209 = (const lean_object*)&l_main___closed__209_value;
static const lean_string_object l_main___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ok_result_state_effects"};
static const lean_object* l_main___closed__210 = (const lean_object*)&l_main___closed__210_value;
static const lean_ctor_object l_main___closed__211_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__205_value),LEAN_SCALAR_PTR_LITERAL(79, 110, 24, 49, 63, 241, 87, 216)}};
static const lean_ctor_object l_main___closed__211_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__211_value_aux_0),((lean_object*)&l_main___closed__210_value),LEAN_SCALAR_PTR_LITERAL(103, 232, 56, 127, 38, 130, 133, 136)}};
static const lean_object* l_main___closed__211 = (const lean_object*)&l_main___closed__211_value;
static const lean_array_object l_main___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__204_value),((lean_object*)&l_main___closed__207_value),((lean_object*)&l_main___closed__209_value),((lean_object*)&l_main___closed__211_value)}};
static const lean_object* l_main___closed__212 = (const lean_object*)&l_main___closed__212_value;
static const lean_string_object l_main___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_TraceBack"};
static const lean_object* l_main___closed__213 = (const lean_object*)&l_main___closed__213_value;
static const lean_string_object l_main___closed__214_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eval_bind"};
static const lean_object* l_main___closed__214 = (const lean_object*)&l_main___closed__214_value;
static const lean_ctor_object l_main___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__215_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__215_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__215_value_aux_1),((lean_object*)&l_main___closed__214_value),LEAN_SCALAR_PTR_LITERAL(122, 228, 175, 221, 213, 9, 16, 133)}};
static const lean_object* l_main___closed__215 = (const lean_object*)&l_main___closed__215_value;
static const lean_string_object l_main___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "installed"};
static const lean_object* l_main___closed__216 = (const lean_object*)&l_main___closed__216_value;
static const lean_ctor_object l_main___closed__217_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__217_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__217_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__217_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(106, 200, 194, 224, 10, 226, 64, 45)}};
static const lean_object* l_main___closed__217 = (const lean_object*)&l_main___closed__217_value;
static const lean_string_object l_main___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "model_congr"};
static const lean_object* l_main___closed__218 = (const lean_object*)&l_main___closed__218_value;
static const lean_ctor_object l_main___closed__219_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__219_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__219_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__219_value_aux_1),((lean_object*)&l_main___closed__218_value),LEAN_SCALAR_PTR_LITERAL(203, 249, 62, 153, 186, 69, 85, 220)}};
static const lean_object* l_main___closed__219 = (const lean_object*)&l_main___closed__219_value;
static const lean_ctor_object l_main___closed__220_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__220_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__220_value_aux_0),((lean_object*)&l_main___closed__213_value),LEAN_SCALAR_PTR_LITERAL(235, 254, 97, 156, 207, 155, 175, 203)}};
static const lean_ctor_object l_main___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__220_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(29, 105, 172, 160, 20, 107, 110, 96)}};
static const lean_object* l_main___closed__220 = (const lean_object*)&l_main___closed__220_value;
static const lean_array_object l_main___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__215_value),((lean_object*)&l_main___closed__217_value),((lean_object*)&l_main___closed__219_value),((lean_object*)&l_main___closed__220_value)}};
static const lean_object* l_main___closed__221 = (const lean_object*)&l_main___closed__221_value;
static const lean_string_object l_main___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_ReadCanonical"};
static const lean_object* l_main___closed__222 = (const lean_object*)&l_main___closed__222_value;
static const lean_string_object l_main___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bytes"};
static const lean_object* l_main___closed__223 = (const lean_object*)&l_main___closed__223_value;
static const lean_ctor_object l_main___closed__224_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__224_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_0),((lean_object*)&l_main___closed__222_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__224_value_aux_1),((lean_object*)&l_main___closed__223_value),LEAN_SCALAR_PTR_LITERAL(89, 95, 44, 163, 159, 126, 215, 101)}};
static const lean_object* l_main___closed__224 = (const lean_object*)&l_main___closed__224_value;
static const lean_string_object l_main___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "field"};
static const lean_object* l_main___closed__225 = (const lean_object*)&l_main___closed__225_value;
static const lean_ctor_object l_main___closed__226_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__226_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__226_value_aux_0),((lean_object*)&l_main___closed__222_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__226_value_aux_1),((lean_object*)&l_main___closed__225_value),LEAN_SCALAR_PTR_LITERAL(152, 63, 110, 14, 253, 180, 222, 122)}};
static const lean_object* l_main___closed__226 = (const lean_object*)&l_main___closed__226_value;
static const lean_string_object l_main___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "limbs"};
static const lean_object* l_main___closed__227 = (const lean_object*)&l_main___closed__227_value;
static const lean_ctor_object l_main___closed__228_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__228_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_0),((lean_object*)&l_main___closed__222_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__228_value_aux_1),((lean_object*)&l_main___closed__227_value),LEAN_SCALAR_PTR_LITERAL(38, 146, 191, 16, 0, 63, 126, 115)}};
static const lean_object* l_main___closed__228 = (const lean_object*)&l_main___closed__228_value;
static const lean_string_object l_main___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "read_canonical"};
static const lean_object* l_main___closed__229 = (const lean_object*)&l_main___closed__229_value;
static const lean_ctor_object l_main___closed__230_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__230_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__230_value_aux_0),((lean_object*)&l_main___closed__222_value),LEAN_SCALAR_PTR_LITERAL(163, 161, 0, 26, 199, 253, 126, 5)}};
static const lean_ctor_object l_main___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__230_value_aux_1),((lean_object*)&l_main___closed__229_value),LEAN_SCALAR_PTR_LITERAL(141, 227, 30, 159, 85, 203, 221, 33)}};
static const lean_object* l_main___closed__230 = (const lean_object*)&l_main___closed__230_value;
static const lean_array_object l_main___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__224_value),((lean_object*)&l_main___closed__226_value),((lean_object*)&l_main___closed__228_value),((lean_object*)&l_main___closed__230_value)}};
static const lean_object* l_main___closed__231 = (const lean_object*)&l_main___closed__231_value;
static const lean_string_object l_main___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFS_QueryOps"};
static const lean_object* l_main___closed__232 = (const lean_object*)&l_main___closed__232_value;
static const lean_string_object l_main___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "accumulation"};
static const lean_object* l_main___closed__233 = (const lean_object*)&l_main___closed__233_value;
static const lean_ctor_object l_main___closed__234_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__234_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__234_value_aux_0),((lean_object*)&l_main___closed__232_value),LEAN_SCALAR_PTR_LITERAL(102, 198, 20, 13, 250, 208, 119, 140)}};
static const lean_ctor_object l_main___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__234_value_aux_1),((lean_object*)&l_main___closed__233_value),LEAN_SCALAR_PTR_LITERAL(60, 122, 195, 2, 176, 249, 55, 90)}};
static const lean_object* l_main___closed__234 = (const lean_object*)&l_main___closed__234_value;
static const lean_string_object l_main___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_main___closed__235 = (const lean_object*)&l_main___closed__235_value;
static const lean_ctor_object l_main___closed__236_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__236_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__236_value_aux_0),((lean_object*)&l_main___closed__232_value),LEAN_SCALAR_PTR_LITERAL(102, 198, 20, 13, 250, 208, 119, 140)}};
static const lean_ctor_object l_main___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__236_value_aux_1),((lean_object*)&l_main___closed__235_value),LEAN_SCALAR_PTR_LITERAL(180, 90, 234, 96, 10, 196, 189, 233)}};
static const lean_object* l_main___closed__236 = (const lean_object*)&l_main___closed__236_value;
static const lean_string_object l_main___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NFS_QueryValuesPacket"};
static const lean_object* l_main___closed__237 = (const lean_object*)&l_main___closed__237_value;
static const lean_string_object l_main___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_main___closed__238 = (const lean_object*)&l_main___closed__238_value;
static const lean_ctor_object l_main___closed__239_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__239_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__239_value_aux_0),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(247, 250, 32, 148, 237, 159, 228, 95)}};
static const lean_ctor_object l_main___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__239_value_aux_1),((lean_object*)&l_main___closed__238_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 135, 160, 98, 177, 143, 131)}};
static const lean_object* l_main___closed__239 = (const lean_object*)&l_main___closed__239_value;
static const lean_ctor_object l_main___closed__240_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__240_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__240_value_aux_0),((lean_object*)&l_main___closed__237_value),LEAN_SCALAR_PTR_LITERAL(247, 250, 32, 148, 237, 159, 228, 95)}};
static const lean_ctor_object l_main___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__240_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(25, 8, 178, 77, 87, 107, 39, 49)}};
static const lean_object* l_main___closed__240 = (const lean_object*)&l_main___closed__240_value;
static const lean_array_object l_main___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__234_value),((lean_object*)&l_main___closed__236_value),((lean_object*)&l_main___closed__239_value),((lean_object*)&l_main___closed__240_value)}};
static const lean_object* l_main___closed__241 = (const lean_object*)&l_main___closed__241_value;
static const lean_string_object l_main___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_QueryLoopRoot"};
static const lean_object* l_main___closed__242 = (const lean_object*)&l_main___closed__242_value;
static const lean_string_object l_main___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finite"};
static const lean_object* l_main___closed__243 = (const lean_object*)&l_main___closed__243_value;
static const lean_ctor_object l_main___closed__244_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__244_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_0),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__244_value_aux_1),((lean_object*)&l_main___closed__243_value),LEAN_SCALAR_PTR_LITERAL(80, 60, 137, 67, 228, 235, 218, 32)}};
static const lean_object* l_main___closed__244 = (const lean_object*)&l_main___closed__244_value;
static const lean_string_object l_main___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l_main___closed__245 = (const lean_object*)&l_main___closed__245_value;
static const lean_ctor_object l_main___closed__246_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__246_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__246_value_aux_0),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__246_value_aux_1),((lean_object*)&l_main___closed__245_value),LEAN_SCALAR_PTR_LITERAL(129, 74, 21, 149, 61, 8, 167, 72)}};
static const lean_object* l_main___closed__246 = (const lean_object*)&l_main___closed__246_value;
static const lean_string_object l_main___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tx1"};
static const lean_object* l_main___closed__247 = (const lean_object*)&l_main___closed__247_value;
static const lean_ctor_object l_main___closed__248_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__248_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__248_value_aux_0),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__248_value_aux_1),((lean_object*)&l_main___closed__247_value),LEAN_SCALAR_PTR_LITERAL(97, 16, 233, 56, 121, 162, 34, 112)}};
static const lean_object* l_main___closed__248 = (const lean_object*)&l_main___closed__248_value;
static const lean_string_object l_main___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tx2"};
static const lean_object* l_main___closed__249 = (const lean_object*)&l_main___closed__249_value;
static const lean_ctor_object l_main___closed__250_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__250_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__250_value_aux_0),((lean_object*)&l_main___closed__242_value),LEAN_SCALAR_PTR_LITERAL(120, 89, 26, 111, 23, 156, 249, 116)}};
static const lean_ctor_object l_main___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__250_value_aux_1),((lean_object*)&l_main___closed__249_value),LEAN_SCALAR_PTR_LITERAL(4, 179, 97, 82, 34, 4, 43, 67)}};
static const lean_object* l_main___closed__250 = (const lean_object*)&l_main___closed__250_value;
static const lean_array_object l_main___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__244_value),((lean_object*)&l_main___closed__246_value),((lean_object*)&l_main___closed__248_value),((lean_object*)&l_main___closed__250_value)}};
static const lean_object* l_main___closed__251 = (const lean_object*)&l_main___closed__251_value;
static const lean_string_object l_main___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_QueryBack"};
static const lean_object* l_main___closed__252 = (const lean_object*)&l_main___closed__252_value;
static const lean_ctor_object l_main___closed__253_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__253_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__253_value_aux_0),((lean_object*)&l_main___closed__252_value),LEAN_SCALAR_PTR_LITERAL(186, 135, 93, 118, 73, 139, 105, 68)}};
static const lean_ctor_object l_main___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__253_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(15, 51, 151, 113, 201, 174, 217, 81)}};
static const lean_object* l_main___closed__253 = (const lean_object*)&l_main___closed__253_value;
static const lean_string_object l_main___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFS_QueryInvariant"};
static const lean_object* l_main___closed__254 = (const lean_object*)&l_main___closed__254_value;
static const lean_string_object l_main___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "active"};
static const lean_object* l_main___closed__255 = (const lean_object*)&l_main___closed__255_value;
static const lean_ctor_object l_main___closed__256_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__256_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__256_value_aux_0),((lean_object*)&l_main___closed__254_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__256_value_aux_1),((lean_object*)&l_main___closed__255_value),LEAN_SCALAR_PTR_LITERAL(230, 205, 73, 150, 123, 187, 99, 151)}};
static const lean_object* l_main___closed__256 = (const lean_object*)&l_main___closed__256_value;
static const lean_string_object l_main___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "form"};
static const lean_object* l_main___closed__257 = (const lean_object*)&l_main___closed__257_value;
static const lean_ctor_object l_main___closed__258_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__258_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__258_value_aux_0),((lean_object*)&l_main___closed__254_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__258_value_aux_1),((lean_object*)&l_main___closed__257_value),LEAN_SCALAR_PTR_LITERAL(211, 122, 96, 177, 138, 34, 8, 171)}};
static const lean_object* l_main___closed__258 = (const lean_object*)&l_main___closed__258_value;
static const lean_ctor_object l_main___closed__259_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__259_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_0),((lean_object*)&l_main___closed__254_value),LEAN_SCALAR_PTR_LITERAL(216, 166, 85, 251, 152, 107, 141, 204)}};
static const lean_ctor_object l_main___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__259_value_aux_1),((lean_object*)&l_main___closed__171_value),LEAN_SCALAR_PTR_LITERAL(96, 172, 209, 234, 213, 248, 166, 12)}};
static const lean_object* l_main___closed__259 = (const lean_object*)&l_main___closed__259_value;
static const lean_array_object l_main___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__253_value),((lean_object*)&l_main___closed__256_value),((lean_object*)&l_main___closed__258_value),((lean_object*)&l_main___closed__259_value)}};
static const lean_object* l_main___closed__260 = (const lean_object*)&l_main___closed__260_value;
static const lean_string_object l_main___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFS_PacketRoot"};
static const lean_object* l_main___closed__261 = (const lean_object*)&l_main___closed__261_value;
static const lean_string_object l_main___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "geometry"};
static const lean_object* l_main___closed__262 = (const lean_object*)&l_main___closed__262_value;
static const lean_ctor_object l_main___closed__263_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__263_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_0),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__263_value_aux_1),((lean_object*)&l_main___closed__262_value),LEAN_SCALAR_PTR_LITERAL(251, 42, 19, 196, 180, 170, 191, 231)}};
static const lean_object* l_main___closed__263 = (const lean_object*)&l_main___closed__263_value;
static const lean_ctor_object l_main___closed__264_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__264_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__264_value_aux_0),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__264_value_aux_1),((lean_object*)&l_main___closed__184_value),LEAN_SCALAR_PTR_LITERAL(141, 132, 113, 147, 92, 201, 135, 255)}};
static const lean_object* l_main___closed__264 = (const lean_object*)&l_main___closed__264_value;
static const lean_string_object l_main___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_main___closed__265 = (const lean_object*)&l_main___closed__265_value;
static const lean_ctor_object l_main___closed__266_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__266_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__266_value_aux_0),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__266_value_aux_1),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(158, 14, 237, 102, 203, 93, 125, 53)}};
static const lean_object* l_main___closed__266 = (const lean_object*)&l_main___closed__266_value;
static const lean_string_object l_main___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "query"};
static const lean_object* l_main___closed__267 = (const lean_object*)&l_main___closed__267_value;
static const lean_ctor_object l_main___closed__268_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__268_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__268_value_aux_0),((lean_object*)&l_main___closed__261_value),LEAN_SCALAR_PTR_LITERAL(61, 35, 194, 84, 193, 75, 82, 39)}};
static const lean_ctor_object l_main___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__268_value_aux_1),((lean_object*)&l_main___closed__267_value),LEAN_SCALAR_PTR_LITERAL(178, 72, 196, 43, 173, 72, 86, 148)}};
static const lean_object* l_main___closed__268 = (const lean_object*)&l_main___closed__268_value;
static const lean_array_object l_main___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__263_value),((lean_object*)&l_main___closed__264_value),((lean_object*)&l_main___closed__266_value),((lean_object*)&l_main___closed__268_value)}};
static const lean_object* l_main___closed__269 = (const lean_object*)&l_main___closed__269_value;
static const lean_string_object l_main___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFS_LoopTrace"};
static const lean_object* l_main___closed__270 = (const lean_object*)&l_main___closed__270_value;
static const lean_ctor_object l_main___closed__271_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__271_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__271_value_aux_0),((lean_object*)&l_main___closed__270_value),LEAN_SCALAR_PTR_LITERAL(101, 42, 121, 192, 38, 118, 224, 12)}};
static const lean_ctor_object l_main___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__271_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(115, 156, 93, 121, 123, 14, 171, 242)}};
static const lean_object* l_main___closed__271 = (const lean_object*)&l_main___closed__271_value;
static const lean_string_object l_main___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_LoopTraceDefs"};
static const lean_object* l_main___closed__272 = (const lean_object*)&l_main___closed__272_value;
static const lean_string_object l_main___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bind_congr"};
static const lean_object* l_main___closed__273 = (const lean_object*)&l_main___closed__273_value;
static const lean_ctor_object l_main___closed__274_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__274_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__274_value_aux_0),((lean_object*)&l_main___closed__272_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__274_value_aux_1),((lean_object*)&l_main___closed__273_value),LEAN_SCALAR_PTR_LITERAL(5, 191, 87, 227, 85, 209, 236, 108)}};
static const lean_object* l_main___closed__274 = (const lean_object*)&l_main___closed__274_value;
static const lean_string_object l_main___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_main___closed__275 = (const lean_object*)&l_main___closed__275_value;
static const lean_ctor_object l_main___closed__276_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__276_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__276_value_aux_0),((lean_object*)&l_main___closed__272_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__276_value_aux_1),((lean_object*)&l_main___closed__275_value),LEAN_SCALAR_PTR_LITERAL(169, 234, 208, 78, 95, 236, 196, 236)}};
static const lean_object* l_main___closed__276 = (const lean_object*)&l_main___closed__276_value;
static const lean_string_object l_main___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "erased"};
static const lean_object* l_main___closed__277 = (const lean_object*)&l_main___closed__277_value;
static const lean_ctor_object l_main___closed__278_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__278_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_0),((lean_object*)&l_main___closed__272_value),LEAN_SCALAR_PTR_LITERAL(7, 131, 80, 130, 108, 136, 51, 156)}};
static const lean_ctor_object l_main___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__278_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(17, 195, 30, 85, 240, 70, 48, 233)}};
static const lean_object* l_main___closed__278 = (const lean_object*)&l_main___closed__278_value;
static const lean_array_object l_main___closed__279_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__271_value),((lean_object*)&l_main___closed__274_value),((lean_object*)&l_main___closed__276_value),((lean_object*)&l_main___closed__278_value)}};
static const lean_object* l_main___closed__279 = (const lean_object*)&l_main___closed__279_value;
static const lean_string_object l_main___closed__280_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFS_FoldInstall"};
static const lean_object* l_main___closed__280 = (const lean_object*)&l_main___closed__280_value;
static const lean_ctor_object l_main___closed__281_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__281_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__281_value_aux_0),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__281_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__281_value_aux_1),((lean_object*)&l_main___closed__235_value),LEAN_SCALAR_PTR_LITERAL(136, 240, 145, 127, 138, 114, 215, 62)}};
static const lean_object* l_main___closed__281 = (const lean_object*)&l_main___closed__281_value;
static const lean_string_object l_main___closed__282_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "map_map"};
static const lean_object* l_main___closed__282 = (const lean_object*)&l_main___closed__282_value;
static const lean_ctor_object l_main___closed__283_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__283_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__283_value_aux_0),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__283_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__283_value_aux_1),((lean_object*)&l_main___closed__282_value),LEAN_SCALAR_PTR_LITERAL(106, 82, 149, 195, 128, 208, 229, 242)}};
static const lean_object* l_main___closed__283 = (const lean_object*)&l_main___closed__283_value;
static const lean_string_object l_main___closed__284_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "rows"};
static const lean_object* l_main___closed__284 = (const lean_object*)&l_main___closed__284_value;
static const lean_ctor_object l_main___closed__285_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__285_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__285_value_aux_0),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__285_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__285_value_aux_1),((lean_object*)&l_main___closed__284_value),LEAN_SCALAR_PTR_LITERAL(131, 37, 110, 78, 11, 107, 144, 121)}};
static const lean_object* l_main___closed__285 = (const lean_object*)&l_main___closed__285_value;
static const lean_string_object l_main___closed__286_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "erase_fixed"};
static const lean_object* l_main___closed__286 = (const lean_object*)&l_main___closed__286_value;
static const lean_ctor_object l_main___closed__287_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__287_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__287_value_aux_0),((lean_object*)&l_main___closed__270_value),LEAN_SCALAR_PTR_LITERAL(101, 42, 121, 192, 38, 118, 224, 12)}};
static const lean_ctor_object l_main___closed__287_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__287_value_aux_1),((lean_object*)&l_main___closed__286_value),LEAN_SCALAR_PTR_LITERAL(181, 107, 11, 202, 159, 42, 150, 134)}};
static const lean_object* l_main___closed__287 = (const lean_object*)&l_main___closed__287_value;
static const lean_array_object l_main___closed__288_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__281_value),((lean_object*)&l_main___closed__283_value),((lean_object*)&l_main___closed__285_value),((lean_object*)&l_main___closed__287_value)}};
static const lean_object* l_main___closed__288 = (const lean_object*)&l_main___closed__288_value;
static const lean_string_object l_main___closed__289_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFS_CallerDomains"};
static const lean_object* l_main___closed__289 = (const lean_object*)&l_main___closed__289_value;
static const lean_string_object l_main___closed__290_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "no_seed"};
static const lean_object* l_main___closed__290 = (const lean_object*)&l_main___closed__290_value;
static const lean_ctor_object l_main___closed__291_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__291_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__291_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__291_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__291_value_aux_1),((lean_object*)&l_main___closed__290_value),LEAN_SCALAR_PTR_LITERAL(224, 255, 155, 13, 54, 4, 141, 127)}};
static const lean_object* l_main___closed__291 = (const lean_object*)&l_main___closed__291_value;
static const lean_string_object l_main___closed__292_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFS_DotTrace"};
static const lean_object* l_main___closed__292 = (const lean_object*)&l_main___closed__292_value;
static const lean_string_object l_main___closed__293_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l_main___closed__293 = (const lean_object*)&l_main___closed__293_value;
static const lean_ctor_object l_main___closed__294_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__294_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__294_value_aux_0),((lean_object*)&l_main___closed__292_value),LEAN_SCALAR_PTR_LITERAL(17, 29, 204, 0, 187, 63, 52, 210)}};
static const lean_ctor_object l_main___closed__294_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__294_value_aux_1),((lean_object*)&l_main___closed__293_value),LEAN_SCALAR_PTR_LITERAL(117, 223, 73, 201, 180, 97, 17, 191)}};
static const lean_object* l_main___closed__294 = (const lean_object*)&l_main___closed__294_value;
static const lean_string_object l_main___closed__295_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "circle"};
static const lean_object* l_main___closed__295 = (const lean_object*)&l_main___closed__295_value;
static const lean_ctor_object l_main___closed__296_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__296_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__296_value_aux_0),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__296_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__296_value_aux_1),((lean_object*)&l_main___closed__295_value),LEAN_SCALAR_PTR_LITERAL(97, 30, 198, 122, 173, 41, 15, 28)}};
static const lean_object* l_main___closed__296 = (const lean_object*)&l_main___closed__296_value;
static const lean_string_object l_main___closed__297_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "domains"};
static const lean_object* l_main___closed__297 = (const lean_object*)&l_main___closed__297_value;
static const lean_ctor_object l_main___closed__298_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__298_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__298_value_aux_0),((lean_object*)&l_main___closed__280_value),LEAN_SCALAR_PTR_LITERAL(234, 144, 91, 234, 157, 251, 204, 86)}};
static const lean_ctor_object l_main___closed__298_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__298_value_aux_1),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(184, 79, 219, 149, 95, 90, 67, 223)}};
static const lean_object* l_main___closed__298 = (const lean_object*)&l_main___closed__298_value;
static const lean_array_object l_main___closed__299_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__291_value),((lean_object*)&l_main___closed__294_value),((lean_object*)&l_main___closed__296_value),((lean_object*)&l_main___closed__298_value)}};
static const lean_object* l_main___closed__299 = (const lean_object*)&l_main___closed__299_value;
static const lean_string_object l_main___closed__300_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dots"};
static const lean_object* l_main___closed__300 = (const lean_object*)&l_main___closed__300_value;
static const lean_ctor_object l_main___closed__301_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__301_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__301_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__301_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__301_value_aux_1),((lean_object*)&l_main___closed__300_value),LEAN_SCALAR_PTR_LITERAL(205, 219, 48, 229, 27, 236, 61, 253)}};
static const lean_object* l_main___closed__301 = (const lean_object*)&l_main___closed__301_value;
static const lean_string_object l_main___closed__302_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fields"};
static const lean_object* l_main___closed__302 = (const lean_object*)&l_main___closed__302_value;
static const lean_ctor_object l_main___closed__303_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__303_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__303_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__303_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__303_value_aux_1),((lean_object*)&l_main___closed__302_value),LEAN_SCALAR_PTR_LITERAL(106, 66, 153, 72, 176, 209, 0, 124)}};
static const lean_object* l_main___closed__303 = (const lean_object*)&l_main___closed__303_value;
static const lean_string_object l_main___closed__304_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "folds"};
static const lean_object* l_main___closed__304 = (const lean_object*)&l_main___closed__304_value;
static const lean_ctor_object l_main___closed__305_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__305_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__305_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__305_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__305_value_aux_1),((lean_object*)&l_main___closed__304_value),LEAN_SCALAR_PTR_LITERAL(121, 169, 113, 215, 237, 144, 115, 89)}};
static const lean_object* l_main___closed__305 = (const lean_object*)&l_main___closed__305_value;
static const lean_string_object l_main___closed__306_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "loop_property"};
static const lean_object* l_main___closed__306 = (const lean_object*)&l_main___closed__306_value;
static const lean_ctor_object l_main___closed__307_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__307_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__307_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__307_value_aux_1),((lean_object*)&l_main___closed__306_value),LEAN_SCALAR_PTR_LITERAL(88, 57, 108, 119, 140, 136, 28, 30)}};
static const lean_object* l_main___closed__307 = (const lean_object*)&l_main___closed__307_value;
static const lean_array_object l_main___closed__308_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__301_value),((lean_object*)&l_main___closed__303_value),((lean_object*)&l_main___closed__305_value),((lean_object*)&l_main___closed__307_value)}};
static const lean_object* l_main___closed__308 = (const lean_object*)&l_main___closed__308_value;
static const lean_string_object l_main___closed__309_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFS_AccumDomain"};
static const lean_object* l_main___closed__309 = (const lean_object*)&l_main___closed__309_value;
static const lean_string_object l_main___closed__310_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "domain"};
static const lean_object* l_main___closed__310 = (const lean_object*)&l_main___closed__310_value;
static const lean_ctor_object l_main___closed__311_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__311_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__311_value_aux_0),((lean_object*)&l_main___closed__309_value),LEAN_SCALAR_PTR_LITERAL(43, 36, 186, 92, 53, 224, 23, 154)}};
static const lean_ctor_object l_main___closed__311_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__311_value_aux_1),((lean_object*)&l_main___closed__310_value),LEAN_SCALAR_PTR_LITERAL(26, 11, 133, 116, 22, 88, 154, 255)}};
static const lean_object* l_main___closed__311 = (const lean_object*)&l_main___closed__311_value;
static const lean_ctor_object l_main___closed__312_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__312_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__312_value_aux_0),((lean_object*)&l_main___closed__309_value),LEAN_SCALAR_PTR_LITERAL(43, 36, 186, 92, 53, 224, 23, 154)}};
static const lean_ctor_object l_main___closed__312_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__312_value_aux_1),((lean_object*)&l_main___closed__235_value),LEAN_SCALAR_PTR_LITERAL(93, 187, 209, 163, 181, 20, 108, 91)}};
static const lean_object* l_main___closed__312 = (const lean_object*)&l_main___closed__312_value;
static const lean_string_object l_main___closed__313_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFS_AccumInstall"};
static const lean_object* l_main___closed__313 = (const lean_object*)&l_main___closed__313_value;
static const lean_ctor_object l_main___closed__314_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__314_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__314_value_aux_0),((lean_object*)&l_main___closed__313_value),LEAN_SCALAR_PTR_LITERAL(198, 195, 235, 195, 29, 24, 238, 158)}};
static const lean_ctor_object l_main___closed__314_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__314_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(155, 184, 204, 22, 19, 124, 109, 247)}};
static const lean_object* l_main___closed__314 = (const lean_object*)&l_main___closed__314_value;
static const lean_string_object l_main___closed__315_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "array_property"};
static const lean_object* l_main___closed__315 = (const lean_object*)&l_main___closed__315_value;
static const lean_ctor_object l_main___closed__316_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__316_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__316_value_aux_0),((lean_object*)&l_main___closed__289_value),LEAN_SCALAR_PTR_LITERAL(171, 236, 212, 219, 154, 150, 126, 16)}};
static const lean_ctor_object l_main___closed__316_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__316_value_aux_1),((lean_object*)&l_main___closed__315_value),LEAN_SCALAR_PTR_LITERAL(101, 136, 184, 95, 1, 228, 235, 150)}};
static const lean_object* l_main___closed__316 = (const lean_object*)&l_main___closed__316_value;
static const lean_array_object l_main___closed__317_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__311_value),((lean_object*)&l_main___closed__312_value),((lean_object*)&l_main___closed__314_value),((lean_object*)&l_main___closed__316_value)}};
static const lean_object* l_main___closed__317 = (const lean_object*)&l_main___closed__317_value;
static const lean_string_object l_main___closed__318_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_TraceBack"};
static const lean_object* l_main___closed__318 = (const lean_object*)&l_main___closed__318_value;
static const lean_ctor_object l_main___closed__319_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__319_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_0),((lean_object*)&l_main___closed__318_value),LEAN_SCALAR_PTR_LITERAL(228, 208, 177, 232, 3, 41, 145, 13)}};
static const lean_ctor_object l_main___closed__319_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__319_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(6, 201, 57, 224, 163, 102, 168, 215)}};
static const lean_object* l_main___closed__319 = (const lean_object*)&l_main___closed__319_value;
static const lean_string_object l_main___closed__320_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_TraceFront"};
static const lean_object* l_main___closed__320 = (const lean_object*)&l_main___closed__320_value;
static const lean_ctor_object l_main___closed__321_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__321_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_0),((lean_object*)&l_main___closed__320_value),LEAN_SCALAR_PTR_LITERAL(228, 60, 113, 141, 82, 197, 154, 61)}};
static const lean_ctor_object l_main___closed__321_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__321_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(6, 109, 36, 76, 116, 231, 56, 91)}};
static const lean_object* l_main___closed__321 = (const lean_object*)&l_main___closed__321_value;
static const lean_string_object l_main___closed__322_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_TraceHead"};
static const lean_object* l_main___closed__322 = (const lean_object*)&l_main___closed__322_value;
static const lean_ctor_object l_main___closed__323_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__323_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__323_value_aux_0),((lean_object*)&l_main___closed__322_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 13, 36, 107, 160, 118, 25)}};
static const lean_ctor_object l_main___closed__323_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__323_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(111, 172, 169, 230, 75, 204, 193, 246)}};
static const lean_object* l_main___closed__323 = (const lean_object*)&l_main___closed__323_value;
static const lean_string_object l_main___closed__324_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_TraceTypes"};
static const lean_object* l_main___closed__324 = (const lean_object*)&l_main___closed__324_value;
static const lean_string_object l_main___closed__325_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pure_result"};
static const lean_object* l_main___closed__325 = (const lean_object*)&l_main___closed__325_value;
static const lean_ctor_object l_main___closed__326_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__326_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__326_value_aux_0),((lean_object*)&l_main___closed__324_value),LEAN_SCALAR_PTR_LITERAL(131, 69, 159, 108, 193, 225, 136, 106)}};
static const lean_ctor_object l_main___closed__326_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__326_value_aux_1),((lean_object*)&l_main___closed__325_value),LEAN_SCALAR_PTR_LITERAL(36, 152, 130, 186, 254, 125, 235, 214)}};
static const lean_object* l_main___closed__326 = (const lean_object*)&l_main___closed__326_value;
static const lean_array_object l_main___closed__327_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__319_value),((lean_object*)&l_main___closed__321_value),((lean_object*)&l_main___closed__323_value),((lean_object*)&l_main___closed__326_value)}};
static const lean_object* l_main___closed__327 = (const lean_object*)&l_main___closed__327_value;
static const lean_string_object l_main___closed__328_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFP_Resume"};
static const lean_object* l_main___closed__328 = (const lean_object*)&l_main___closed__328_value;
static const lean_ctor_object l_main___closed__329_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__329_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__329_value_aux_0),((lean_object*)&l_main___closed__328_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 155, 253, 196, 128, 147, 219)}};
static const lean_ctor_object l_main___closed__329_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__329_value_aux_1),((lean_object*)&l_main___closed__249_value),LEAN_SCALAR_PTR_LITERAL(164, 212, 12, 61, 21, 155, 255, 214)}};
static const lean_object* l_main___closed__329 = (const lean_object*)&l_main___closed__329_value;
static const lean_string_object l_main___closed__330_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_ReturnCuts"};
static const lean_object* l_main___closed__330 = (const lean_object*)&l_main___closed__330_value;
static const lean_string_object l_main___closed__331_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "continuation"};
static const lean_object* l_main___closed__331 = (const lean_object*)&l_main___closed__331_value;
static const lean_ctor_object l_main___closed__332_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__332_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__332_value_aux_0),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(101, 95, 58, 219, 88, 245, 49, 54)}};
static const lean_ctor_object l_main___closed__332_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__332_value_aux_1),((lean_object*)&l_main___closed__331_value),LEAN_SCALAR_PTR_LITERAL(164, 56, 190, 19, 92, 227, 64, 20)}};
static const lean_object* l_main___closed__332 = (const lean_object*)&l_main___closed__332_value;
static const lean_ctor_object l_main___closed__333_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__333_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__333_value_aux_0),((lean_object*)&l_main___closed__330_value),LEAN_SCALAR_PTR_LITERAL(101, 95, 58, 219, 88, 245, 49, 54)}};
static const lean_ctor_object l_main___closed__333_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__333_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(27, 66, 29, 186, 36, 232, 197, 61)}};
static const lean_object* l_main___closed__333 = (const lean_object*)&l_main___closed__333_value;
static const lean_string_object l_main___closed__334_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_SuffixCuts"};
static const lean_object* l_main___closed__334 = (const lean_object*)&l_main___closed__334_value;
static const lean_ctor_object l_main___closed__335_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__335_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__335_value_aux_0),((lean_object*)&l_main___closed__334_value),LEAN_SCALAR_PTR_LITERAL(65, 23, 102, 118, 189, 152, 124, 107)}};
static const lean_ctor_object l_main___closed__335_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__335_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(127, 234, 223, 104, 109, 168, 128, 242)}};
static const lean_object* l_main___closed__335 = (const lean_object*)&l_main___closed__335_value;
static const lean_array_object l_main___closed__336_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__329_value),((lean_object*)&l_main___closed__332_value),((lean_object*)&l_main___closed__333_value),((lean_object*)&l_main___closed__335_value)}};
static const lean_object* l_main___closed__336 = (const lean_object*)&l_main___closed__336_value;
static const lean_string_object l_main___closed__337_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_QueryTrace"};
static const lean_object* l_main___closed__337 = (const lean_object*)&l_main___closed__337_value;
static const lean_ctor_object l_main___closed__338_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__338_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__338_value_aux_0),((lean_object*)&l_main___closed__337_value),LEAN_SCALAR_PTR_LITERAL(108, 15, 4, 107, 176, 191, 20, 201)}};
static const lean_ctor_object l_main___closed__338_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__338_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(222, 123, 151, 176, 80, 200, 161, 235)}};
static const lean_object* l_main___closed__338 = (const lean_object*)&l_main___closed__338_value;
static const lean_string_object l_main___closed__339_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFP_RejectionTrace"};
static const lean_object* l_main___closed__339 = (const lean_object*)&l_main___closed__339_value;
static const lean_string_object l_main___closed__340_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "guard"};
static const lean_object* l_main___closed__340 = (const lean_object*)&l_main___closed__340_value;
static const lean_ctor_object l_main___closed__341_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__341_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__341_value_aux_0),((lean_object*)&l_main___closed__339_value),LEAN_SCALAR_PTR_LITERAL(218, 18, 186, 94, 233, 180, 60, 161)}};
static const lean_ctor_object l_main___closed__341_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__341_value_aux_1),((lean_object*)&l_main___closed__340_value),LEAN_SCALAR_PTR_LITERAL(190, 249, 137, 76, 151, 14, 71, 208)}};
static const lean_object* l_main___closed__341 = (const lean_object*)&l_main___closed__341_value;
static const lean_string_object l_main___closed__342_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "rejected_prefix"};
static const lean_object* l_main___closed__342 = (const lean_object*)&l_main___closed__342_value;
static const lean_ctor_object l_main___closed__343_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__343_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__343_value_aux_0),((lean_object*)&l_main___closed__339_value),LEAN_SCALAR_PTR_LITERAL(218, 18, 186, 94, 233, 180, 60, 161)}};
static const lean_ctor_object l_main___closed__343_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__343_value_aux_1),((lean_object*)&l_main___closed__342_value),LEAN_SCALAR_PTR_LITERAL(73, 159, 29, 119, 29, 229, 38, 90)}};
static const lean_object* l_main___closed__343 = (const lean_object*)&l_main___closed__343_value;
static const lean_ctor_object l_main___closed__344_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__344_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__344_value_aux_0),((lean_object*)&l_main___closed__328_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 155, 253, 196, 128, 147, 219)}};
static const lean_ctor_object l_main___closed__344_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__344_value_aux_1),((lean_object*)&l_main___closed__247_value),LEAN_SCALAR_PTR_LITERAL(193, 89, 191, 135, 34, 89, 82, 193)}};
static const lean_object* l_main___closed__344 = (const lean_object*)&l_main___closed__344_value;
static const lean_array_object l_main___closed__345_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__338_value),((lean_object*)&l_main___closed__341_value),((lean_object*)&l_main___closed__343_value),((lean_object*)&l_main___closed__344_value)}};
static const lean_object* l_main___closed__345 = (const lean_object*)&l_main___closed__345_value;
static const lean_string_object l_main___closed__346_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_ProductLaw"};
static const lean_object* l_main___closed__346 = (const lean_object*)&l_main___closed__346_value;
static const lean_ctor_object l_main___closed__347_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__347_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__347_value_aux_0),((lean_object*)&l_main___closed__346_value),LEAN_SCALAR_PTR_LITERAL(82, 99, 204, 19, 159, 121, 29, 12)}};
static const lean_ctor_object l_main___closed__347_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__347_value_aux_1),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(253, 61, 135, 74, 12, 214, 122, 116)}};
static const lean_object* l_main___closed__347 = (const lean_object*)&l_main___closed__347_value;
static const lean_string_object l_main___closed__348_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFP_QueryAdvance"};
static const lean_object* l_main___closed__348 = (const lean_object*)&l_main___closed__348_value;
static const lean_string_object l_main___closed__349_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "accepted"};
static const lean_object* l_main___closed__349 = (const lean_object*)&l_main___closed__349_value;
static const lean_ctor_object l_main___closed__350_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__350_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__350_value_aux_0),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(252, 24, 77, 116, 29, 133, 154, 64)}};
static const lean_ctor_object l_main___closed__350_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__350_value_aux_1),((lean_object*)&l_main___closed__349_value),LEAN_SCALAR_PTR_LITERAL(244, 82, 166, 211, 18, 187, 196, 181)}};
static const lean_object* l_main___closed__350 = (const lean_object*)&l_main___closed__350_value;
static const lean_string_object l_main___closed__351_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_main___closed__351 = (const lean_object*)&l_main___closed__351_value;
static const lean_ctor_object l_main___closed__352_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__352_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_0),((lean_object*)&l_main___closed__348_value),LEAN_SCALAR_PTR_LITERAL(252, 24, 77, 116, 29, 133, 154, 64)}};
static const lean_ctor_object l_main___closed__352_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__352_value_aux_1),((lean_object*)&l_main___closed__351_value),LEAN_SCALAR_PTR_LITERAL(234, 88, 84, 215, 168, 32, 254, 33)}};
static const lean_object* l_main___closed__352 = (const lean_object*)&l_main___closed__352_value;
static const lean_string_object l_main___closed__353_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_QueryCuts"};
static const lean_object* l_main___closed__353 = (const lean_object*)&l_main___closed__353_value;
static const lean_ctor_object l_main___closed__354_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__354_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__354_value_aux_0),((lean_object*)&l_main___closed__353_value),LEAN_SCALAR_PTR_LITERAL(186, 77, 88, 39, 124, 223, 121, 161)}};
static const lean_ctor_object l_main___closed__354_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__354_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(152, 36, 48, 173, 235, 7, 28, 79)}};
static const lean_object* l_main___closed__354 = (const lean_object*)&l_main___closed__354_value;
static const lean_array_object l_main___closed__355_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__347_value),((lean_object*)&l_main___closed__350_value),((lean_object*)&l_main___closed__352_value),((lean_object*)&l_main___closed__354_value)}};
static const lean_object* l_main___closed__355 = (const lean_object*)&l_main___closed__355_value;
static const lean_string_object l_main___closed__356_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFP_ObserverErasure"};
static const lean_object* l_main___closed__356 = (const lean_object*)&l_main___closed__356_value;
static const lean_ctor_object l_main___closed__357_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__357_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__357_value_aux_0),((lean_object*)&l_main___closed__356_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__357_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__357_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 21, 20, 52, 233, 15, 11, 167)}};
static const lean_object* l_main___closed__357 = (const lean_object*)&l_main___closed__357_value;
static const lean_ctor_object l_main___closed__358_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__358_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__358_value_aux_0),((lean_object*)&l_main___closed__356_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__358_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__358_value_aux_1),((lean_object*)&l_main___closed__267_value),LEAN_SCALAR_PTR_LITERAL(99, 92, 185, 58, 113, 121, 218, 190)}};
static const lean_object* l_main___closed__358 = (const lean_object*)&l_main___closed__358_value;
static const lean_string_object l_main___closed__359_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_main___closed__359 = (const lean_object*)&l_main___closed__359_value;
static const lean_ctor_object l_main___closed__360_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__360_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__360_value_aux_0),((lean_object*)&l_main___closed__356_value),LEAN_SCALAR_PTR_LITERAL(64, 206, 196, 31, 21, 70, 147, 182)}};
static const lean_ctor_object l_main___closed__360_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__360_value_aux_1),((lean_object*)&l_main___closed__359_value),LEAN_SCALAR_PTR_LITERAL(235, 153, 248, 117, 174, 251, 56, 187)}};
static const lean_object* l_main___closed__360 = (const lean_object*)&l_main___closed__360_value;
static const lean_string_object l_main___closed__361_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "emitted"};
static const lean_object* l_main___closed__361 = (const lean_object*)&l_main___closed__361_value;
static const lean_ctor_object l_main___closed__362_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__362_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__362_value_aux_0),((lean_object*)&l_main___closed__346_value),LEAN_SCALAR_PTR_LITERAL(82, 99, 204, 19, 159, 121, 29, 12)}};
static const lean_ctor_object l_main___closed__362_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__362_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(147, 167, 163, 146, 188, 84, 216, 226)}};
static const lean_object* l_main___closed__362 = (const lean_object*)&l_main___closed__362_value;
static const lean_array_object l_main___closed__363_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__357_value),((lean_object*)&l_main___closed__358_value),((lean_object*)&l_main___closed__360_value),((lean_object*)&l_main___closed__362_value)}};
static const lean_object* l_main___closed__363 = (const lean_object*)&l_main___closed__363_value;
static const lean_string_object l_main___closed__364_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFP_NodeDictionary"};
static const lean_object* l_main___closed__364 = (const lean_object*)&l_main___closed__364_value;
static const lean_string_object l_main___closed__365_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_main___closed__365 = (const lean_object*)&l_main___closed__365_value;
static const lean_ctor_object l_main___closed__366_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__366_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__366_value_aux_0),((lean_object*)&l_main___closed__364_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__366_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__366_value_aux_1),((lean_object*)&l_main___closed__365_value),LEAN_SCALAR_PTR_LITERAL(238, 169, 201, 8, 87, 117, 100, 21)}};
static const lean_object* l_main___closed__366 = (const lean_object*)&l_main___closed__366_value;
static const lean_ctor_object l_main___closed__367_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__367_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__367_value_aux_0),((lean_object*)&l_main___closed__364_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__367_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__367_value_aux_1),((lean_object*)&l_main___closed__265_value),LEAN_SCALAR_PTR_LITERAL(108, 195, 202, 172, 5, 134, 119, 176)}};
static const lean_object* l_main___closed__367 = (const lean_object*)&l_main___closed__367_value;
static const lean_string_object l_main___closed__368_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "product"};
static const lean_object* l_main___closed__368 = (const lean_object*)&l_main___closed__368_value;
static const lean_ctor_object l_main___closed__369_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__369_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__369_value_aux_0),((lean_object*)&l_main___closed__364_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__369_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__369_value_aux_1),((lean_object*)&l_main___closed__368_value),LEAN_SCALAR_PTR_LITERAL(201, 162, 245, 140, 25, 206, 167, 18)}};
static const lean_object* l_main___closed__369 = (const lean_object*)&l_main___closed__369_value;
static const lean_string_object l_main___closed__370_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_main___closed__370 = (const lean_object*)&l_main___closed__370_value;
static const lean_ctor_object l_main___closed__371_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__371_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__371_value_aux_0),((lean_object*)&l_main___closed__364_value),LEAN_SCALAR_PTR_LITERAL(39, 201, 242, 74, 60, 0, 61, 59)}};
static const lean_ctor_object l_main___closed__371_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__371_value_aux_1),((lean_object*)&l_main___closed__370_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 31, 192, 139, 25, 153, 132)}};
static const lean_object* l_main___closed__371 = (const lean_object*)&l_main___closed__371_value;
static const lean_array_object l_main___closed__372_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__366_value),((lean_object*)&l_main___closed__367_value),((lean_object*)&l_main___closed__369_value),((lean_object*)&l_main___closed__371_value)}};
static const lean_object* l_main___closed__372 = (const lean_object*)&l_main___closed__372_value;
static const lean_string_object l_main___closed__373_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFP_LoopTransport"};
static const lean_object* l_main___closed__373 = (const lean_object*)&l_main___closed__373_value;
static const lean_ctor_object l_main___closed__374_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__374_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__374_value_aux_0),((lean_object*)&l_main___closed__373_value),LEAN_SCALAR_PTR_LITERAL(39, 227, 16, 37, 232, 157, 112, 26)}};
static const lean_ctor_object l_main___closed__374_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__374_value_aux_1),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(200, 42, 120, 75, 52, 0, 78, 174)}};
static const lean_object* l_main___closed__374 = (const lean_object*)&l_main___closed__374_value;
static const lean_string_object l_main___closed__375_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_NatBase"};
static const lean_object* l_main___closed__375 = (const lean_object*)&l_main___closed__375_value;
static const lean_ctor_object l_main___closed__376_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__376_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__376_value_aux_0),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__376_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__376_value_aux_1),((lean_object*)&l_main___closed__365_value),LEAN_SCALAR_PTR_LITERAL(146, 182, 100, 241, 87, 145, 21, 110)}};
static const lean_object* l_main___closed__376 = (const lean_object*)&l_main___closed__376_value;
static const lean_ctor_object l_main___closed__377_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__377_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__377_value_aux_0),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__377_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__377_value_aux_1),((lean_object*)&l_main___closed__370_value),LEAN_SCALAR_PTR_LITERAL(201, 220, 6, 88, 194, 28, 147, 123)}};
static const lean_object* l_main___closed__377 = (const lean_object*)&l_main___closed__377_value;
static const lean_string_object l_main___closed__378_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sub_word"};
static const lean_object* l_main___closed__378 = (const lean_object*)&l_main___closed__378_value;
static const lean_ctor_object l_main___closed__379_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__379_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__379_value_aux_0),((lean_object*)&l_main___closed__375_value),LEAN_SCALAR_PTR_LITERAL(91, 112, 243, 140, 79, 143, 193, 156)}};
static const lean_ctor_object l_main___closed__379_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__379_value_aux_1),((lean_object*)&l_main___closed__378_value),LEAN_SCALAR_PTR_LITERAL(207, 79, 41, 175, 58, 149, 134, 117)}};
static const lean_object* l_main___closed__379 = (const lean_object*)&l_main___closed__379_value;
static const lean_array_object l_main___closed__380_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__374_value),((lean_object*)&l_main___closed__376_value),((lean_object*)&l_main___closed__377_value),((lean_object*)&l_main___closed__379_value)}};
static const lean_object* l_main___closed__380 = (const lean_object*)&l_main___closed__380_value;
static const lean_string_object l_main___closed__381_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFP_LoopTerminals"};
static const lean_object* l_main___closed__381 = (const lean_object*)&l_main___closed__381_value;
static const lean_string_object l_main___closed__382_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_main___closed__382 = (const lean_object*)&l_main___closed__382_value;
static const lean_ctor_object l_main___closed__383_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__383_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__383_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__383_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__383_value_aux_1),((lean_object*)&l_main___closed__382_value),LEAN_SCALAR_PTR_LITERAL(123, 217, 188, 18, 12, 151, 22, 194)}};
static const lean_object* l_main___closed__383 = (const lean_object*)&l_main___closed__383_value;
static const lean_string_object l_main___closed__384_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rejected"};
static const lean_object* l_main___closed__384 = (const lean_object*)&l_main___closed__384_value;
static const lean_ctor_object l_main___closed__385_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__385_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__385_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__385_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__385_value_aux_1),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(33, 9, 143, 213, 185, 100, 247, 183)}};
static const lean_object* l_main___closed__385 = (const lean_object*)&l_main___closed__385_value;
static const lean_string_object l_main___closed__386_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "stopped"};
static const lean_object* l_main___closed__386 = (const lean_object*)&l_main___closed__386_value;
static const lean_ctor_object l_main___closed__387_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__387_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__387_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__387_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__387_value_aux_1),((lean_object*)&l_main___closed__386_value),LEAN_SCALAR_PTR_LITERAL(101, 61, 76, 16, 24, 87, 120, 145)}};
static const lean_object* l_main___closed__387 = (const lean_object*)&l_main___closed__387_value;
static const lean_string_object l_main___closed__388_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "child"};
static const lean_object* l_main___closed__388 = (const lean_object*)&l_main___closed__388_value;
static const lean_ctor_object l_main___closed__389_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__389_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__389_value_aux_0),((lean_object*)&l_main___closed__373_value),LEAN_SCALAR_PTR_LITERAL(39, 227, 16, 37, 232, 157, 112, 26)}};
static const lean_ctor_object l_main___closed__389_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__389_value_aux_1),((lean_object*)&l_main___closed__388_value),LEAN_SCALAR_PTR_LITERAL(204, 255, 184, 193, 155, 231, 255, 204)}};
static const lean_object* l_main___closed__389 = (const lean_object*)&l_main___closed__389_value;
static const lean_array_object l_main___closed__390_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__383_value),((lean_object*)&l_main___closed__385_value),((lean_object*)&l_main___closed__387_value),((lean_object*)&l_main___closed__389_value)}};
static const lean_object* l_main___closed__390 = (const lean_object*)&l_main___closed__390_value;
static const lean_string_object l_main___closed__391_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_LoopBudget"};
static const lean_object* l_main___closed__391 = (const lean_object*)&l_main___closed__391_value;
static const lean_ctor_object l_main___closed__392_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__392_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__392_value_aux_0),((lean_object*)&l_main___closed__391_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__392_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__392_value_aux_1),((lean_object*)&l_main___closed__247_value),LEAN_SCALAR_PTR_LITERAL(215, 32, 253, 208, 7, 40, 225, 30)}};
static const lean_object* l_main___closed__392 = (const lean_object*)&l_main___closed__392_value;
static const lean_ctor_object l_main___closed__393_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__393_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__393_value_aux_0),((lean_object*)&l_main___closed__391_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__393_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__393_value_aux_1),((lean_object*)&l_main___closed__249_value),LEAN_SCALAR_PTR_LITERAL(58, 60, 42, 170, 54, 246, 3, 65)}};
static const lean_object* l_main___closed__393 = (const lean_object*)&l_main___closed__393_value;
static const lean_string_object l_main___closed__394_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "diverged"};
static const lean_object* l_main___closed__394 = (const lean_object*)&l_main___closed__394_value;
static const lean_ctor_object l_main___closed__395_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__395_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__395_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__395_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__395_value_aux_1),((lean_object*)&l_main___closed__394_value),LEAN_SCALAR_PTR_LITERAL(122, 15, 102, 113, 216, 62, 46, 226)}};
static const lean_object* l_main___closed__395 = (const lean_object*)&l_main___closed__395_value;
static const lean_string_object l_main___closed__396_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_main___closed__396 = (const lean_object*)&l_main___closed__396_value;
static const lean_ctor_object l_main___closed__397_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__397_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__397_value_aux_0),((lean_object*)&l_main___closed__381_value),LEAN_SCALAR_PTR_LITERAL(239, 41, 199, 219, 165, 42, 167, 142)}};
static const lean_ctor_object l_main___closed__397_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__397_value_aux_1),((lean_object*)&l_main___closed__396_value),LEAN_SCALAR_PTR_LITERAL(25, 49, 207, 98, 169, 197, 196, 117)}};
static const lean_object* l_main___closed__397 = (const lean_object*)&l_main___closed__397_value;
static const lean_array_object l_main___closed__398_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__392_value),((lean_object*)&l_main___closed__393_value),((lean_object*)&l_main___closed__395_value),((lean_object*)&l_main___closed__397_value)}};
static const lean_object* l_main___closed__398 = (const lean_object*)&l_main___closed__398_value;
static const lean_string_object l_main___closed__399_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFP_FrameExt"};
static const lean_object* l_main___closed__399 = (const lean_object*)&l_main___closed__399_value;
static const lean_string_object l_main___closed__400_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_main___closed__400 = (const lean_object*)&l_main___closed__400_value;
static const lean_ctor_object l_main___closed__401_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__401_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__401_value_aux_0),((lean_object*)&l_main___closed__399_value),LEAN_SCALAR_PTR_LITERAL(183, 89, 81, 47, 10, 120, 51, 245)}};
static const lean_ctor_object l_main___closed__401_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__401_value_aux_1),((lean_object*)&l_main___closed__400_value),LEAN_SCALAR_PTR_LITERAL(220, 145, 195, 127, 154, 20, 177, 165)}};
static const lean_object* l_main___closed__401 = (const lean_object*)&l_main___closed__401_value;
static const lean_string_object l_main___closed__402_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFP_GeometryDomains"};
static const lean_object* l_main___closed__402 = (const lean_object*)&l_main___closed__402_value;
static const lean_string_object l_main___closed__403_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reads"};
static const lean_object* l_main___closed__403 = (const lean_object*)&l_main___closed__403_value;
static const lean_ctor_object l_main___closed__404_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__404_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__404_value_aux_0),((lean_object*)&l_main___closed__402_value),LEAN_SCALAR_PTR_LITERAL(86, 86, 2, 155, 143, 134, 85, 221)}};
static const lean_ctor_object l_main___closed__404_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__404_value_aux_1),((lean_object*)&l_main___closed__403_value),LEAN_SCALAR_PTR_LITERAL(195, 76, 148, 244, 79, 46, 204, 67)}};
static const lean_object* l_main___closed__404 = (const lean_object*)&l_main___closed__404_value;
static const lean_string_object l_main___closed__405_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_HeadDomain"};
static const lean_object* l_main___closed__405 = (const lean_object*)&l_main___closed__405_value;
static const lean_string_object l_main___closed__406_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reached"};
static const lean_object* l_main___closed__406 = (const lean_object*)&l_main___closed__406_value;
static const lean_ctor_object l_main___closed__407_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__407_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__407_value_aux_0),((lean_object*)&l_main___closed__405_value),LEAN_SCALAR_PTR_LITERAL(54, 156, 46, 216, 87, 232, 209, 148)}};
static const lean_ctor_object l_main___closed__407_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__407_value_aux_1),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(252, 53, 106, 13, 197, 125, 193, 40)}};
static const lean_object* l_main___closed__407 = (const lean_object*)&l_main___closed__407_value;
static const lean_string_object l_main___closed__408_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "maximum"};
static const lean_object* l_main___closed__408 = (const lean_object*)&l_main___closed__408_value;
static const lean_ctor_object l_main___closed__409_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__409_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__409_value_aux_0),((lean_object*)&l_main___closed__391_value),LEAN_SCALAR_PTR_LITERAL(94, 244, 60, 33, 29, 83, 44, 114)}};
static const lean_ctor_object l_main___closed__409_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__409_value_aux_1),((lean_object*)&l_main___closed__408_value),LEAN_SCALAR_PTR_LITERAL(130, 237, 83, 249, 24, 24, 197, 67)}};
static const lean_object* l_main___closed__409 = (const lean_object*)&l_main___closed__409_value;
static const lean_array_object l_main___closed__410_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__401_value),((lean_object*)&l_main___closed__404_value),((lean_object*)&l_main___closed__407_value),((lean_object*)&l_main___closed__409_value)}};
static const lean_object* l_main___closed__410 = (const lean_object*)&l_main___closed__410_value;
static const lean_string_object l_main___closed__411_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFP_DotCaller"};
static const lean_object* l_main___closed__411 = (const lean_object*)&l_main___closed__411_value;
static const lean_string_object l_main___closed__412_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tail"};
static const lean_object* l_main___closed__412 = (const lean_object*)&l_main___closed__412_value;
static const lean_ctor_object l_main___closed__413_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__413_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__413_value_aux_0),((lean_object*)&l_main___closed__411_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 230, 43, 184, 60, 163, 4)}};
static const lean_ctor_object l_main___closed__413_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__413_value_aux_1),((lean_object*)&l_main___closed__412_value),LEAN_SCALAR_PTR_LITERAL(244, 235, 7, 207, 6, 168, 116, 243)}};
static const lean_object* l_main___closed__413 = (const lean_object*)&l_main___closed__413_value;
static const lean_string_object l_main___closed__414_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_DotDomains"};
static const lean_object* l_main___closed__414 = (const lean_object*)&l_main___closed__414_value;
static const lean_string_object l_main___closed__415_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "returned"};
static const lean_object* l_main___closed__415 = (const lean_object*)&l_main___closed__415_value;
static const lean_ctor_object l_main___closed__416_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__416_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__416_value_aux_0),((lean_object*)&l_main___closed__414_value),LEAN_SCALAR_PTR_LITERAL(176, 127, 218, 117, 196, 215, 101, 155)}};
static const lean_ctor_object l_main___closed__416_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__416_value_aux_1),((lean_object*)&l_main___closed__415_value),LEAN_SCALAR_PTR_LITERAL(234, 245, 209, 227, 196, 227, 67, 7)}};
static const lean_object* l_main___closed__416 = (const lean_object*)&l_main___closed__416_value;
static const lean_string_object l_main___closed__417_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFP_DotInstall"};
static const lean_object* l_main___closed__417 = (const lean_object*)&l_main___closed__417_value;
static const lean_string_object l_main___closed__418_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dot_result"};
static const lean_object* l_main___closed__418 = (const lean_object*)&l_main___closed__418_value;
static const lean_ctor_object l_main___closed__419_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__419_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__419_value_aux_0),((lean_object*)&l_main___closed__417_value),LEAN_SCALAR_PTR_LITERAL(24, 118, 1, 221, 143, 165, 20, 107)}};
static const lean_ctor_object l_main___closed__419_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__419_value_aux_1),((lean_object*)&l_main___closed__418_value),LEAN_SCALAR_PTR_LITERAL(155, 210, 244, 116, 168, 80, 94, 36)}};
static const lean_object* l_main___closed__419 = (const lean_object*)&l_main___closed__419_value;
static const lean_ctor_object l_main___closed__420_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__420_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__420_value_aux_0),((lean_object*)&l_main___closed__417_value),LEAN_SCALAR_PTR_LITERAL(24, 118, 1, 221, 143, 165, 20, 107)}};
static const lean_ctor_object l_main___closed__420_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__420_value_aux_1),((lean_object*)&l_main___closed__293_value),LEAN_SCALAR_PTR_LITERAL(136, 117, 249, 217, 14, 238, 209, 212)}};
static const lean_object* l_main___closed__420 = (const lean_object*)&l_main___closed__420_value;
static const lean_array_object l_main___closed__421_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__413_value),((lean_object*)&l_main___closed__416_value),((lean_object*)&l_main___closed__419_value),((lean_object*)&l_main___closed__420_value)}};
static const lean_object* l_main___closed__421 = (const lean_object*)&l_main___closed__421_value;
static const lean_string_object l_main___closed__422_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_Carrier"};
static const lean_object* l_main___closed__422 = (const lean_object*)&l_main___closed__422_value;
static const lean_string_object l_main___closed__423_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "from_to"};
static const lean_object* l_main___closed__423 = (const lean_object*)&l_main___closed__423_value;
static const lean_ctor_object l_main___closed__424_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__424_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__424_value_aux_0),((lean_object*)&l_main___closed__422_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__424_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__424_value_aux_1),((lean_object*)&l_main___closed__423_value),LEAN_SCALAR_PTR_LITERAL(226, 146, 35, 10, 11, 120, 251, 192)}};
static const lean_object* l_main___closed__424 = (const lean_object*)&l_main___closed__424_value;
static const lean_string_object l_main___closed__425_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "to_from"};
static const lean_object* l_main___closed__425 = (const lean_object*)&l_main___closed__425_value;
static const lean_ctor_object l_main___closed__426_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__426_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__426_value_aux_0),((lean_object*)&l_main___closed__422_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__426_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__426_value_aux_1),((lean_object*)&l_main___closed__425_value),LEAN_SCALAR_PTR_LITERAL(76, 50, 240, 31, 131, 133, 75, 212)}};
static const lean_object* l_main___closed__426 = (const lean_object*)&l_main___closed__426_value;
static const lean_string_object l_main___closed__427_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "words"};
static const lean_object* l_main___closed__427 = (const lean_object*)&l_main___closed__427_value;
static const lean_ctor_object l_main___closed__428_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__428_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__428_value_aux_0),((lean_object*)&l_main___closed__422_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__428_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__428_value_aux_1),((lean_object*)&l_main___closed__427_value),LEAN_SCALAR_PTR_LITERAL(186, 109, 129, 71, 129, 137, 136, 22)}};
static const lean_object* l_main___closed__428 = (const lean_object*)&l_main___closed__428_value;
static const lean_ctor_object l_main___closed__429_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__429_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__429_value_aux_0),((lean_object*)&l_main___closed__411_value),LEAN_SCALAR_PTR_LITERAL(199, 242, 230, 43, 184, 60, 163, 4)}};
static const lean_ctor_object l_main___closed__429_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__429_value_aux_1),((lean_object*)&l_main___closed__267_value),LEAN_SCALAR_PTR_LITERAL(208, 111, 192, 28, 125, 232, 238, 170)}};
static const lean_object* l_main___closed__429 = (const lean_object*)&l_main___closed__429_value;
static const lean_array_object l_main___closed__430_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__424_value),((lean_object*)&l_main___closed__426_value),((lean_object*)&l_main___closed__428_value),((lean_object*)&l_main___closed__429_value)}};
static const lean_object* l_main___closed__430 = (const lean_object*)&l_main___closed__430_value;
static const lean_string_object l_main___closed__431_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Thread"};
static const lean_object* l_main___closed__431 = (const lean_object*)&l_main___closed__431_value;
static const lean_string_object l_main___closed__432_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_main___closed__432 = (const lean_object*)&l_main___closed__432_value;
static const lean_ctor_object l_main___closed__433_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__433_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__433_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__433_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__433_value_aux_1),((lean_object*)&l_main___closed__432_value),LEAN_SCALAR_PTR_LITERAL(25, 192, 101, 193, 116, 160, 52, 50)}};
static const lean_object* l_main___closed__433 = (const lean_object*)&l_main___closed__433_value;
static const lean_string_object l_main___closed__434_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__434 = (const lean_object*)&l_main___closed__434_value;
static const lean_ctor_object l_main___closed__435_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__435_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__435_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__435_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__435_value_aux_1),((lean_object*)&l_main___closed__434_value),LEAN_SCALAR_PTR_LITERAL(248, 15, 109, 66, 111, 241, 252, 39)}};
static const lean_object* l_main___closed__435 = (const lean_object*)&l_main___closed__435_value;
static const lean_string_object l_main___closed__436_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFP_Advance"};
static const lean_object* l_main___closed__436 = (const lean_object*)&l_main___closed__436_value;
static const lean_ctor_object l_main___closed__437_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__437_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__437_value_aux_0),((lean_object*)&l_main___closed__436_value),LEAN_SCALAR_PTR_LITERAL(180, 104, 145, 38, 238, 42, 79, 101)}};
static const lean_ctor_object l_main___closed__437_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__437_value_aux_1),((lean_object*)&l_main___closed__349_value),LEAN_SCALAR_PTR_LITERAL(220, 148, 186, 0, 139, 212, 2, 228)}};
static const lean_object* l_main___closed__437 = (const lean_object*)&l_main___closed__437_value;
static const lean_string_object l_main___closed__438_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonical"};
static const lean_object* l_main___closed__438 = (const lean_object*)&l_main___closed__438_value;
static const lean_ctor_object l_main___closed__439_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__439_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__439_value_aux_0),((lean_object*)&l_main___closed__422_value),LEAN_SCALAR_PTR_LITERAL(15, 158, 9, 216, 113, 114, 113, 106)}};
static const lean_ctor_object l_main___closed__439_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__439_value_aux_1),((lean_object*)&l_main___closed__438_value),LEAN_SCALAR_PTR_LITERAL(30, 159, 83, 66, 130, 43, 155, 199)}};
static const lean_object* l_main___closed__439 = (const lean_object*)&l_main___closed__439_value;
static const lean_array_object l_main___closed__440_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__433_value),((lean_object*)&l_main___closed__435_value),((lean_object*)&l_main___closed__437_value),((lean_object*)&l_main___closed__439_value)}};
static const lean_object* l_main___closed__440 = (const lean_object*)&l_main___closed__440_value;
static const lean_string_object l_main___closed__441_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance3"};
static const lean_object* l_main___closed__441 = (const lean_object*)&l_main___closed__441_value;
static const lean_ctor_object l_main___closed__442_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__442_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__442_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__442_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__442_value_aux_1),((lean_object*)&l_main___closed__441_value),LEAN_SCALAR_PTR_LITERAL(253, 86, 175, 235, 209, 155, 38, 3)}};
static const lean_object* l_main___closed__442 = (const lean_object*)&l_main___closed__442_value;
static const lean_string_object l_main___closed__443_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance4"};
static const lean_object* l_main___closed__443 = (const lean_object*)&l_main___closed__443_value;
static const lean_ctor_object l_main___closed__444_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__444_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__444_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__444_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__444_value_aux_1),((lean_object*)&l_main___closed__443_value),LEAN_SCALAR_PTR_LITERAL(27, 35, 21, 223, 238, 83, 53, 179)}};
static const lean_object* l_main___closed__444 = (const lean_object*)&l_main___closed__444_value;
static const lean_string_object l_main___closed__445_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance5"};
static const lean_object* l_main___closed__445 = (const lean_object*)&l_main___closed__445_value;
static const lean_ctor_object l_main___closed__446_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__446_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__446_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__446_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__446_value_aux_1),((lean_object*)&l_main___closed__445_value),LEAN_SCALAR_PTR_LITERAL(98, 105, 130, 74, 21, 187, 121, 84)}};
static const lean_object* l_main___closed__446 = (const lean_object*)&l_main___closed__446_value;
static const lean_string_object l_main___closed__447_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance6"};
static const lean_object* l_main___closed__447 = (const lean_object*)&l_main___closed__447_value;
static const lean_ctor_object l_main___closed__448_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__448_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__448_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__448_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__448_value_aux_1),((lean_object*)&l_main___closed__447_value),LEAN_SCALAR_PTR_LITERAL(127, 221, 39, 217, 235, 184, 187, 188)}};
static const lean_object* l_main___closed__448 = (const lean_object*)&l_main___closed__448_value;
static const lean_array_object l_main___closed__449_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__442_value),((lean_object*)&l_main___closed__444_value),((lean_object*)&l_main___closed__446_value),((lean_object*)&l_main___closed__448_value)}};
static const lean_object* l_main___closed__449 = (const lean_object*)&l_main___closed__449_value;
static const lean_string_object l_main___closed__450_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "advance"};
static const lean_object* l_main___closed__450 = (const lean_object*)&l_main___closed__450_value;
static const lean_ctor_object l_main___closed__451_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__451_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__451_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__451_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__451_value_aux_1),((lean_object*)&l_main___closed__450_value),LEAN_SCALAR_PTR_LITERAL(0, 44, 131, 14, 179, 219, 49, 39)}};
static const lean_object* l_main___closed__451 = (const lean_object*)&l_main___closed__451_value;
static const lean_string_object l_main___closed__452_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance0"};
static const lean_object* l_main___closed__452 = (const lean_object*)&l_main___closed__452_value;
static const lean_ctor_object l_main___closed__453_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__453_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__453_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__453_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__453_value_aux_1),((lean_object*)&l_main___closed__452_value),LEAN_SCALAR_PTR_LITERAL(72, 218, 125, 145, 26, 60, 66, 185)}};
static const lean_object* l_main___closed__453 = (const lean_object*)&l_main___closed__453_value;
static const lean_string_object l_main___closed__454_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance1"};
static const lean_object* l_main___closed__454 = (const lean_object*)&l_main___closed__454_value;
static const lean_ctor_object l_main___closed__455_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__455_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__455_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__455_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__455_value_aux_1),((lean_object*)&l_main___closed__454_value),LEAN_SCALAR_PTR_LITERAL(111, 214, 217, 182, 79, 81, 150, 175)}};
static const lean_object* l_main___closed__455 = (const lean_object*)&l_main___closed__455_value;
static const lean_string_object l_main___closed__456_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "advance2"};
static const lean_object* l_main___closed__456 = (const lean_object*)&l_main___closed__456_value;
static const lean_ctor_object l_main___closed__457_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__457_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__457_value_aux_0),((lean_object*)&l_main___closed__431_value),LEAN_SCALAR_PTR_LITERAL(232, 36, 49, 0, 62, 7, 10, 96)}};
static const lean_ctor_object l_main___closed__457_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__457_value_aux_1),((lean_object*)&l_main___closed__456_value),LEAN_SCALAR_PTR_LITERAL(50, 199, 149, 52, 163, 123, 10, 73)}};
static const lean_object* l_main___closed__457 = (const lean_object*)&l_main___closed__457_value;
static const lean_array_object l_main___closed__458_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__451_value),((lean_object*)&l_main___closed__453_value),((lean_object*)&l_main___closed__455_value),((lean_object*)&l_main___closed__457_value)}};
static const lean_object* l_main___closed__458 = (const lean_object*)&l_main___closed__458_value;
static const lean_string_object l_main___closed__459_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Single"};
static const lean_object* l_main___closed__459 = (const lean_object*)&l_main___closed__459_value;
static const lean_string_object l_main___closed__460_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "same"};
static const lean_object* l_main___closed__460 = (const lean_object*)&l_main___closed__460_value;
static const lean_ctor_object l_main___closed__461_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__461_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__461_value_aux_0),((lean_object*)&l_main___closed__459_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__461_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__461_value_aux_1),((lean_object*)&l_main___closed__460_value),LEAN_SCALAR_PTR_LITERAL(136, 225, 49, 109, 161, 134, 112, 52)}};
static const lean_object* l_main___closed__461 = (const lean_object*)&l_main___closed__461_value;
static const lean_string_object l_main___closed__462_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFM_Span"};
static const lean_object* l_main___closed__462 = (const lean_object*)&l_main___closed__462_value;
static const lean_string_object l_main___closed__463_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scalar"};
static const lean_object* l_main___closed__463 = (const lean_object*)&l_main___closed__463_value;
static const lean_ctor_object l_main___closed__464_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__464_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__464_value_aux_0),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__464_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__464_value_aux_1),((lean_object*)&l_main___closed__463_value),LEAN_SCALAR_PTR_LITERAL(207, 75, 193, 166, 166, 255, 152, 94)}};
static const lean_object* l_main___closed__464 = (const lean_object*)&l_main___closed__464_value;
static const lean_ctor_object l_main___closed__465_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__465_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__465_value_aux_0),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__465_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__465_value_aux_1),((lean_object*)&l_main___closed__412_value),LEAN_SCALAR_PTR_LITERAL(175, 160, 152, 99, 169, 9, 74, 195)}};
static const lean_object* l_main___closed__465 = (const lean_object*)&l_main___closed__465_value;
static const lean_string_object l_main___closed__466_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "window"};
static const lean_object* l_main___closed__466 = (const lean_object*)&l_main___closed__466_value;
static const lean_ctor_object l_main___closed__467_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__467_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__467_value_aux_0),((lean_object*)&l_main___closed__462_value),LEAN_SCALAR_PTR_LITERAL(208, 77, 18, 208, 232, 177, 150, 234)}};
static const lean_ctor_object l_main___closed__467_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__467_value_aux_1),((lean_object*)&l_main___closed__466_value),LEAN_SCALAR_PTR_LITERAL(212, 99, 40, 183, 138, 131, 214, 78)}};
static const lean_object* l_main___closed__467 = (const lean_object*)&l_main___closed__467_value;
static const lean_array_object l_main___closed__468_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__461_value),((lean_object*)&l_main___closed__464_value),((lean_object*)&l_main___closed__465_value),((lean_object*)&l_main___closed__467_value)}};
static const lean_object* l_main___closed__468 = (const lean_object*)&l_main___closed__468_value;
static const lean_string_object l_main___closed__469_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFM_ProductInstance"};
static const lean_object* l_main___closed__469 = (const lean_object*)&l_main___closed__469_value;
static const lean_string_object l_main___closed__470_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wrapper"};
static const lean_object* l_main___closed__470 = (const lean_object*)&l_main___closed__470_value;
static const lean_ctor_object l_main___closed__471_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__471_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__471_value_aux_0),((lean_object*)&l_main___closed__469_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__471_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__471_value_aux_1),((lean_object*)&l_main___closed__470_value),LEAN_SCALAR_PTR_LITERAL(173, 78, 168, 213, 70, 99, 52, 197)}};
static const lean_object* l_main___closed__471 = (const lean_object*)&l_main___closed__471_value;
static const lean_ctor_object l_main___closed__472_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__472_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__472_value_aux_0),((lean_object*)&l_main___closed__459_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__472_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__472_value_aux_1),((lean_object*)&l_main___closed__297_value),LEAN_SCALAR_PTR_LITERAL(250, 91, 23, 186, 33, 41, 156, 120)}};
static const lean_object* l_main___closed__472 = (const lean_object*)&l_main___closed__472_value;
static const lean_ctor_object l_main___closed__473_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__473_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__473_value_aux_0),((lean_object*)&l_main___closed__459_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__473_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__473_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(25, 203, 78, 204, 6, 110, 68, 189)}};
static const lean_object* l_main___closed__473 = (const lean_object*)&l_main___closed__473_value;
static const lean_string_object l_main___closed__474_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "main_same"};
static const lean_object* l_main___closed__474 = (const lean_object*)&l_main___closed__474_value;
static const lean_ctor_object l_main___closed__475_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__475_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__475_value_aux_0),((lean_object*)&l_main___closed__459_value),LEAN_SCALAR_PTR_LITERAL(160, 19, 217, 253, 90, 20, 194, 84)}};
static const lean_ctor_object l_main___closed__475_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__475_value_aux_1),((lean_object*)&l_main___closed__474_value),LEAN_SCALAR_PTR_LITERAL(17, 13, 72, 22, 179, 169, 150, 197)}};
static const lean_object* l_main___closed__475 = (const lean_object*)&l_main___closed__475_value;
static const lean_array_object l_main___closed__476_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__471_value),((lean_object*)&l_main___closed__472_value),((lean_object*)&l_main___closed__473_value),((lean_object*)&l_main___closed__475_value)}};
static const lean_object* l_main___closed__476 = (const lean_object*)&l_main___closed__476_value;
static const lean_string_object l_main___closed__477_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFM_InnerControl"};
static const lean_object* l_main___closed__477 = (const lean_object*)&l_main___closed__477_value;
static const lean_ctor_object l_main___closed__478_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__478_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__478_value_aux_0),((lean_object*)&l_main___closed__477_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__478_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__478_value_aux_1),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(173, 63, 11, 215, 68, 78, 129, 62)}};
static const lean_object* l_main___closed__478 = (const lean_object*)&l_main___closed__478_value;
static const lean_ctor_object l_main___closed__479_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__479_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__479_value_aux_0),((lean_object*)&l_main___closed__469_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__479_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__479_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(49, 64, 12, 130, 97, 100, 181, 138)}};
static const lean_object* l_main___closed__479 = (const lean_object*)&l_main___closed__479_value;
static const lean_string_object l_main___closed__480_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "main_law"};
static const lean_object* l_main___closed__480 = (const lean_object*)&l_main___closed__480_value;
static const lean_ctor_object l_main___closed__481_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__481_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__481_value_aux_0),((lean_object*)&l_main___closed__469_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__481_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__481_value_aux_1),((lean_object*)&l_main___closed__480_value),LEAN_SCALAR_PTR_LITERAL(91, 92, 160, 243, 255, 19, 254, 98)}};
static const lean_object* l_main___closed__481 = (const lean_object*)&l_main___closed__481_value;
static const lean_string_object l_main___closed__482_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tail_law"};
static const lean_object* l_main___closed__482 = (const lean_object*)&l_main___closed__482_value;
static const lean_ctor_object l_main___closed__483_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__483_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__483_value_aux_0),((lean_object*)&l_main___closed__469_value),LEAN_SCALAR_PTR_LITERAL(132, 131, 20, 100, 229, 183, 118, 216)}};
static const lean_ctor_object l_main___closed__483_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__483_value_aux_1),((lean_object*)&l_main___closed__482_value),LEAN_SCALAR_PTR_LITERAL(18, 4, 130, 45, 231, 249, 80, 103)}};
static const lean_object* l_main___closed__483 = (const lean_object*)&l_main___closed__483_value;
static const lean_array_object l_main___closed__484_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__478_value),((lean_object*)&l_main___closed__479_value),((lean_object*)&l_main___closed__481_value),((lean_object*)&l_main___closed__483_value)}};
static const lean_object* l_main___closed__484 = (const lean_object*)&l_main___closed__484_value;
static const lean_string_object l_main___closed__485_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFM_Frames"};
static const lean_object* l_main___closed__485 = (const lean_object*)&l_main___closed__485_value;
static const lean_string_object l_main___closed__486_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "sequence"};
static const lean_object* l_main___closed__486 = (const lean_object*)&l_main___closed__486_value;
static const lean_ctor_object l_main___closed__487_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__487_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__487_value_aux_0),((lean_object*)&l_main___closed__485_value),LEAN_SCALAR_PTR_LITERAL(87, 248, 228, 255, 233, 2, 254, 94)}};
static const lean_ctor_object l_main___closed__487_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__487_value_aux_1),((lean_object*)&l_main___closed__486_value),LEAN_SCALAR_PTR_LITERAL(4, 253, 116, 32, 188, 71, 54, 146)}};
static const lean_object* l_main___closed__487 = (const lean_object*)&l_main___closed__487_value;
static const lean_ctor_object l_main___closed__488_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__488_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__488_value_aux_0),((lean_object*)&l_main___closed__485_value),LEAN_SCALAR_PTR_LITERAL(87, 248, 228, 255, 233, 2, 254, 94)}};
static const lean_ctor_object l_main___closed__488_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__488_value_aux_1),((lean_object*)&l_main___closed__466_value),LEAN_SCALAR_PTR_LITERAL(191, 246, 200, 55, 1, 85, 150, 96)}};
static const lean_object* l_main___closed__488 = (const lean_object*)&l_main___closed__488_value;
static const lean_ctor_object l_main___closed__489_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__489_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__489_value_aux_0),((lean_object*)&l_main___closed__477_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__489_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__489_value_aux_1),((lean_object*)&l_main___closed__255_value),LEAN_SCALAR_PTR_LITERAL(160, 5, 238, 112, 253, 92, 35, 153)}};
static const lean_object* l_main___closed__489 = (const lean_object*)&l_main___closed__489_value;
static const lean_string_object l_main___closed__490_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "at_cut"};
static const lean_object* l_main___closed__490 = (const lean_object*)&l_main___closed__490_value;
static const lean_ctor_object l_main___closed__491_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__491_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__491_value_aux_0),((lean_object*)&l_main___closed__477_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 169, 76, 226, 18, 200, 168)}};
static const lean_ctor_object l_main___closed__491_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__491_value_aux_1),((lean_object*)&l_main___closed__490_value),LEAN_SCALAR_PTR_LITERAL(209, 204, 74, 21, 22, 19, 116, 22)}};
static const lean_object* l_main___closed__491 = (const lean_object*)&l_main___closed__491_value;
static const lean_array_object l_main___closed__492_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__487_value),((lean_object*)&l_main___closed__488_value),((lean_object*)&l_main___closed__489_value),((lean_object*)&l_main___closed__491_value)}};
static const lean_object* l_main___closed__492 = (const lean_object*)&l_main___closed__492_value;
static const lean_string_object l_main___closed__493_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFM_Cuts"};
static const lean_object* l_main___closed__493 = (const lean_object*)&l_main___closed__493_value;
static const lean_string_object l_main___closed__494_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "window_erased"};
static const lean_object* l_main___closed__494 = (const lean_object*)&l_main___closed__494_value;
static const lean_ctor_object l_main___closed__495_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__495_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__495_value_aux_0),((lean_object*)&l_main___closed__493_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__495_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__495_value_aux_1),((lean_object*)&l_main___closed__494_value),LEAN_SCALAR_PTR_LITERAL(62, 212, 90, 206, 108, 28, 221, 21)}};
static const lean_object* l_main___closed__495 = (const lean_object*)&l_main___closed__495_value;
static const lean_string_object l_main___closed__496_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFM_Domains"};
static const lean_object* l_main___closed__496 = (const lean_object*)&l_main___closed__496_value;
static const lean_string_object l_main___closed__497_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "limb_cap"};
static const lean_object* l_main___closed__497 = (const lean_object*)&l_main___closed__497_value;
static const lean_ctor_object l_main___closed__498_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__498_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__498_value_aux_0),((lean_object*)&l_main___closed__496_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__498_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__498_value_aux_1),((lean_object*)&l_main___closed__497_value),LEAN_SCALAR_PTR_LITERAL(109, 216, 106, 241, 154, 201, 222, 223)}};
static const lean_object* l_main___closed__498 = (const lean_object*)&l_main___closed__498_value;
static const lean_string_object l_main___closed__499_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "slots"};
static const lean_object* l_main___closed__499 = (const lean_object*)&l_main___closed__499_value;
static const lean_ctor_object l_main___closed__500_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__500_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__500_value_aux_0),((lean_object*)&l_main___closed__496_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__500_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__500_value_aux_1),((lean_object*)&l_main___closed__499_value),LEAN_SCALAR_PTR_LITERAL(126, 66, 142, 1, 163, 23, 219, 29)}};
static const lean_object* l_main___closed__500 = (const lean_object*)&l_main___closed__500_value;
static const lean_string_object l_main___closed__501_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sums_reset"};
static const lean_object* l_main___closed__501 = (const lean_object*)&l_main___closed__501_value;
static const lean_ctor_object l_main___closed__502_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__502_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__502_value_aux_0),((lean_object*)&l_main___closed__496_value),LEAN_SCALAR_PTR_LITERAL(227, 109, 112, 169, 120, 216, 106, 251)}};
static const lean_ctor_object l_main___closed__502_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__502_value_aux_1),((lean_object*)&l_main___closed__501_value),LEAN_SCALAR_PTR_LITERAL(217, 142, 132, 164, 186, 103, 151, 208)}};
static const lean_object* l_main___closed__502 = (const lean_object*)&l_main___closed__502_value;
static const lean_array_object l_main___closed__503_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__495_value),((lean_object*)&l_main___closed__498_value),((lean_object*)&l_main___closed__500_value),((lean_object*)&l_main___closed__502_value)}};
static const lean_object* l_main___closed__503 = (const lean_object*)&l_main___closed__503_value;
static const lean_string_object l_main___closed__504_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFM_Control"};
static const lean_object* l_main___closed__504 = (const lean_object*)&l_main___closed__504_value;
static const lean_string_object l_main___closed__505_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_count"};
static const lean_object* l_main___closed__505 = (const lean_object*)&l_main___closed__505_value;
static const lean_ctor_object l_main___closed__506_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__506_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__506_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__506_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__506_value_aux_1),((lean_object*)&l_main___closed__505_value),LEAN_SCALAR_PTR_LITERAL(199, 86, 211, 81, 73, 218, 83, 204)}};
static const lean_object* l_main___closed__506 = (const lean_object*)&l_main___closed__506_value;
static const lean_string_object l_main___closed__507_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abort_prefix"};
static const lean_object* l_main___closed__507 = (const lean_object*)&l_main___closed__507_value;
static const lean_ctor_object l_main___closed__508_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__508_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__508_value_aux_0),((lean_object*)&l_main___closed__493_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__508_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__508_value_aux_1),((lean_object*)&l_main___closed__507_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 251, 208, 222, 37, 175, 67)}};
static const lean_object* l_main___closed__508 = (const lean_object*)&l_main___closed__508_value;
static const lean_ctor_object l_main___closed__509_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__509_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__509_value_aux_0),((lean_object*)&l_main___closed__493_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__509_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__509_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(117, 55, 90, 132, 124, 22, 88, 174)}};
static const lean_object* l_main___closed__509 = (const lean_object*)&l_main___closed__509_value;
static const lean_ctor_object l_main___closed__510_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__510_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__510_value_aux_0),((lean_object*)&l_main___closed__493_value),LEAN_SCALAR_PTR_LITERAL(235, 113, 129, 105, 240, 183, 139, 185)}};
static const lean_ctor_object l_main___closed__510_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__510_value_aux_1),((lean_object*)&l_main___closed__434_value),LEAN_SCALAR_PTR_LITERAL(183, 69, 1, 228, 233, 22, 164, 235)}};
static const lean_object* l_main___closed__510 = (const lean_object*)&l_main___closed__510_value;
static const lean_array_object l_main___closed__511_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__506_value),((lean_object*)&l_main___closed__508_value),((lean_object*)&l_main___closed__509_value),((lean_object*)&l_main___closed__510_value)}};
static const lean_object* l_main___closed__511 = (const lean_object*)&l_main___closed__511_value;
static const lean_string_object l_main___closed__512_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next6"};
static const lean_object* l_main___closed__512 = (const lean_object*)&l_main___closed__512_value;
static const lean_ctor_object l_main___closed__513_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__513_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__513_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__513_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__513_value_aux_1),((lean_object*)&l_main___closed__512_value),LEAN_SCALAR_PTR_LITERAL(116, 231, 213, 25, 116, 238, 186, 201)}};
static const lean_object* l_main___closed__513 = (const lean_object*)&l_main___closed__513_value;
static const lean_string_object l_main___closed__514_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "next_at"};
static const lean_object* l_main___closed__514 = (const lean_object*)&l_main___closed__514_value;
static const lean_ctor_object l_main___closed__515_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__515_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__515_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__515_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__515_value_aux_1),((lean_object*)&l_main___closed__514_value),LEAN_SCALAR_PTR_LITERAL(224, 38, 147, 240, 112, 154, 134, 154)}};
static const lean_object* l_main___closed__515 = (const lean_object*)&l_main___closed__515_value;
static const lean_string_object l_main___closed__516_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "state_sequence"};
static const lean_object* l_main___closed__516 = (const lean_object*)&l_main___closed__516_value;
static const lean_ctor_object l_main___closed__517_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__517_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__517_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__517_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__517_value_aux_1),((lean_object*)&l_main___closed__516_value),LEAN_SCALAR_PTR_LITERAL(99, 202, 198, 244, 29, 25, 63, 89)}};
static const lean_object* l_main___closed__517 = (const lean_object*)&l_main___closed__517_value;
static const lean_ctor_object l_main___closed__518_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__518_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__518_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__518_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__518_value_aux_1),((lean_object*)&l_main___closed__386_value),LEAN_SCALAR_PTR_LITERAL(38, 222, 9, 153, 75, 54, 109, 149)}};
static const lean_object* l_main___closed__518 = (const lean_object*)&l_main___closed__518_value;
static const lean_array_object l_main___closed__519_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__513_value),((lean_object*)&l_main___closed__515_value),((lean_object*)&l_main___closed__517_value),((lean_object*)&l_main___closed__518_value)}};
static const lean_object* l_main___closed__519 = (const lean_object*)&l_main___closed__519_value;
static const lean_string_object l_main___closed__520_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next2"};
static const lean_object* l_main___closed__520 = (const lean_object*)&l_main___closed__520_value;
static const lean_ctor_object l_main___closed__521_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__521_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__521_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__521_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__521_value_aux_1),((lean_object*)&l_main___closed__520_value),LEAN_SCALAR_PTR_LITERAL(69, 57, 5, 6, 20, 199, 121, 101)}};
static const lean_object* l_main___closed__521 = (const lean_object*)&l_main___closed__521_value;
static const lean_string_object l_main___closed__522_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next3"};
static const lean_object* l_main___closed__522 = (const lean_object*)&l_main___closed__522_value;
static const lean_ctor_object l_main___closed__523_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__523_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__523_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__523_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__523_value_aux_1),((lean_object*)&l_main___closed__522_value),LEAN_SCALAR_PTR_LITERAL(237, 11, 178, 68, 3, 176, 155, 77)}};
static const lean_object* l_main___closed__523 = (const lean_object*)&l_main___closed__523_value;
static const lean_string_object l_main___closed__524_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next4"};
static const lean_object* l_main___closed__524 = (const lean_object*)&l_main___closed__524_value;
static const lean_ctor_object l_main___closed__525_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__525_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__525_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__525_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__525_value_aux_1),((lean_object*)&l_main___closed__524_value),LEAN_SCALAR_PTR_LITERAL(41, 34, 253, 149, 7, 230, 117, 180)}};
static const lean_object* l_main___closed__525 = (const lean_object*)&l_main___closed__525_value;
static const lean_string_object l_main___closed__526_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next5"};
static const lean_object* l_main___closed__526 = (const lean_object*)&l_main___closed__526_value;
static const lean_ctor_object l_main___closed__527_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__527_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__527_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__527_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__527_value_aux_1),((lean_object*)&l_main___closed__526_value),LEAN_SCALAR_PTR_LITERAL(161, 234, 60, 182, 15, 80, 36, 164)}};
static const lean_object* l_main___closed__527 = (const lean_object*)&l_main___closed__527_value;
static const lean_array_object l_main___closed__528_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__521_value),((lean_object*)&l_main___closed__523_value),((lean_object*)&l_main___closed__525_value),((lean_object*)&l_main___closed__527_value)}};
static const lean_object* l_main___closed__528 = (const lean_object*)&l_main___closed__528_value;
static const lean_string_object l_main___closed__529_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixed_outer"};
static const lean_object* l_main___closed__529 = (const lean_object*)&l_main___closed__529_value;
static const lean_ctor_object l_main___closed__530_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__530_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__530_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__530_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__530_value_aux_1),((lean_object*)&l_main___closed__529_value),LEAN_SCALAR_PTR_LITERAL(55, 225, 94, 109, 221, 102, 54, 232)}};
static const lean_object* l_main___closed__530 = (const lean_object*)&l_main___closed__530_value;
static const lean_string_object l_main___closed__531_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fixed_terms"};
static const lean_object* l_main___closed__531 = (const lean_object*)&l_main___closed__531_value;
static const lean_ctor_object l_main___closed__532_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__532_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__532_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__532_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__532_value_aux_1),((lean_object*)&l_main___closed__531_value),LEAN_SCALAR_PTR_LITERAL(26, 101, 195, 203, 0, 183, 19, 181)}};
static const lean_object* l_main___closed__532 = (const lean_object*)&l_main___closed__532_value;
static const lean_string_object l_main___closed__533_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next0"};
static const lean_object* l_main___closed__533 = (const lean_object*)&l_main___closed__533_value;
static const lean_ctor_object l_main___closed__534_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__534_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__534_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__534_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__534_value_aux_1),((lean_object*)&l_main___closed__533_value),LEAN_SCALAR_PTR_LITERAL(8, 19, 179, 5, 66, 208, 134, 192)}};
static const lean_object* l_main___closed__534 = (const lean_object*)&l_main___closed__534_value;
static const lean_string_object l_main___closed__535_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next1"};
static const lean_object* l_main___closed__535 = (const lean_object*)&l_main___closed__535_value;
static const lean_ctor_object l_main___closed__536_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__536_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__536_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__536_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__536_value_aux_1),((lean_object*)&l_main___closed__535_value),LEAN_SCALAR_PTR_LITERAL(64, 26, 212, 95, 77, 191, 199, 40)}};
static const lean_object* l_main___closed__536 = (const lean_object*)&l_main___closed__536_value;
static const lean_array_object l_main___closed__537_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__530_value),((lean_object*)&l_main___closed__532_value),((lean_object*)&l_main___closed__534_value),((lean_object*)&l_main___closed__536_value)}};
static const lean_object* l_main___closed__537 = (const lean_object*)&l_main___closed__537_value;
static const lean_string_object l_main___closed__538_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFI_WrapperTrace"};
static const lean_object* l_main___closed__538 = (const lean_object*)&l_main___closed__538_value;
static const lean_string_object l_main___closed__539_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "headline"};
static const lean_object* l_main___closed__539 = (const lean_object*)&l_main___closed__539_value;
static const lean_ctor_object l_main___closed__540_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__540_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__540_value_aux_0),((lean_object*)&l_main___closed__538_value),LEAN_SCALAR_PTR_LITERAL(108, 62, 131, 135, 24, 53, 95, 21)}};
static const lean_ctor_object l_main___closed__540_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__540_value_aux_1),((lean_object*)&l_main___closed__539_value),LEAN_SCALAR_PTR_LITERAL(181, 207, 198, 86, 178, 179, 146, 230)}};
static const lean_object* l_main___closed__540 = (const lean_object*)&l_main___closed__540_value;
static const lean_string_object l_main___closed__541_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFM_CallDomains"};
static const lean_object* l_main___closed__541 = (const lean_object*)&l_main___closed__541_value;
static const lean_string_object l_main___closed__542_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tail_counts"};
static const lean_object* l_main___closed__542 = (const lean_object*)&l_main___closed__542_value;
static const lean_ctor_object l_main___closed__543_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__543_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__543_value_aux_0),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(28, 182, 30, 20, 17, 15, 40, 165)}};
static const lean_ctor_object l_main___closed__543_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__543_value_aux_1),((lean_object*)&l_main___closed__542_value),LEAN_SCALAR_PTR_LITERAL(28, 112, 226, 119, 52, 124, 202, 240)}};
static const lean_object* l_main___closed__543 = (const lean_object*)&l_main___closed__543_value;
static const lean_string_object l_main___closed__544_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "terminal"};
static const lean_object* l_main___closed__544 = (const lean_object*)&l_main___closed__544_value;
static const lean_ctor_object l_main___closed__545_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__545_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__545_value_aux_0),((lean_object*)&l_main___closed__541_value),LEAN_SCALAR_PTR_LITERAL(28, 182, 30, 20, 17, 15, 40, 165)}};
static const lean_ctor_object l_main___closed__545_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__545_value_aux_1),((lean_object*)&l_main___closed__544_value),LEAN_SCALAR_PTR_LITERAL(110, 28, 239, 55, 39, 140, 216, 27)}};
static const lean_object* l_main___closed__545 = (const lean_object*)&l_main___closed__545_value;
static const lean_string_object l_main___closed__546_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "body_at"};
static const lean_object* l_main___closed__546 = (const lean_object*)&l_main___closed__546_value;
static const lean_ctor_object l_main___closed__547_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__547_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__547_value_aux_0),((lean_object*)&l_main___closed__504_value),LEAN_SCALAR_PTR_LITERAL(112, 161, 84, 85, 202, 147, 85, 175)}};
static const lean_ctor_object l_main___closed__547_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__547_value_aux_1),((lean_object*)&l_main___closed__546_value),LEAN_SCALAR_PTR_LITERAL(111, 47, 23, 243, 133, 137, 78, 242)}};
static const lean_object* l_main___closed__547 = (const lean_object*)&l_main___closed__547_value;
static const lean_array_object l_main___closed__548_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__540_value),((lean_object*)&l_main___closed__543_value),((lean_object*)&l_main___closed__545_value),((lean_object*)&l_main___closed__547_value)}};
static const lean_object* l_main___closed__548 = (const lean_object*)&l_main___closed__548_value;
static const lean_string_object l_main___closed__549_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_TraceResult"};
static const lean_object* l_main___closed__549 = (const lean_object*)&l_main___closed__549_value;
static const lean_string_object l_main___closed__550_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_pure"};
static const lean_object* l_main___closed__550 = (const lean_object*)&l_main___closed__550_value;
static const lean_ctor_object l_main___closed__551_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__551_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__551_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__551_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__551_value_aux_1),((lean_object*)&l_main___closed__550_value),LEAN_SCALAR_PTR_LITERAL(0, 54, 162, 74, 223, 242, 248, 137)}};
static const lean_object* l_main___closed__551 = (const lean_object*)&l_main___closed__551_value;
static const lean_string_object l_main___closed__552_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fail_prefix"};
static const lean_object* l_main___closed__552 = (const lean_object*)&l_main___closed__552_value;
static const lean_ctor_object l_main___closed__553_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__553_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__553_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__553_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__553_value_aux_1),((lean_object*)&l_main___closed__552_value),LEAN_SCALAR_PTR_LITERAL(148, 52, 2, 203, 44, 199, 228, 14)}};
static const lean_object* l_main___closed__553 = (const lean_object*)&l_main___closed__553_value;
static const lean_string_object l_main___closed__554_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "NFI_WrapperDomains"};
static const lean_object* l_main___closed__554 = (const lean_object*)&l_main___closed__554_value;
static const lean_ctor_object l_main___closed__555_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__555_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__555_value_aux_0),((lean_object*)&l_main___closed__554_value),LEAN_SCALAR_PTR_LITERAL(25, 232, 182, 77, 28, 85, 252, 251)}};
static const lean_ctor_object l_main___closed__555_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__555_value_aux_1),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(95, 174, 230, 152, 166, 73, 36, 117)}};
static const lean_object* l_main___closed__555 = (const lean_object*)&l_main___closed__555_value;
static const lean_ctor_object l_main___closed__556_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__556_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__556_value_aux_0),((lean_object*)&l_main___closed__538_value),LEAN_SCALAR_PTR_LITERAL(108, 62, 131, 135, 24, 53, 95, 21)}};
static const lean_ctor_object l_main___closed__556_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__556_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 80, 154, 43, 28, 133, 69)}};
static const lean_object* l_main___closed__556 = (const lean_object*)&l_main___closed__556_value;
static const lean_array_object l_main___closed__557_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__551_value),((lean_object*)&l_main___closed__553_value),((lean_object*)&l_main___closed__555_value),((lean_object*)&l_main___closed__556_value)}};
static const lean_object* l_main___closed__557 = (const lean_object*)&l_main___closed__557_value;
static const lean_string_object l_main___closed__558_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "div_prefix"};
static const lean_object* l_main___closed__558 = (const lean_object*)&l_main___closed__558_value;
static const lean_ctor_object l_main___closed__559_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__559_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__559_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__559_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__559_value_aux_1),((lean_object*)&l_main___closed__558_value),LEAN_SCALAR_PTR_LITERAL(21, 52, 77, 98, 180, 229, 144, 242)}};
static const lean_object* l_main___closed__559 = (const lean_object*)&l_main___closed__559_value;
static const lean_string_object l_main___closed__560_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_bind"};
static const lean_object* l_main___closed__560 = (const lean_object*)&l_main___closed__560_value;
static const lean_ctor_object l_main___closed__561_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__561_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__561_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__561_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__561_value_aux_1),((lean_object*)&l_main___closed__560_value),LEAN_SCALAR_PTR_LITERAL(132, 52, 163, 84, 164, 40, 235, 86)}};
static const lean_object* l_main___closed__561 = (const lean_object*)&l_main___closed__561_value;
static const lean_string_object l_main___closed__562_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_lift"};
static const lean_object* l_main___closed__562 = (const lean_object*)&l_main___closed__562_value;
static const lean_ctor_object l_main___closed__563_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__563_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__563_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__563_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__563_value_aux_1),((lean_object*)&l_main___closed__562_value),LEAN_SCALAR_PTR_LITERAL(81, 23, 212, 251, 142, 3, 166, 22)}};
static const lean_object* l_main___closed__563 = (const lean_object*)&l_main___closed__563_value;
static const lean_string_object l_main___closed__564_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "erase_mark"};
static const lean_object* l_main___closed__564 = (const lean_object*)&l_main___closed__564_value;
static const lean_ctor_object l_main___closed__565_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__565_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__565_value_aux_0),((lean_object*)&l_main___closed__549_value),LEAN_SCALAR_PTR_LITERAL(65, 95, 101, 95, 46, 131, 243, 202)}};
static const lean_ctor_object l_main___closed__565_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__565_value_aux_1),((lean_object*)&l_main___closed__564_value),LEAN_SCALAR_PTR_LITERAL(242, 17, 164, 78, 33, 83, 4, 86)}};
static const lean_object* l_main___closed__565 = (const lean_object*)&l_main___closed__565_value;
static const lean_array_object l_main___closed__566_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__559_value),((lean_object*)&l_main___closed__561_value),((lean_object*)&l_main___closed__563_value),((lean_object*)&l_main___closed__565_value)}};
static const lean_object* l_main___closed__566 = (const lean_object*)&l_main___closed__566_value;
static const lean_string_object l_main___closed__567_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_SingleTrace"};
static const lean_object* l_main___closed__567 = (const lean_object*)&l_main___closed__567_value;
static const lean_ctor_object l_main___closed__568_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__568_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__568_value_aux_0),((lean_object*)&l_main___closed__567_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__568_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__568_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(61, 26, 157, 130, 170, 242, 171, 144)}};
static const lean_object* l_main___closed__568 = (const lean_object*)&l_main___closed__568_value;
static const lean_string_object l_main___closed__569_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "main_erased"};
static const lean_object* l_main___closed__569 = (const lean_object*)&l_main___closed__569_value;
static const lean_ctor_object l_main___closed__570_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__570_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__570_value_aux_0),((lean_object*)&l_main___closed__567_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__570_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__570_value_aux_1),((lean_object*)&l_main___closed__569_value),LEAN_SCALAR_PTR_LITERAL(78, 226, 209, 160, 249, 49, 177, 170)}};
static const lean_object* l_main___closed__570 = (const lean_object*)&l_main___closed__570_value;
static const lean_string_object l_main___closed__571_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFI_TailTrace"};
static const lean_object* l_main___closed__571 = (const lean_object*)&l_main___closed__571_value;
static const lean_ctor_object l_main___closed__572_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__572_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__572_value_aux_0),((lean_object*)&l_main___closed__571_value),LEAN_SCALAR_PTR_LITERAL(4, 231, 152, 194, 252, 118, 242, 97)}};
static const lean_ctor_object l_main___closed__572_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__572_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(165, 0, 6, 167, 220, 113, 238, 100)}};
static const lean_object* l_main___closed__572 = (const lean_object*)&l_main___closed__572_value;
static const lean_ctor_object l_main___closed__573_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__573_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__573_value_aux_0),((lean_object*)&l_main___closed__571_value),LEAN_SCALAR_PTR_LITERAL(4, 231, 152, 194, 252, 118, 242, 97)}};
static const lean_ctor_object l_main___closed__573_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__573_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(166, 248, 148, 201, 3, 4, 50, 160)}};
static const lean_object* l_main___closed__573 = (const lean_object*)&l_main___closed__573_value;
static const lean_array_object l_main___closed__574_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__568_value),((lean_object*)&l_main___closed__570_value),((lean_object*)&l_main___closed__572_value),((lean_object*)&l_main___closed__573_value)}};
static const lean_object* l_main___closed__574 = (const lean_object*)&l_main___closed__574_value;
static const lean_string_object l_main___closed__575_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFI_OuterTrace"};
static const lean_object* l_main___closed__575 = (const lean_object*)&l_main___closed__575_value;
static const lean_string_object l_main___closed__576_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "replay"};
static const lean_object* l_main___closed__576 = (const lean_object*)&l_main___closed__576_value;
static const lean_ctor_object l_main___closed__577_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__577_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__577_value_aux_0),((lean_object*)&l_main___closed__575_value),LEAN_SCALAR_PTR_LITERAL(8, 118, 2, 4, 86, 237, 27, 215)}};
static const lean_ctor_object l_main___closed__577_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__577_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(234, 179, 17, 19, 116, 77, 238, 75)}};
static const lean_object* l_main___closed__577 = (const lean_object*)&l_main___closed__577_value;
static const lean_string_object l_main___closed__578_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_PrivateCuts"};
static const lean_object* l_main___closed__578 = (const lean_object*)&l_main___closed__578_value;
static const lean_ctor_object l_main___closed__579_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__579_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__579_value_aux_0),((lean_object*)&l_main___closed__578_value),LEAN_SCALAR_PTR_LITERAL(189, 98, 135, 203, 147, 60, 89, 216)}};
static const lean_ctor_object l_main___closed__579_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__579_value_aux_1),((lean_object*)&l_main___closed__216_value),LEAN_SCALAR_PTR_LITERAL(164, 251, 16, 63, 14, 2, 32, 56)}};
static const lean_object* l_main___closed__579 = (const lean_object*)&l_main___closed__579_value;
static const lean_string_object l_main___closed__580_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFI_SingleDomains"};
static const lean_object* l_main___closed__580 = (const lean_object*)&l_main___closed__580_value;
static const lean_ctor_object l_main___closed__581_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__581_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__581_value_aux_0),((lean_object*)&l_main___closed__580_value),LEAN_SCALAR_PTR_LITERAL(145, 179, 180, 57, 88, 75, 141, 19)}};
static const lean_ctor_object l_main___closed__581_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__581_value_aux_1),((lean_object*)&l_main___closed__406_value),LEAN_SCALAR_PTR_LITERAL(135, 62, 207, 187, 220, 244, 159, 114)}};
static const lean_object* l_main___closed__581 = (const lean_object*)&l_main___closed__581_value;
static const lean_ctor_object l_main___closed__582_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__582_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__582_value_aux_0),((lean_object*)&l_main___closed__567_value),LEAN_SCALAR_PTR_LITERAL(131, 123, 38, 146, 158, 123, 150, 43)}};
static const lean_ctor_object l_main___closed__582_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__582_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(14, 74, 27, 120, 132, 130, 101, 177)}};
static const lean_object* l_main___closed__582 = (const lean_object*)&l_main___closed__582_value;
static const lean_array_object l_main___closed__583_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__577_value),((lean_object*)&l_main___closed__579_value),((lean_object*)&l_main___closed__581_value),((lean_object*)&l_main___closed__582_value)}};
static const lean_object* l_main___closed__583 = (const lean_object*)&l_main___closed__583_value;
static const lean_string_object l_main___closed__584_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_OuterActual"};
static const lean_object* l_main___closed__584 = (const lean_object*)&l_main___closed__584_value;
static const lean_ctor_object l_main___closed__585_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__585_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__585_value_aux_0),((lean_object*)&l_main___closed__584_value),LEAN_SCALAR_PTR_LITERAL(77, 210, 129, 247, 118, 183, 212, 1)}};
static const lean_ctor_object l_main___closed__585_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__585_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(120, 143, 136, 115, 55, 174, 103, 186)}};
static const lean_object* l_main___closed__585 = (const lean_object*)&l_main___closed__585_value;
static const lean_string_object l_main___closed__586_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFI_OuterCut"};
static const lean_object* l_main___closed__586 = (const lean_object*)&l_main___closed__586_value;
static const lean_ctor_object l_main___closed__587_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__587_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__587_value_aux_0),((lean_object*)&l_main___closed__586_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 109, 171, 132, 5, 27, 67)}};
static const lean_ctor_object l_main___closed__587_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__587_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(178, 139, 75, 13, 4, 24, 238, 252)}};
static const lean_object* l_main___closed__587 = (const lean_object*)&l_main___closed__587_value;
static const lean_string_object l_main___closed__588_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "same_input"};
static const lean_object* l_main___closed__588 = (const lean_object*)&l_main___closed__588_value;
static const lean_ctor_object l_main___closed__589_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__589_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__589_value_aux_0),((lean_object*)&l_main___closed__586_value),LEAN_SCALAR_PTR_LITERAL(224, 171, 109, 171, 132, 5, 27, 67)}};
static const lean_ctor_object l_main___closed__589_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__589_value_aux_1),((lean_object*)&l_main___closed__588_value),LEAN_SCALAR_PTR_LITERAL(64, 132, 157, 37, 89, 91, 248, 180)}};
static const lean_object* l_main___closed__589 = (const lean_object*)&l_main___closed__589_value;
static const lean_string_object l_main___closed__590_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "frames"};
static const lean_object* l_main___closed__590 = (const lean_object*)&l_main___closed__590_value;
static const lean_ctor_object l_main___closed__591_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__591_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__591_value_aux_0),((lean_object*)&l_main___closed__575_value),LEAN_SCALAR_PTR_LITERAL(8, 118, 2, 4, 86, 237, 27, 215)}};
static const lean_ctor_object l_main___closed__591_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__591_value_aux_1),((lean_object*)&l_main___closed__590_value),LEAN_SCALAR_PTR_LITERAL(39, 31, 106, 231, 221, 14, 152, 56)}};
static const lean_object* l_main___closed__591 = (const lean_object*)&l_main___closed__591_value;
static const lean_array_object l_main___closed__592_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__585_value),((lean_object*)&l_main___closed__587_value),((lean_object*)&l_main___closed__589_value),((lean_object*)&l_main___closed__591_value)}};
static const lean_object* l_main___closed__592 = (const lean_object*)&l_main___closed__592_value;
static const lean_string_object l_main___closed__593_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFI_OpeningFrame"};
static const lean_object* l_main___closed__593 = (const lean_object*)&l_main___closed__593_value;
static const lean_string_object l_main___closed__594_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arbitrary_complement"};
static const lean_object* l_main___closed__594 = (const lean_object*)&l_main___closed__594_value;
static const lean_ctor_object l_main___closed__595_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__595_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__595_value_aux_0),((lean_object*)&l_main___closed__593_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__595_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__595_value_aux_1),((lean_object*)&l_main___closed__594_value),LEAN_SCALAR_PTR_LITERAL(206, 233, 40, 55, 182, 39, 125, 227)}};
static const lean_object* l_main___closed__595 = (const lean_object*)&l_main___closed__595_value;
static const lean_string_object l_main___closed__596_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "original_byte"};
static const lean_object* l_main___closed__596 = (const lean_object*)&l_main___closed__596_value;
static const lean_ctor_object l_main___closed__597_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__597_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__597_value_aux_0),((lean_object*)&l_main___closed__593_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__597_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__597_value_aux_1),((lean_object*)&l_main___closed__596_value),LEAN_SCALAR_PTR_LITERAL(127, 79, 70, 98, 221, 64, 84, 140)}};
static const lean_object* l_main___closed__597 = (const lean_object*)&l_main___closed__597_value;
static const lean_string_object l_main___closed__598_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "receiver_and_return_frame"};
static const lean_object* l_main___closed__598 = (const lean_object*)&l_main___closed__598_value;
static const lean_ctor_object l_main___closed__599_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__599_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__599_value_aux_0),((lean_object*)&l_main___closed__593_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__599_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__599_value_aux_1),((lean_object*)&l_main___closed__598_value),LEAN_SCALAR_PTR_LITERAL(54, 192, 35, 244, 227, 237, 210, 15)}};
static const lean_object* l_main___closed__599 = (const lean_object*)&l_main___closed__599_value;
static const lean_string_object l_main___closed__600_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "same_heap_frame"};
static const lean_object* l_main___closed__600 = (const lean_object*)&l_main___closed__600_value;
static const lean_ctor_object l_main___closed__601_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__601_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__601_value_aux_0),((lean_object*)&l_main___closed__593_value),LEAN_SCALAR_PTR_LITERAL(71, 255, 185, 230, 215, 219, 166, 101)}};
static const lean_ctor_object l_main___closed__601_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__601_value_aux_1),((lean_object*)&l_main___closed__600_value),LEAN_SCALAR_PTR_LITERAL(199, 192, 115, 116, 46, 133, 12, 191)}};
static const lean_object* l_main___closed__601 = (const lean_object*)&l_main___closed__601_value;
static const lean_array_object l_main___closed__602_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__595_value),((lean_object*)&l_main___closed__597_value),((lean_object*)&l_main___closed__599_value),((lean_object*)&l_main___closed__601_value)}};
static const lean_object* l_main___closed__602 = (const lean_object*)&l_main___closed__602_value;
static const lean_string_object l_main___closed__603_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFI_InnerCut"};
static const lean_object* l_main___closed__603 = (const lean_object*)&l_main___closed__603_value;
static const lean_ctor_object l_main___closed__604_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__604_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__604_value_aux_0),((lean_object*)&l_main___closed__603_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 141, 195, 90, 19, 102, 43)}};
static const lean_ctor_object l_main___closed__604_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__604_value_aux_1),((lean_object*)&l_main___closed__277_value),LEAN_SCALAR_PTR_LITERAL(98, 184, 69, 141, 2, 108, 194, 166)}};
static const lean_object* l_main___closed__604 = (const lean_object*)&l_main___closed__604_value;
static const lean_ctor_object l_main___closed__605_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__605_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__605_value_aux_0),((lean_object*)&l_main___closed__603_value),LEAN_SCALAR_PTR_LITERAL(208, 157, 141, 195, 90, 19, 102, 43)}};
static const lean_ctor_object l_main___closed__605_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__605_value_aux_1),((lean_object*)&l_main___closed__588_value),LEAN_SCALAR_PTR_LITERAL(48, 42, 211, 247, 201, 221, 50, 124)}};
static const lean_object* l_main___closed__605 = (const lean_object*)&l_main___closed__605_value;
static const lean_string_object l_main___closed__606_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFI_InnerTrace"};
static const lean_object* l_main___closed__606 = (const lean_object*)&l_main___closed__606_value;
static const lean_ctor_object l_main___closed__607_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__607_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__607_value_aux_0),((lean_object*)&l_main___closed__606_value),LEAN_SCALAR_PTR_LITERAL(137, 7, 11, 159, 52, 26, 77, 24)}};
static const lean_ctor_object l_main___closed__607_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__607_value_aux_1),((lean_object*)&l_main___closed__590_value),LEAN_SCALAR_PTR_LITERAL(18, 176, 48, 207, 229, 245, 223, 227)}};
static const lean_object* l_main___closed__607 = (const lean_object*)&l_main___closed__607_value;
static const lean_ctor_object l_main___closed__608_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__608_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__608_value_aux_0),((lean_object*)&l_main___closed__606_value),LEAN_SCALAR_PTR_LITERAL(137, 7, 11, 159, 52, 26, 77, 24)}};
static const lean_ctor_object l_main___closed__608_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__608_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(255, 45, 228, 219, 214, 7, 132, 57)}};
static const lean_object* l_main___closed__608 = (const lean_object*)&l_main___closed__608_value;
static const lean_array_object l_main___closed__609_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__604_value),((lean_object*)&l_main___closed__605_value),((lean_object*)&l_main___closed__607_value),((lean_object*)&l_main___closed__608_value)}};
static const lean_object* l_main___closed__609 = (const lean_object*)&l_main___closed__609_value;
static const lean_string_object l_main___closed__610_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFI_FailurePrefixes"};
static const lean_object* l_main___closed__610 = (const lean_object*)&l_main___closed__610_value;
static const lean_string_object l_main___closed__611_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "trace_prefix"};
static const lean_object* l_main___closed__611 = (const lean_object*)&l_main___closed__611_value;
static const lean_ctor_object l_main___closed__612_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__612_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__612_value_aux_0),((lean_object*)&l_main___closed__610_value),LEAN_SCALAR_PTR_LITERAL(101, 18, 190, 101, 2, 217, 219, 28)}};
static const lean_ctor_object l_main___closed__612_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__612_value_aux_1),((lean_object*)&l_main___closed__611_value),LEAN_SCALAR_PTR_LITERAL(166, 120, 11, 231, 192, 75, 149, 142)}};
static const lean_object* l_main___closed__612 = (const lean_object*)&l_main___closed__612_value;
static const lean_string_object l_main___closed__613_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFI_InnerActual"};
static const lean_object* l_main___closed__613 = (const lean_object*)&l_main___closed__613_value;
static const lean_string_object l_main___closed__614_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "borrowed_frame"};
static const lean_object* l_main___closed__614 = (const lean_object*)&l_main___closed__614_value;
static const lean_ctor_object l_main___closed__615_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__615_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__615_value_aux_0),((lean_object*)&l_main___closed__613_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__615_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__615_value_aux_1),((lean_object*)&l_main___closed__614_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 249, 51, 82, 48, 35, 7)}};
static const lean_object* l_main___closed__615 = (const lean_object*)&l_main___closed__615_value;
static const lean_string_object l_main___closed__616_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "canonical_at_cut"};
static const lean_object* l_main___closed__616 = (const lean_object*)&l_main___closed__616_value;
static const lean_ctor_object l_main___closed__617_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__617_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__617_value_aux_0),((lean_object*)&l_main___closed__613_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__617_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__617_value_aux_1),((lean_object*)&l_main___closed__616_value),LEAN_SCALAR_PTR_LITERAL(220, 117, 150, 134, 164, 227, 145, 108)}};
static const lean_object* l_main___closed__617 = (const lean_object*)&l_main___closed__617_value;
static const lean_ctor_object l_main___closed__618_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__618_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__618_value_aux_0),((lean_object*)&l_main___closed__613_value),LEAN_SCALAR_PTR_LITERAL(112, 71, 209, 227, 203, 253, 246, 80)}};
static const lean_ctor_object l_main___closed__618_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__618_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(9, 251, 44, 26, 241, 90, 249, 48)}};
static const lean_object* l_main___closed__618 = (const lean_object*)&l_main___closed__618_value;
static const lean_array_object l_main___closed__619_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__612_value),((lean_object*)&l_main___closed__615_value),((lean_object*)&l_main___closed__617_value),((lean_object*)&l_main___closed__618_value)}};
static const lean_object* l_main___closed__619 = (const lean_object*)&l_main___closed__619_value;
static const lean_string_object l_main___closed__620_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFG_QueryLoopSource"};
static const lean_object* l_main___closed__620 = (const lean_object*)&l_main___closed__620_value;
static const lean_ctor_object l_main___closed__621_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__621_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__621_value_aux_0),((lean_object*)&l_main___closed__620_value),LEAN_SCALAR_PTR_LITERAL(88, 59, 114, 222, 81, 236, 187, 161)}};
static const lean_ctor_object l_main___closed__621_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__621_value_aux_1),((lean_object*)&l_main___closed__198_value),LEAN_SCALAR_PTR_LITERAL(35, 213, 149, 102, 87, 98, 239, 70)}};
static const lean_object* l_main___closed__621 = (const lean_object*)&l_main___closed__621_value;
static const lean_string_object l_main___closed__622_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFG_SmallEffects"};
static const lean_object* l_main___closed__622 = (const lean_object*)&l_main___closed__622_value;
static const lean_string_object l_main___closed__623_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_main___closed__623 = (const lean_object*)&l_main___closed__623_value;
static const lean_ctor_object l_main___closed__624_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__624_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__624_value_aux_0),((lean_object*)&l_main___closed__622_value),LEAN_SCALAR_PTR_LITERAL(135, 135, 94, 9, 5, 176, 142, 54)}};
static const lean_ctor_object l_main___closed__624_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__624_value_aux_1),((lean_object*)&l_main___closed__623_value),LEAN_SCALAR_PTR_LITERAL(140, 240, 8, 196, 228, 5, 112, 199)}};
static const lean_object* l_main___closed__624 = (const lean_object*)&l_main___closed__624_value;
static const lean_ctor_object l_main___closed__625_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__625_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__625_value_aux_0),((lean_object*)&l_main___closed__622_value),LEAN_SCALAR_PTR_LITERAL(135, 135, 94, 9, 5, 176, 142, 54)}};
static const lean_ctor_object l_main___closed__625_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__625_value_aux_1),((lean_object*)&l_main___closed__192_value),LEAN_SCALAR_PTR_LITERAL(215, 34, 175, 153, 139, 254, 77, 216)}};
static const lean_object* l_main___closed__625 = (const lean_object*)&l_main___closed__625_value;
static const lean_ctor_object l_main___closed__626_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__626_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__626_value_aux_0),((lean_object*)&l_main___closed__610_value),LEAN_SCALAR_PTR_LITERAL(101, 18, 190, 101, 2, 217, 219, 28)}};
static const lean_ctor_object l_main___closed__626_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__626_value_aux_1),((lean_object*)&l_main___closed__384_value),LEAN_SCALAR_PTR_LITERAL(35, 125, 236, 110, 138, 18, 194, 0)}};
static const lean_object* l_main___closed__626 = (const lean_object*)&l_main___closed__626_value;
static const lean_array_object l_main___closed__627_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__621_value),((lean_object*)&l_main___closed__624_value),((lean_object*)&l_main___closed__625_value),((lean_object*)&l_main___closed__626_value)}};
static const lean_object* l_main___closed__627 = (const lean_object*)&l_main___closed__627_value;
static const lean_string_object l_main___closed__628_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFG_ProductOk"};
static const lean_object* l_main___closed__628 = (const lean_object*)&l_main___closed__628_value;
static const lean_ctor_object l_main___closed__629_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__629_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__629_value_aux_0),((lean_object*)&l_main___closed__628_value),LEAN_SCALAR_PTR_LITERAL(161, 26, 124, 238, 73, 13, 10, 250)}};
static const lean_ctor_object l_main___closed__629_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__629_value_aux_1),((lean_object*)&l_main___closed__238_value),LEAN_SCALAR_PTR_LITERAL(214, 144, 109, 103, 82, 225, 83, 116)}};
static const lean_object* l_main___closed__629 = (const lean_object*)&l_main___closed__629_value;
static const lean_string_object l_main___closed__630_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NFG_PushRoot"};
static const lean_object* l_main___closed__630 = (const lean_object*)&l_main___closed__630_value;
static const lean_string_object l_main___closed__631_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "private_domains"};
static const lean_object* l_main___closed__631 = (const lean_object*)&l_main___closed__631_value;
static const lean_ctor_object l_main___closed__632_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__632_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__632_value_aux_0),((lean_object*)&l_main___closed__630_value),LEAN_SCALAR_PTR_LITERAL(85, 13, 2, 171, 254, 60, 240, 22)}};
static const lean_ctor_object l_main___closed__632_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__632_value_aux_1),((lean_object*)&l_main___closed__631_value),LEAN_SCALAR_PTR_LITERAL(132, 45, 238, 185, 32, 111, 246, 136)}};
static const lean_object* l_main___closed__632 = (const lean_object*)&l_main___closed__632_value;
static const lean_string_object l_main___closed__633_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "private_result"};
static const lean_object* l_main___closed__633 = (const lean_object*)&l_main___closed__633_value;
static const lean_ctor_object l_main___closed__634_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__634_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__634_value_aux_0),((lean_object*)&l_main___closed__630_value),LEAN_SCALAR_PTR_LITERAL(85, 13, 2, 171, 254, 60, 240, 22)}};
static const lean_ctor_object l_main___closed__634_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__634_value_aux_1),((lean_object*)&l_main___closed__633_value),LEAN_SCALAR_PTR_LITERAL(155, 139, 182, 186, 62, 49, 38, 31)}};
static const lean_object* l_main___closed__634 = (const lean_object*)&l_main___closed__634_value;
static const lean_string_object l_main___closed__635_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public_result"};
static const lean_object* l_main___closed__635 = (const lean_object*)&l_main___closed__635_value;
static const lean_ctor_object l_main___closed__636_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__636_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__636_value_aux_0),((lean_object*)&l_main___closed__630_value),LEAN_SCALAR_PTR_LITERAL(85, 13, 2, 171, 254, 60, 240, 22)}};
static const lean_ctor_object l_main___closed__636_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__636_value_aux_1),((lean_object*)&l_main___closed__635_value),LEAN_SCALAR_PTR_LITERAL(49, 51, 175, 173, 11, 29, 130, 140)}};
static const lean_object* l_main___closed__636 = (const lean_object*)&l_main___closed__636_value;
static const lean_array_object l_main___closed__637_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__629_value),((lean_object*)&l_main___closed__632_value),((lean_object*)&l_main___closed__634_value),((lean_object*)&l_main___closed__636_value)}};
static const lean_object* l_main___closed__637 = (const lean_object*)&l_main___closed__637_value;
static const lean_string_object l_main___closed__638_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_RawTypedLog"};
static const lean_object* l_main___closed__638 = (const lean_object*)&l_main___closed__638_value;
static const lean_string_object l_main___closed__639_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "operands"};
static const lean_object* l_main___closed__639 = (const lean_object*)&l_main___closed__639_value;
static const lean_ctor_object l_main___closed__640_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__640_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__640_value_aux_0),((lean_object*)&l_main___closed__638_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__640_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__640_value_aux_1),((lean_object*)&l_main___closed__639_value),LEAN_SCALAR_PTR_LITERAL(135, 66, 146, 168, 212, 42, 105, 225)}};
static const lean_object* l_main___closed__640 = (const lean_object*)&l_main___closed__640_value;
static const lean_ctor_object l_main___closed__641_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__641_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__641_value_aux_0),((lean_object*)&l_main___closed__638_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__641_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__641_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(7, 77, 214, 252, 146, 120, 209, 89)}};
static const lean_object* l_main___closed__641 = (const lean_object*)&l_main___closed__641_value;
static const lean_string_object l_main___closed__642_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_ReadDomains"};
static const lean_object* l_main___closed__642 = (const lean_object*)&l_main___closed__642_value;
static const lean_ctor_object l_main___closed__643_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__643_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__643_value_aux_0),((lean_object*)&l_main___closed__642_value),LEAN_SCALAR_PTR_LITERAL(20, 16, 99, 141, 245, 60, 73, 254)}};
static const lean_ctor_object l_main___closed__643_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__643_value_aux_1),((lean_object*)&l_main___closed__438_value),LEAN_SCALAR_PTR_LITERAL(129, 69, 191, 201, 171, 254, 143, 228)}};
static const lean_object* l_main___closed__643 = (const lean_object*)&l_main___closed__643_value;
static const lean_string_object l_main___closed__644_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "selected"};
static const lean_object* l_main___closed__644 = (const lean_object*)&l_main___closed__644_value;
static const lean_ctor_object l_main___closed__645_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__645_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__645_value_aux_0),((lean_object*)&l_main___closed__642_value),LEAN_SCALAR_PTR_LITERAL(20, 16, 99, 141, 245, 60, 73, 254)}};
static const lean_ctor_object l_main___closed__645_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__645_value_aux_1),((lean_object*)&l_main___closed__644_value),LEAN_SCALAR_PTR_LITERAL(42, 142, 165, 201, 6, 101, 247, 250)}};
static const lean_object* l_main___closed__645 = (const lean_object*)&l_main___closed__645_value;
static const lean_array_object l_main___closed__646_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__640_value),((lean_object*)&l_main___closed__641_value),((lean_object*)&l_main___closed__643_value),((lean_object*)&l_main___closed__645_value)}};
static const lean_object* l_main___closed__646 = (const lean_object*)&l_main___closed__646_value;
static const lean_string_object l_main___closed__647_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NFF_RawLog"};
static const lean_object* l_main___closed__647 = (const lean_object*)&l_main___closed__647_value;
static const lean_string_object l_main___closed__648_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natural"};
static const lean_object* l_main___closed__648 = (const lean_object*)&l_main___closed__648_value;
static const lean_ctor_object l_main___closed__649_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__649_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__649_value_aux_0),((lean_object*)&l_main___closed__647_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__649_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__649_value_aux_1),((lean_object*)&l_main___closed__648_value),LEAN_SCALAR_PTR_LITERAL(76, 182, 234, 141, 227, 195, 71, 191)}};
static const lean_object* l_main___closed__649 = (const lean_object*)&l_main___closed__649_value;
static const lean_ctor_object l_main___closed__650_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__650_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__650_value_aux_0),((lean_object*)&l_main___closed__647_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__650_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__650_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(14, 152, 225, 79, 207, 165, 40, 65)}};
static const lean_object* l_main___closed__650 = (const lean_object*)&l_main___closed__650_value;
static const lean_string_object l_main___closed__651_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "same_log"};
static const lean_object* l_main___closed__651 = (const lean_object*)&l_main___closed__651_value;
static const lean_ctor_object l_main___closed__652_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__652_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__652_value_aux_0),((lean_object*)&l_main___closed__647_value),LEAN_SCALAR_PTR_LITERAL(156, 123, 179, 156, 19, 42, 242, 216)}};
static const lean_ctor_object l_main___closed__652_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__652_value_aux_1),((lean_object*)&l_main___closed__651_value),LEAN_SCALAR_PTR_LITERAL(116, 64, 109, 93, 5, 183, 193, 164)}};
static const lean_object* l_main___closed__652 = (const lean_object*)&l_main___closed__652_value;
static const lean_ctor_object l_main___closed__653_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__653_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__653_value_aux_0),((lean_object*)&l_main___closed__638_value),LEAN_SCALAR_PTR_LITERAL(225, 86, 170, 118, 229, 43, 73, 234)}};
static const lean_ctor_object l_main___closed__653_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__653_value_aux_1),((lean_object*)&l_main___closed__438_value),LEAN_SCALAR_PTR_LITERAL(104, 87, 122, 181, 117, 124, 197, 119)}};
static const lean_object* l_main___closed__653 = (const lean_object*)&l_main___closed__653_value;
static const lean_array_object l_main___closed__654_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__649_value),((lean_object*)&l_main___closed__650_value),((lean_object*)&l_main___closed__652_value),((lean_object*)&l_main___closed__653_value)}};
static const lean_object* l_main___closed__654 = (const lean_object*)&l_main___closed__654_value;
static const lean_string_object l_main___closed__655_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_LoggedWrapper"};
static const lean_object* l_main___closed__655 = (const lean_object*)&l_main___closed__655_value;
static const lean_ctor_object l_main___closed__656_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__656_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__656_value_aux_0),((lean_object*)&l_main___closed__655_value),LEAN_SCALAR_PTR_LITERAL(73, 209, 125, 72, 224, 37, 185, 37)}};
static const lean_ctor_object l_main___closed__656_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__656_value_aux_1),((lean_object*)&l_main___closed__539_value),LEAN_SCALAR_PTR_LITERAL(212, 162, 139, 9, 179, 60, 229, 246)}};
static const lean_object* l_main___closed__656 = (const lean_object*)&l_main___closed__656_value;
static const lean_ctor_object l_main___closed__657_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__657_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__657_value_aux_0),((lean_object*)&l_main___closed__655_value),LEAN_SCALAR_PTR_LITERAL(73, 209, 125, 72, 224, 37, 185, 37)}};
static const lean_ctor_object l_main___closed__657_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__657_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(63, 89, 80, 39, 31, 102, 170, 240)}};
static const lean_object* l_main___closed__657 = (const lean_object*)&l_main___closed__657_value;
static const lean_string_object l_main___closed__658_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_ProductCall"};
static const lean_object* l_main___closed__658 = (const lean_object*)&l_main___closed__658_value;
static const lean_ctor_object l_main___closed__659_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__659_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__659_value_aux_0),((lean_object*)&l_main___closed__658_value),LEAN_SCALAR_PTR_LITERAL(142, 228, 132, 23, 103, 2, 148, 55)}};
static const lean_ctor_object l_main___closed__659_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__659_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(148, 182, 96, 132, 240, 142, 198, 70)}};
static const lean_object* l_main___closed__659 = (const lean_object*)&l_main___closed__659_value;
static const lean_string_object l_main___closed__660_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFF_QueryProduct"};
static const lean_object* l_main___closed__660 = (const lean_object*)&l_main___closed__660_value;
static const lean_ctor_object l_main___closed__661_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__661_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__661_value_aux_0),((lean_object*)&l_main___closed__660_value),LEAN_SCALAR_PTR_LITERAL(12, 135, 44, 229, 33, 168, 124, 190)}};
static const lean_ctor_object l_main___closed__661_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__661_value_aux_1),((lean_object*)&l_main___closed__361_value),LEAN_SCALAR_PTR_LITERAL(77, 45, 9, 231, 125, 16, 2, 172)}};
static const lean_object* l_main___closed__661 = (const lean_object*)&l_main___closed__661_value;
static const lean_array_object l_main___closed__662_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__656_value),((lean_object*)&l_main___closed__657_value),((lean_object*)&l_main___closed__659_value),((lean_object*)&l_main___closed__661_value)}};
static const lean_object* l_main___closed__662 = (const lean_object*)&l_main___closed__662_value;
static const lean_string_object l_main___closed__663_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFF_LoggedRaw"};
static const lean_object* l_main___closed__663 = (const lean_object*)&l_main___closed__663_value;
static const lean_ctor_object l_main___closed__664_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__664_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__664_value_aux_0),((lean_object*)&l_main___closed__663_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 187, 109, 99, 51, 126, 174)}};
static const lean_ctor_object l_main___closed__664_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__664_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(133, 223, 8, 68, 65, 103, 154, 125)}};
static const lean_object* l_main___closed__664 = (const lean_object*)&l_main___closed__664_value;
static const lean_string_object l_main___closed__665_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedStep"};
static const lean_object* l_main___closed__665 = (const lean_object*)&l_main___closed__665_value;
static const lean_ctor_object l_main___closed__666_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__666_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__666_value_aux_0),((lean_object*)&l_main___closed__665_value),LEAN_SCALAR_PTR_LITERAL(166, 134, 206, 222, 20, 145, 99, 64)}};
static const lean_ctor_object l_main___closed__666_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__666_value_aux_1),((lean_object*)&l_main___closed__255_value),LEAN_SCALAR_PTR_LITERAL(112, 206, 112, 91, 179, 105, 101, 83)}};
static const lean_object* l_main___closed__666 = (const lean_object*)&l_main___closed__666_value;
static const lean_string_object l_main___closed__667_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "update_replay"};
static const lean_object* l_main___closed__667 = (const lean_object*)&l_main___closed__667_value;
static const lean_ctor_object l_main___closed__668_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__668_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__668_value_aux_0),((lean_object*)&l_main___closed__665_value),LEAN_SCALAR_PTR_LITERAL(166, 134, 206, 222, 20, 145, 99, 64)}};
static const lean_ctor_object l_main___closed__668_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__668_value_aux_1),((lean_object*)&l_main___closed__667_value),LEAN_SCALAR_PTR_LITERAL(93, 105, 20, 51, 229, 47, 71, 67)}};
static const lean_object* l_main___closed__668 = (const lean_object*)&l_main___closed__668_value;
static const lean_string_object l_main___closed__669_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedTail"};
static const lean_object* l_main___closed__669 = (const lean_object*)&l_main___closed__669_value;
static const lean_ctor_object l_main___closed__670_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__670_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__670_value_aux_0),((lean_object*)&l_main___closed__669_value),LEAN_SCALAR_PTR_LITERAL(207, 173, 189, 88, 177, 37, 16, 19)}};
static const lean_ctor_object l_main___closed__670_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__670_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(233, 61, 74, 4, 216, 92, 73, 72)}};
static const lean_object* l_main___closed__670 = (const lean_object*)&l_main___closed__670_value;
static const lean_array_object l_main___closed__671_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__664_value),((lean_object*)&l_main___closed__666_value),((lean_object*)&l_main___closed__668_value),((lean_object*)&l_main___closed__670_value)}};
static const lean_object* l_main___closed__671 = (const lean_object*)&l_main___closed__671_value;
static const lean_string_object l_main___closed__672_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFF_LoggedOuterStep"};
static const lean_object* l_main___closed__672 = (const lean_object*)&l_main___closed__672_value;
static const lean_ctor_object l_main___closed__673_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__673_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__673_value_aux_0),((lean_object*)&l_main___closed__672_value),LEAN_SCALAR_PTR_LITERAL(148, 21, 130, 45, 156, 30, 140, 40)}};
static const lean_ctor_object l_main___closed__673_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__673_value_aux_1),((lean_object*)&l_main___closed__386_value),LEAN_SCALAR_PTR_LITERAL(50, 126, 68, 84, 237, 125, 113, 195)}};
static const lean_object* l_main___closed__673 = (const lean_object*)&l_main___closed__673_value;
static const lean_string_object l_main___closed__674_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedPush"};
static const lean_object* l_main___closed__674 = (const lean_object*)&l_main___closed__674_value;
static const lean_string_object l_main___closed__675_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "private_replay"};
static const lean_object* l_main___closed__675 = (const lean_object*)&l_main___closed__675_value;
static const lean_ctor_object l_main___closed__676_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__676_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__676_value_aux_0),((lean_object*)&l_main___closed__674_value),LEAN_SCALAR_PTR_LITERAL(121, 180, 87, 35, 209, 192, 221, 181)}};
static const lean_ctor_object l_main___closed__676_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__676_value_aux_1),((lean_object*)&l_main___closed__675_value),LEAN_SCALAR_PTR_LITERAL(168, 70, 104, 218, 61, 144, 195, 211)}};
static const lean_object* l_main___closed__676 = (const lean_object*)&l_main___closed__676_value;
static const lean_string_object l_main___closed__677_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public_replay"};
static const lean_object* l_main___closed__677 = (const lean_object*)&l_main___closed__677_value;
static const lean_ctor_object l_main___closed__678_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__678_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__678_value_aux_0),((lean_object*)&l_main___closed__674_value),LEAN_SCALAR_PTR_LITERAL(121, 180, 87, 35, 209, 192, 221, 181)}};
static const lean_ctor_object l_main___closed__678_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__678_value_aux_1),((lean_object*)&l_main___closed__677_value),LEAN_SCALAR_PTR_LITERAL(66, 7, 33, 227, 225, 81, 185, 245)}};
static const lean_object* l_main___closed__678 = (const lean_object*)&l_main___closed__678_value;
static const lean_ctor_object l_main___closed__679_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__679_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__679_value_aux_0),((lean_object*)&l_main___closed__663_value),LEAN_SCALAR_PTR_LITERAL(251, 217, 187, 109, 99, 51, 126, 174)}};
static const lean_ctor_object l_main___closed__679_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__679_value_aux_1),((lean_object*)&l_main___closed__539_value),LEAN_SCALAR_PTR_LITERAL(110, 207, 7, 126, 159, 133, 60, 190)}};
static const lean_object* l_main___closed__679 = (const lean_object*)&l_main___closed__679_value;
static const lean_array_object l_main___closed__680_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__673_value),((lean_object*)&l_main___closed__676_value),((lean_object*)&l_main___closed__678_value),((lean_object*)&l_main___closed__679_value)}};
static const lean_object* l_main___closed__680 = (const lean_object*)&l_main___closed__680_value;
static const lean_string_object l_main___closed__681_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NFF_LoggedLoop"};
static const lean_object* l_main___closed__681 = (const lean_object*)&l_main___closed__681_value;
static const lean_ctor_object l_main___closed__682_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__682_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__682_value_aux_0),((lean_object*)&l_main___closed__681_value),LEAN_SCALAR_PTR_LITERAL(186, 99, 211, 216, 149, 255, 96, 20)}};
static const lean_ctor_object l_main___closed__682_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__682_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(48, 73, 57, 165, 103, 103, 36, 175)}};
static const lean_object* l_main___closed__682 = (const lean_object*)&l_main___closed__682_value;
static const lean_string_object l_main___closed__683_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFF_LoggedOne"};
static const lean_object* l_main___closed__683 = (const lean_object*)&l_main___closed__683_value;
static const lean_ctor_object l_main___closed__684_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__684_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__684_value_aux_0),((lean_object*)&l_main___closed__683_value),LEAN_SCALAR_PTR_LITERAL(23, 173, 85, 152, 243, 194, 49, 246)}};
static const lean_ctor_object l_main___closed__684_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__684_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(161, 83, 95, 14, 109, 100, 11, 2)}};
static const lean_object* l_main___closed__684 = (const lean_object*)&l_main___closed__684_value;
static const lean_string_object l_main___closed__685_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NFF_LoggedOuterLoop"};
static const lean_object* l_main___closed__685 = (const lean_object*)&l_main___closed__685_value;
static const lean_ctor_object l_main___closed__686_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__686_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__686_value_aux_0),((lean_object*)&l_main___closed__685_value),LEAN_SCALAR_PTR_LITERAL(75, 181, 148, 102, 119, 146, 80, 84)}};
static const lean_ctor_object l_main___closed__686_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__686_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(21, 186, 247, 122, 2, 162, 159, 69)}};
static const lean_object* l_main___closed__686 = (const lean_object*)&l_main___closed__686_value;
static const lean_ctor_object l_main___closed__687_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__687_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__687_value_aux_0),((lean_object*)&l_main___closed__672_value),LEAN_SCALAR_PTR_LITERAL(148, 21, 130, 45, 156, 30, 140, 40)}};
static const lean_ctor_object l_main___closed__687_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__687_value_aux_1),((lean_object*)&l_main___closed__255_value),LEAN_SCALAR_PTR_LITERAL(170, 196, 98, 68, 56, 229, 108, 245)}};
static const lean_object* l_main___closed__687 = (const lean_object*)&l_main___closed__687_value;
static const lean_array_object l_main___closed__688_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__682_value),((lean_object*)&l_main___closed__684_value),((lean_object*)&l_main___closed__686_value),((lean_object*)&l_main___closed__687_value)}};
static const lean_object* l_main___closed__688 = (const lean_object*)&l_main___closed__688_value;
static const lean_string_object l_main___closed__689_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_LoggedDomains"};
static const lean_object* l_main___closed__689 = (const lean_object*)&l_main___closed__689_value;
static const lean_string_object l_main___closed__690_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "four"};
static const lean_object* l_main___closed__690 = (const lean_object*)&l_main___closed__690_value;
static const lean_ctor_object l_main___closed__691_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__691_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__691_value_aux_0),((lean_object*)&l_main___closed__689_value),LEAN_SCALAR_PTR_LITERAL(16, 148, 160, 32, 220, 222, 109, 183)}};
static const lean_ctor_object l_main___closed__691_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__691_value_aux_1),((lean_object*)&l_main___closed__690_value),LEAN_SCALAR_PTR_LITERAL(3, 173, 209, 219, 100, 130, 71, 101)}};
static const lean_object* l_main___closed__691 = (const lean_object*)&l_main___closed__691_value;
static const lean_string_object l_main___closed__692_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_main___closed__692 = (const lean_object*)&l_main___closed__692_value;
static const lean_ctor_object l_main___closed__693_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__693_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__693_value_aux_0),((lean_object*)&l_main___closed__689_value),LEAN_SCALAR_PTR_LITERAL(16, 148, 160, 32, 220, 222, 109, 183)}};
static const lean_ctor_object l_main___closed__693_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__693_value_aux_1),((lean_object*)&l_main___closed__692_value),LEAN_SCALAR_PTR_LITERAL(96, 244, 64, 92, 69, 230, 194, 112)}};
static const lean_object* l_main___closed__693 = (const lean_object*)&l_main___closed__693_value;
static const lean_string_object l_main___closed__694_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_LoggedEight"};
static const lean_object* l_main___closed__694 = (const lean_object*)&l_main___closed__694_value;
static const lean_string_object l_main___closed__695_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cell_replay"};
static const lean_object* l_main___closed__695 = (const lean_object*)&l_main___closed__695_value;
static const lean_ctor_object l_main___closed__696_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__696_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__696_value_aux_0),((lean_object*)&l_main___closed__694_value),LEAN_SCALAR_PTR_LITERAL(68, 120, 197, 213, 127, 179, 11, 77)}};
static const lean_ctor_object l_main___closed__696_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__696_value_aux_1),((lean_object*)&l_main___closed__695_value),LEAN_SCALAR_PTR_LITERAL(121, 134, 180, 163, 179, 11, 81, 78)}};
static const lean_object* l_main___closed__696 = (const lean_object*)&l_main___closed__696_value;
static const lean_ctor_object l_main___closed__697_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__697_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__697_value_aux_0),((lean_object*)&l_main___closed__694_value),LEAN_SCALAR_PTR_LITERAL(68, 120, 197, 213, 127, 179, 11, 77)}};
static const lean_ctor_object l_main___closed__697_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__697_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(166, 111, 119, 169, 197, 99, 171, 152)}};
static const lean_object* l_main___closed__697 = (const lean_object*)&l_main___closed__697_value;
static const lean_array_object l_main___closed__698_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__691_value),((lean_object*)&l_main___closed__693_value),((lean_object*)&l_main___closed__696_value),((lean_object*)&l_main___closed__697_value)}};
static const lean_object* l_main___closed__698 = (const lean_object*)&l_main___closed__698_value;
static const lean_string_object l_main___closed__699_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFF_CoreReduction"};
static const lean_object* l_main___closed__699 = (const lean_object*)&l_main___closed__699_value;
static const lean_ctor_object l_main___closed__700_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__700_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__700_value_aux_0),((lean_object*)&l_main___closed__699_value),LEAN_SCALAR_PTR_LITERAL(12, 126, 227, 112, 249, 85, 34, 37)}};
static const lean_ctor_object l_main___closed__700_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__700_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(166, 171, 119, 132, 12, 138, 26, 31)}};
static const lean_object* l_main___closed__700 = (const lean_object*)&l_main___closed__700_value;
static const lean_string_object l_main___closed__701_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NFF_FullOne"};
static const lean_object* l_main___closed__701 = (const lean_object*)&l_main___closed__701_value;
static const lean_ctor_object l_main___closed__702_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__702_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__702_value_aux_0),((lean_object*)&l_main___closed__701_value),LEAN_SCALAR_PTR_LITERAL(148, 82, 37, 38, 223, 114, 24, 172)}};
static const lean_ctor_object l_main___closed__702_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__702_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(182, 129, 194, 232, 243, 17, 14, 137)}};
static const lean_object* l_main___closed__702 = (const lean_object*)&l_main___closed__702_value;
static const lean_string_object l_main___closed__703_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFF_FullWrapper"};
static const lean_object* l_main___closed__703 = (const lean_object*)&l_main___closed__703_value;
static const lean_ctor_object l_main___closed__704_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__704_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__704_value_aux_0),((lean_object*)&l_main___closed__703_value),LEAN_SCALAR_PTR_LITERAL(215, 28, 127, 186, 250, 168, 228, 167)}};
static const lean_ctor_object l_main___closed__704_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__704_value_aux_1),((lean_object*)&l_main___closed__539_value),LEAN_SCALAR_PTR_LITERAL(34, 108, 222, 12, 74, 200, 81, 62)}};
static const lean_object* l_main___closed__704 = (const lean_object*)&l_main___closed__704_value;
static const lean_ctor_object l_main___closed__705_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__705_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__705_value_aux_0),((lean_object*)&l_main___closed__703_value),LEAN_SCALAR_PTR_LITERAL(215, 28, 127, 186, 250, 168, 228, 167)}};
static const lean_ctor_object l_main___closed__705_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__705_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(225, 72, 246, 189, 106, 159, 81, 158)}};
static const lean_object* l_main___closed__705 = (const lean_object*)&l_main___closed__705_value;
static const lean_array_object l_main___closed__706_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__700_value),((lean_object*)&l_main___closed__702_value),((lean_object*)&l_main___closed__704_value),((lean_object*)&l_main___closed__705_value)}};
static const lean_object* l_main___closed__706 = (const lean_object*)&l_main___closed__706_value;
static const lean_string_object l_main___closed__707_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "NFF_BaseMultiply"};
static const lean_object* l_main___closed__707 = (const lean_object*)&l_main___closed__707_value;
static const lean_string_object l_main___closed__708_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "word_product"};
static const lean_object* l_main___closed__708 = (const lean_object*)&l_main___closed__708_value;
static const lean_ctor_object l_main___closed__709_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__709_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__709_value_aux_0),((lean_object*)&l_main___closed__707_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__709_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__709_value_aux_1),((lean_object*)&l_main___closed__708_value),LEAN_SCALAR_PTR_LITERAL(59, 155, 210, 33, 254, 7, 108, 147)}};
static const lean_object* l_main___closed__709 = (const lean_object*)&l_main___closed__709_value;
static const lean_string_object l_main___closed__710_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NFF_Cell"};
static const lean_object* l_main___closed__710 = (const lean_object*)&l_main___closed__710_value;
static const lean_string_object l_main___closed__711_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "primitive_reply"};
static const lean_object* l_main___closed__711 = (const lean_object*)&l_main___closed__711_value;
static const lean_ctor_object l_main___closed__712_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__712_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__712_value_aux_0),((lean_object*)&l_main___closed__710_value),LEAN_SCALAR_PTR_LITERAL(128, 0, 184, 35, 50, 111, 115, 54)}};
static const lean_ctor_object l_main___closed__712_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__712_value_aux_1),((lean_object*)&l_main___closed__711_value),LEAN_SCALAR_PTR_LITERAL(190, 107, 87, 73, 62, 118, 131, 147)}};
static const lean_object* l_main___closed__712 = (const lean_object*)&l_main___closed__712_value;
static const lean_ctor_object l_main___closed__713_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__713_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__713_value_aux_0),((lean_object*)&l_main___closed__710_value),LEAN_SCALAR_PTR_LITERAL(128, 0, 184, 35, 50, 111, 115, 54)}};
static const lean_ctor_object l_main___closed__713_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__713_value_aux_1),((lean_object*)&l_main___closed__576_value),LEAN_SCALAR_PTR_LITERAL(18, 252, 70, 209, 2, 116, 227, 57)}};
static const lean_object* l_main___closed__713 = (const lean_object*)&l_main___closed__713_value;
static const lean_ctor_object l_main___closed__714_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__714_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__714_value_aux_0),((lean_object*)&l_main___closed__699_value),LEAN_SCALAR_PTR_LITERAL(12, 126, 227, 112, 249, 85, 34, 37)}};
static const lean_ctor_object l_main___closed__714_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__714_value_aux_1),((lean_object*)&l_main___closed__460_value),LEAN_SCALAR_PTR_LITERAL(20, 74, 193, 122, 239, 44, 196, 48)}};
static const lean_object* l_main___closed__714 = (const lean_object*)&l_main___closed__714_value;
static const lean_array_object l_main___closed__715_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__709_value),((lean_object*)&l_main___closed__712_value),((lean_object*)&l_main___closed__713_value),((lean_object*)&l_main___closed__714_value)}};
static const lean_object* l_main___closed__715 = (const lean_object*)&l_main___closed__715_value;
static const lean_string_object l_main___closed__716_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NFE_DotBridge"};
static const lean_object* l_main___closed__716 = (const lean_object*)&l_main___closed__716_value;
static const lean_ctor_object l_main___closed__717_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__717_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__717_value_aux_0),((lean_object*)&l_main___closed__716_value),LEAN_SCALAR_PTR_LITERAL(196, 85, 115, 203, 129, 162, 182, 230)}};
static const lean_ctor_object l_main___closed__717_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__717_value_aux_1),((lean_object*)&l_main___closed__692_value),LEAN_SCALAR_PTR_LITERAL(68, 217, 118, 251, 9, 206, 68, 35)}};
static const lean_object* l_main___closed__717 = (const lean_object*)&l_main___closed__717_value;
static const lean_string_object l_main___closed__718_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NFE_WrapperBridge"};
static const lean_object* l_main___closed__718 = (const lean_object*)&l_main___closed__718_value;
static const lean_ctor_object l_main___closed__719_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__719_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__719_value_aux_0),((lean_object*)&l_main___closed__718_value),LEAN_SCALAR_PTR_LITERAL(193, 8, 198, 52, 196, 97, 243, 20)}};
static const lean_ctor_object l_main___closed__719_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__719_value_aux_1),((lean_object*)&l_main___closed__690_value),LEAN_SCALAR_PTR_LITERAL(222, 125, 100, 106, 166, 221, 233, 53)}};
static const lean_object* l_main___closed__719 = (const lean_object*)&l_main___closed__719_value;
static const lean_string_object l_main___closed__720_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "product_bound"};
static const lean_object* l_main___closed__720 = (const lean_object*)&l_main___closed__720_value;
static const lean_ctor_object l_main___closed__721_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__721_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__721_value_aux_0),((lean_object*)&l_main___closed__707_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__721_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__721_value_aux_1),((lean_object*)&l_main___closed__720_value),LEAN_SCALAR_PTR_LITERAL(125, 149, 230, 231, 156, 185, 249, 245)}};
static const lean_object* l_main___closed__721 = (const lean_object*)&l_main___closed__721_value;
static const lean_ctor_object l_main___closed__722_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__201_value),LEAN_SCALAR_PTR_LITERAL(202, 163, 186, 119, 233, 146, 49, 43)}};
static const lean_ctor_object l_main___closed__722_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__722_value_aux_0),((lean_object*)&l_main___closed__707_value),LEAN_SCALAR_PTR_LITERAL(55, 160, 201, 161, 18, 163, 168, 112)}};
static const lean_ctor_object l_main___closed__722_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__722_value_aux_1),((lean_object*)&l_main___closed__152_value),LEAN_SCALAR_PTR_LITERAL(89, 171, 227, 195, 108, 177, 191, 65)}};
static const lean_object* l_main___closed__722 = (const lean_object*)&l_main___closed__722_value;
static const lean_array_object l_main___closed__723_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_main___closed__717_value),((lean_object*)&l_main___closed__719_value),((lean_object*)&l_main___closed__721_value),((lean_object*)&l_main___closed__722_value)}};
static const lean_object* l_main___closed__723 = (const lean_object*)&l_main___closed__723_value;
static const lean_string_object l_main___closed__724_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__724 = (const lean_object*)&l_main___closed__724_value;
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
uint32_t v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = 1;
v___x_2751_ = lean_box_uint32(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = 0;
v___x_2753_ = lean_box_uint32(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = 2;
v___x_2755_ = lean_box_uint32(v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2756_){
_start:
{
uint8_t v___y_2759_; uint32_t v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2785_; uint32_t v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2805_; size_t v___y_2806_; lean_object* v___y_2807_; uint32_t v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2836_; size_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; uint32_t v___y_2840_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = l_NFA__MemoryLimit_set();
v___x_2848_ = ((lean_object*)(l_main___closed__7));
v___x_2849_ = l_Lean_findSysroot(v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = lean_box(0);
v___x_2852_ = l_Lean_initSearchPath(v_a_2850_, v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref_known(v___x_2852_, 1);
v___x_2853_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___y_2855_; lean_object* v_fst_2856_; lean_object* v_snd_2857_; lean_object* v___y_2939_; 
lean_dec_ref_known(v___x_2853_, 1);
if (lean_obj_tag(v_args_2756_) == 0)
{
lean_object* v___x_3209_; 
v___x_3209_ = ((lean_object*)(l_main___closed__724));
v___y_2939_ = v___x_3209_;
goto v___jp_2938_;
}
else
{
lean_object* v_head_3210_; 
v_head_3210_ = lean_ctor_get(v_args_2756_, 0);
lean_inc(v_head_3210_);
lean_dec_ref_known(v_args_2756_, 2);
v___y_2939_ = v_head_3210_;
goto v___jp_2938_;
}
v___jp_2854_:
{
size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint32_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; uint8_t v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_sz_2858_ = lean_array_size(v_fst_2856_);
v___x_2859_ = ((size_t)0ULL);
lean_inc_ref(v_fst_2856_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_2858_, v___x_2859_, v_fst_2856_);
v___x_2861_ = l_Lean_Options_empty;
v___x_2862_ = 0;
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = ((lean_object*)(l_main___closed__8));
v___x_2865_ = 0;
v___x_2866_ = 1;
v___x_2867_ = 2;
v___x_2868_ = lean_box(1);
v___x_2869_ = l_Lean_importModules(v___x_2860_, v___x_2861_, v___x_2862_, v___x_2864_, v___x_2865_, v___x_2866_, v___x_2867_, v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = ((lean_object*)(l_main___closed__9));
v___x_2872_ = lean_string_dec_eq(v___y_2855_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_2874_ = lean_string_dec_eq(v___y_2855_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; size_t v_sz_2879_; lean_object* v___x_2880_; 
v___x_2875_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_2876_ = lean_obj_once(&l_main___closed__16, &l_main___closed__16_once, _init_l_main___closed__16);
v___x_2877_ = l_Lean_Elab_Command_mkState(v_a_2870_, v___x_2876_, v___x_2861_);
v___x_2878_ = lean_st_mk_ref(v___x_2877_);
v_sz_2879_ = lean_array_size(v_snd_2857_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_2855_, v_snd_2857_, v_sz_2879_, v___x_2859_, v___x_2865_, v___x_2875_, v___x_2878_);
lean_dec_ref(v___y_2855_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; lean_object* v_messages_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = lean_st_ref_get(v___x_2878_);
lean_dec(v___x_2878_);
v_messages_2883_ = lean_ctor_get(v___x_2882_, 1);
lean_inc_ref(v_messages_2883_);
lean_dec(v___x_2882_);
v___x_2884_ = l_Lean_MessageLog_toList(v_messages_2883_);
lean_dec_ref(v_messages_2883_);
v___x_2885_ = lean_box(0);
v___x_2886_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v___x_2884_, v___x_2885_);
lean_dec(v___x_2884_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2886_, 0);
lean_dec(v_unused_2900_);
v___x_2888_ = v___x_2886_;
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v___x_2886_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_unbox(v_a_2881_);
lean_dec(v_a_2881_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2891_ = l_main___boxed__const__2;
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2891_);
v___x_2893_ = v___x_2888_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_main___boxed__const__1;
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2895_);
v___x_2897_ = v___x_2888_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_a_2881_);
v_a_2901_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2886_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2886_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec(v___x_2878_);
v_a_2909_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2910_ = l_Lean_Exception_toMessageData(v_a_2909_);
v___x_2911_ = l_Lean_MessageData_toString(v___x_2910_);
v___x_2912_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2911_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2921_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_main___boxed__const__3;
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_a_2922_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2912_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
else
{
v___y_2836_ = v___y_2855_;
v___y_2837_ = v___x_2859_;
v___y_2838_ = v_a_2870_;
v___y_2839_ = v___x_2863_;
v___y_2840_ = v___x_2862_;
goto v___jp_2835_;
}
}
else
{
v___y_2836_ = v___y_2855_;
v___y_2837_ = v___x_2859_;
v___y_2838_ = v_a_2870_;
v___y_2839_ = v___x_2863_;
v___y_2840_ = v___x_2862_;
goto v___jp_2835_;
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v___y_2855_);
v_a_2930_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2869_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2869_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
v___jp_2938_:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = ((lean_object*)(l_main___closed__17));
v___x_2941_ = lean_string_dec_eq(v___y_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_main___closed__18));
v___x_2943_ = lean_string_dec_eq(v___y_2939_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = ((lean_object*)(l_main___closed__19));
v___x_2945_ = lean_string_dec_eq(v___y_2939_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_main___closed__20));
v___x_2947_ = lean_string_dec_eq(v___y_2939_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = ((lean_object*)(l_main___closed__21));
v___x_2949_ = lean_string_dec_eq(v___y_2939_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_main___closed__22));
v___x_2951_ = lean_string_dec_eq(v___y_2939_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_main___closed__23));
v___x_2953_ = lean_string_dec_eq(v___y_2939_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = ((lean_object*)(l_main___closed__24));
v___x_2955_ = lean_string_dec_eq(v___y_2939_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_main___closed__25));
v___x_2957_ = lean_string_dec_eq(v___y_2939_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_main___closed__26));
v___x_2959_ = lean_string_dec_eq(v___y_2939_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = ((lean_object*)(l_main___closed__27));
v___x_2961_ = lean_string_dec_eq(v___y_2939_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_main___closed__28));
v___x_2963_ = lean_string_dec_eq(v___y_2939_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = ((lean_object*)(l_main___closed__29));
v___x_2965_ = lean_string_dec_eq(v___y_2939_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = ((lean_object*)(l_main___closed__30));
v___x_2967_ = lean_string_dec_eq(v___y_2939_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = ((lean_object*)(l_main___closed__31));
v___x_2969_ = lean_string_dec_eq(v___y_2939_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = ((lean_object*)(l_main___closed__32));
v___x_2971_ = lean_string_dec_eq(v___y_2939_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_main___closed__33));
v___x_2973_ = lean_string_dec_eq(v___y_2939_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = ((lean_object*)(l_main___closed__34));
v___x_2975_ = lean_string_dec_eq(v___y_2939_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_main___closed__35));
v___x_2977_ = lean_string_dec_eq(v___y_2939_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_main___closed__36));
v___x_2979_ = lean_string_dec_eq(v___y_2939_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = ((lean_object*)(l_main___closed__37));
v___x_2981_ = lean_string_dec_eq(v___y_2939_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_main___closed__38));
v___x_2983_ = lean_string_dec_eq(v___y_2939_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2984_ = ((lean_object*)(l_main___closed__39));
v___x_2985_ = lean_string_dec_eq(v___y_2939_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = ((lean_object*)(l_main___closed__40));
v___x_2987_ = lean_string_dec_eq(v___y_2939_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = ((lean_object*)(l_main___closed__41));
v___x_2989_ = lean_string_dec_eq(v___y_2939_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = ((lean_object*)(l_main___closed__42));
v___x_2991_ = lean_string_dec_eq(v___y_2939_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2992_ = ((lean_object*)(l_main___closed__43));
v___x_2993_ = lean_string_dec_eq(v___y_2939_, v___x_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = ((lean_object*)(l_main___closed__44));
v___x_2995_ = lean_string_dec_eq(v___y_2939_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = ((lean_object*)(l_main___closed__45));
v___x_2997_ = lean_string_dec_eq(v___y_2939_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_main___closed__46));
v___x_2999_ = lean_string_dec_eq(v___y_2939_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_main___closed__47));
v___x_3001_ = lean_string_dec_eq(v___y_2939_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = ((lean_object*)(l_main___closed__48));
v___x_3003_ = lean_string_dec_eq(v___y_2939_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = ((lean_object*)(l_main___closed__49));
v___x_3005_ = lean_string_dec_eq(v___y_2939_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = ((lean_object*)(l_main___closed__50));
v___x_3007_ = lean_string_dec_eq(v___y_2939_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = ((lean_object*)(l_main___closed__51));
v___x_3009_ = lean_string_dec_eq(v___y_2939_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = ((lean_object*)(l_main___closed__52));
v___x_3011_ = lean_string_dec_eq(v___y_2939_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = ((lean_object*)(l_main___closed__53));
v___x_3013_ = lean_string_dec_eq(v___y_2939_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_main___closed__54));
v___x_3015_ = lean_string_dec_eq(v___y_2939_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_main___closed__55));
v___x_3017_ = lean_string_dec_eq(v___y_2939_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = ((lean_object*)(l_main___closed__56));
v___x_3019_ = lean_string_dec_eq(v___y_2939_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = ((lean_object*)(l_main___closed__57));
v___x_3021_ = lean_string_dec_eq(v___y_2939_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = ((lean_object*)(l_main___closed__58));
v___x_3023_ = lean_string_dec_eq(v___y_2939_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = ((lean_object*)(l_main___closed__59));
v___x_3025_ = lean_string_dec_eq(v___y_2939_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = ((lean_object*)(l_main___closed__60));
v___x_3027_ = lean_string_dec_eq(v___y_2939_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = ((lean_object*)(l_main___closed__61));
v___x_3029_ = lean_string_dec_eq(v___y_2939_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_main___closed__62));
v___x_3031_ = lean_string_dec_eq(v___y_2939_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = ((lean_object*)(l_main___closed__63));
v___x_3033_ = lean_string_dec_eq(v___y_2939_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3034_ = ((lean_object*)(l_main___closed__64));
v___x_3035_ = lean_string_dec_eq(v___y_2939_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = ((lean_object*)(l_main___closed__65));
v___x_3037_ = lean_string_dec_eq(v___y_2939_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_main___closed__66));
v___x_3039_ = lean_string_dec_eq(v___y_2939_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = ((lean_object*)(l_main___closed__67));
v___x_3041_ = lean_string_dec_eq(v___y_2939_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = ((lean_object*)(l_main___closed__68));
v___x_3043_ = lean_string_dec_eq(v___y_2939_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = ((lean_object*)(l_main___closed__69));
v___x_3045_ = lean_string_dec_eq(v___y_2939_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_main___closed__70));
v___x_3047_ = lean_string_dec_eq(v___y_2939_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = ((lean_object*)(l_main___closed__71));
v___x_3049_ = lean_string_dec_eq(v___y_2939_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_main___closed__72));
v___x_3051_ = lean_string_dec_eq(v___y_2939_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_main___closed__73));
v___x_3053_ = lean_string_dec_eq(v___y_2939_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = ((lean_object*)(l_main___closed__74));
v___x_3055_ = lean_string_dec_eq(v___y_2939_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_main___closed__75));
v___x_3057_ = lean_string_dec_eq(v___y_2939_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_main___closed__76));
v___x_3059_ = lean_string_dec_eq(v___y_2939_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_main___closed__77));
v___x_3061_ = lean_string_dec_eq(v___y_2939_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_main___closed__78));
v___x_3063_ = lean_string_dec_eq(v___y_2939_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_main___closed__79));
v___x_3065_ = lean_string_dec_eq(v___y_2939_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_main___closed__80));
v___x_3067_ = lean_string_dec_eq(v___y_2939_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = ((lean_object*)(l_main___closed__81));
v___x_3069_ = lean_string_dec_eq(v___y_2939_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_main___closed__82));
v___x_3071_ = lean_string_dec_eq(v___y_2939_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_main___closed__83));
v___x_3073_ = lean_string_dec_eq(v___y_2939_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = ((lean_object*)(l_NER_referenceNames___closed__0));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3074_;
v_snd_2857_ = v___x_3074_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_main___closed__88));
v___x_3076_ = ((lean_object*)(l_main___closed__105));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3075_;
v_snd_2857_ = v___x_3076_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l_main___closed__108));
v___x_3078_ = ((lean_object*)(l_main___closed__117));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3077_;
v_snd_2857_ = v___x_3078_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_main___closed__108));
v___x_3080_ = ((lean_object*)(l_main___closed__127));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3079_;
v_snd_2857_ = v___x_3080_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_main___closed__108));
v___x_3082_ = ((lean_object*)(l_main___closed__138));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3081_;
v_snd_2857_ = v___x_3082_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l_main___closed__108));
v___x_3084_ = ((lean_object*)(l_main___closed__147));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3083_;
v_snd_2857_ = v___x_3084_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l_main___closed__108));
v___x_3086_ = ((lean_object*)(l_main___closed__158));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3085_;
v_snd_2857_ = v___x_3086_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l_main___closed__108));
v___x_3088_ = ((lean_object*)(l_main___closed__169));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3087_;
v_snd_2857_ = v___x_3088_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = ((lean_object*)(l_main___closed__108));
v___x_3090_ = ((lean_object*)(l_main___closed__179));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3089_;
v_snd_2857_ = v___x_3090_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = ((lean_object*)(l_main___closed__108));
v___x_3092_ = ((lean_object*)(l_main___closed__188));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3091_;
v_snd_2857_ = v___x_3092_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_main___closed__108));
v___x_3094_ = ((lean_object*)(l_main___closed__200));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3093_;
v_snd_2857_ = v___x_3094_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l_main___closed__108));
v___x_3096_ = ((lean_object*)(l_main___closed__212));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3095_;
v_snd_2857_ = v___x_3096_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = ((lean_object*)(l_main___closed__108));
v___x_3098_ = ((lean_object*)(l_main___closed__221));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3097_;
v_snd_2857_ = v___x_3098_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l_main___closed__108));
v___x_3100_ = ((lean_object*)(l_main___closed__231));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3099_;
v_snd_2857_ = v___x_3100_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_main___closed__108));
v___x_3102_ = ((lean_object*)(l_main___closed__241));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3101_;
v_snd_2857_ = v___x_3102_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_main___closed__108));
v___x_3104_ = ((lean_object*)(l_main___closed__251));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3103_;
v_snd_2857_ = v___x_3104_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l_main___closed__108));
v___x_3106_ = ((lean_object*)(l_main___closed__260));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3105_;
v_snd_2857_ = v___x_3106_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_main___closed__108));
v___x_3108_ = ((lean_object*)(l_main___closed__269));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3107_;
v_snd_2857_ = v___x_3108_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l_main___closed__108));
v___x_3110_ = ((lean_object*)(l_main___closed__279));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3109_;
v_snd_2857_ = v___x_3110_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l_main___closed__108));
v___x_3112_ = ((lean_object*)(l_main___closed__288));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3111_;
v_snd_2857_ = v___x_3112_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l_main___closed__108));
v___x_3114_ = ((lean_object*)(l_main___closed__299));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3113_;
v_snd_2857_ = v___x_3114_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_main___closed__108));
v___x_3116_ = ((lean_object*)(l_main___closed__308));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3115_;
v_snd_2857_ = v___x_3116_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_main___closed__108));
v___x_3118_ = ((lean_object*)(l_main___closed__317));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3117_;
v_snd_2857_ = v___x_3118_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_main___closed__108));
v___x_3120_ = ((lean_object*)(l_main___closed__327));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3119_;
v_snd_2857_ = v___x_3120_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = ((lean_object*)(l_main___closed__108));
v___x_3122_ = ((lean_object*)(l_main___closed__336));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3121_;
v_snd_2857_ = v___x_3122_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_main___closed__108));
v___x_3124_ = ((lean_object*)(l_main___closed__345));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3123_;
v_snd_2857_ = v___x_3124_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_main___closed__108));
v___x_3126_ = ((lean_object*)(l_main___closed__355));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3125_;
v_snd_2857_ = v___x_3126_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = ((lean_object*)(l_main___closed__108));
v___x_3128_ = ((lean_object*)(l_main___closed__363));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3127_;
v_snd_2857_ = v___x_3128_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = ((lean_object*)(l_main___closed__108));
v___x_3130_ = ((lean_object*)(l_main___closed__372));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3129_;
v_snd_2857_ = v___x_3130_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l_main___closed__108));
v___x_3132_ = ((lean_object*)(l_main___closed__380));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3131_;
v_snd_2857_ = v___x_3132_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l_main___closed__108));
v___x_3134_ = ((lean_object*)(l_main___closed__390));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3133_;
v_snd_2857_ = v___x_3134_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_main___closed__108));
v___x_3136_ = ((lean_object*)(l_main___closed__398));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3135_;
v_snd_2857_ = v___x_3136_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_main___closed__108));
v___x_3138_ = ((lean_object*)(l_main___closed__410));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3137_;
v_snd_2857_ = v___x_3138_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = ((lean_object*)(l_main___closed__108));
v___x_3140_ = ((lean_object*)(l_main___closed__421));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3139_;
v_snd_2857_ = v___x_3140_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = ((lean_object*)(l_main___closed__108));
v___x_3142_ = ((lean_object*)(l_main___closed__430));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3141_;
v_snd_2857_ = v___x_3142_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_main___closed__108));
v___x_3144_ = ((lean_object*)(l_main___closed__440));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3143_;
v_snd_2857_ = v___x_3144_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_main___closed__108));
v___x_3146_ = ((lean_object*)(l_main___closed__449));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3145_;
v_snd_2857_ = v___x_3146_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = ((lean_object*)(l_main___closed__108));
v___x_3148_ = ((lean_object*)(l_main___closed__458));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3147_;
v_snd_2857_ = v___x_3148_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_main___closed__108));
v___x_3150_ = ((lean_object*)(l_main___closed__468));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3149_;
v_snd_2857_ = v___x_3150_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = ((lean_object*)(l_main___closed__108));
v___x_3152_ = ((lean_object*)(l_main___closed__476));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3151_;
v_snd_2857_ = v___x_3152_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = ((lean_object*)(l_main___closed__108));
v___x_3154_ = ((lean_object*)(l_main___closed__484));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3153_;
v_snd_2857_ = v___x_3154_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = ((lean_object*)(l_main___closed__108));
v___x_3156_ = ((lean_object*)(l_main___closed__492));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3155_;
v_snd_2857_ = v___x_3156_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_main___closed__108));
v___x_3158_ = ((lean_object*)(l_main___closed__503));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3157_;
v_snd_2857_ = v___x_3158_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l_main___closed__108));
v___x_3160_ = ((lean_object*)(l_main___closed__511));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3159_;
v_snd_2857_ = v___x_3160_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = ((lean_object*)(l_main___closed__108));
v___x_3162_ = ((lean_object*)(l_main___closed__519));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3161_;
v_snd_2857_ = v___x_3162_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = ((lean_object*)(l_main___closed__108));
v___x_3164_ = ((lean_object*)(l_main___closed__528));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3163_;
v_snd_2857_ = v___x_3164_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_main___closed__108));
v___x_3166_ = ((lean_object*)(l_main___closed__537));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3165_;
v_snd_2857_ = v___x_3166_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = ((lean_object*)(l_main___closed__108));
v___x_3168_ = ((lean_object*)(l_main___closed__548));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3167_;
v_snd_2857_ = v___x_3168_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = ((lean_object*)(l_main___closed__108));
v___x_3170_ = ((lean_object*)(l_main___closed__557));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3169_;
v_snd_2857_ = v___x_3170_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_main___closed__108));
v___x_3172_ = ((lean_object*)(l_main___closed__566));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3171_;
v_snd_2857_ = v___x_3172_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_main___closed__108));
v___x_3174_ = ((lean_object*)(l_main___closed__574));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3173_;
v_snd_2857_ = v___x_3174_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_main___closed__108));
v___x_3176_ = ((lean_object*)(l_main___closed__583));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3175_;
v_snd_2857_ = v___x_3176_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_main___closed__108));
v___x_3178_ = ((lean_object*)(l_main___closed__592));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3177_;
v_snd_2857_ = v___x_3178_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_main___closed__108));
v___x_3180_ = ((lean_object*)(l_main___closed__602));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3179_;
v_snd_2857_ = v___x_3180_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_main___closed__108));
v___x_3182_ = ((lean_object*)(l_main___closed__609));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3181_;
v_snd_2857_ = v___x_3182_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_main___closed__108));
v___x_3184_ = ((lean_object*)(l_main___closed__619));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3183_;
v_snd_2857_ = v___x_3184_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_main___closed__108));
v___x_3186_ = ((lean_object*)(l_main___closed__627));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3185_;
v_snd_2857_ = v___x_3186_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_main___closed__108));
v___x_3188_ = ((lean_object*)(l_main___closed__637));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3187_;
v_snd_2857_ = v___x_3188_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_main___closed__108));
v___x_3190_ = ((lean_object*)(l_main___closed__646));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3189_;
v_snd_2857_ = v___x_3190_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_main___closed__108));
v___x_3192_ = ((lean_object*)(l_main___closed__654));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3191_;
v_snd_2857_ = v___x_3192_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_main___closed__108));
v___x_3194_ = ((lean_object*)(l_main___closed__662));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3193_;
v_snd_2857_ = v___x_3194_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_main___closed__108));
v___x_3196_ = ((lean_object*)(l_main___closed__671));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3195_;
v_snd_2857_ = v___x_3196_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_main___closed__108));
v___x_3198_ = ((lean_object*)(l_main___closed__680));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3197_;
v_snd_2857_ = v___x_3198_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_main___closed__108));
v___x_3200_ = ((lean_object*)(l_main___closed__688));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3199_;
v_snd_2857_ = v___x_3200_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_main___closed__108));
v___x_3202_ = ((lean_object*)(l_main___closed__698));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3201_;
v_snd_2857_ = v___x_3202_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_main___closed__108));
v___x_3204_ = ((lean_object*)(l_main___closed__706));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3203_;
v_snd_2857_ = v___x_3204_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_main___closed__108));
v___x_3206_ = ((lean_object*)(l_main___closed__715));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3205_;
v_snd_2857_ = v___x_3206_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l_main___closed__108));
v___x_3208_ = ((lean_object*)(l_main___closed__723));
v___y_2855_ = v___y_2939_;
v_fst_2856_ = v___x_3207_;
v_snd_2857_ = v___x_3208_;
goto v___jp_2854_;
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_args_2756_);
v_a_3211_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_2853_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_2853_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_args_2756_);
v_a_3219_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_2852_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_2852_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v_args_2756_);
v_a_3227_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_2849_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_2849_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
v___jp_2758_:
{
lean_object* v___x_2762_; 
lean_inc_ref(v___y_2761_);
v___x_2762_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___y_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2774_; 
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___x_2762_, 0);
lean_dec(v_unused_2775_);
v___x_2764_ = v___x_2762_;
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v___x_2762_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2774_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
if (v___y_2759_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_box_uint32(v___y_2760_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = l_main___boxed__const__1;
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2770_);
v___x_2772_ = v___x_2764_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
v_a_2776_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2762_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2762_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
v___jp_2784_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_NER_loadedScan(v___y_2785_, v___y_2788_, v___y_2787_);
lean_dec_ref(v___y_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = lean_unbox(v_a_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = ((lean_object*)(l_main___closed__0));
v___x_2793_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
v___y_2759_ = v___x_2793_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v___x_2792_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_main___closed__1));
v___x_2795_ = lean_unbox(v_a_2790_);
lean_dec(v_a_2790_);
v___y_2759_ = v___x_2795_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v___x_2794_;
goto v___jp_2758_;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_a_2796_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2789_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2789_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
v___jp_2804_:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_IO_FS_lines(v___y_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; size_t v_sz_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v_sz_2813_ = lean_array_size(v_a_2812_);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_a_2812_, v_sz_2813_, v___y_2806_, v___y_2805_);
lean_dec(v_a_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
if (v___y_2809_ == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = ((lean_object*)(l_main___closed__2));
v___y_2785_ = v___y_2807_;
v___y_2786_ = v___y_2808_;
v___y_2787_ = v_a_2815_;
v___y_2788_ = v___x_2816_;
goto v___jp_2784_;
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2818_ = ((lean_object*)(l_main___closed__3));
v___y_2785_ = v___y_2807_;
v___y_2786_ = v___y_2808_;
v___y_2787_ = v_a_2817_;
v___y_2788_ = v___x_2818_;
goto v___jp_2784_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v___y_2807_);
v_a_2819_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2814_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2814_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2827_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2811_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2811_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
v___jp_2835_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2841_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___y_2839_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_2844_ = lean_string_dec_eq(v___y_2836_, v___x_2843_);
lean_dec_ref(v___y_2836_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
v___x_2845_ = ((lean_object*)(l_main___closed__5));
v___y_2805_ = v___x_2842_;
v___y_2806_ = v___y_2837_;
v___y_2807_ = v___y_2838_;
v___y_2808_ = v___y_2840_;
v___y_2809_ = v___x_2844_;
v___y_2810_ = v___x_2845_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2846_; 
v___x_2846_ = ((lean_object*)(l_main___closed__6));
v___y_2805_ = v___x_2842_;
v___y_2806_ = v___y_2837_;
v___y_2807_ = v___y_2838_;
v___y_2808_ = v___y_2840_;
v___y_2809_ = v___x_2844_;
v___y_2810_ = v___x_2846_;
goto v___jp_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = _lean_main(v_args_3235_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_3238_, lean_object* v_as_x27_3239_, lean_object* v_b_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_3239_, v_b_3240_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_3244_, lean_object* v_as_x27_3245_, lean_object* v_b_3246_, lean_object* v_a_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_3244_, v_as_x27_3245_, v_b_3246_, v_a_3247_);
lean_dec(v_as_x27_3245_);
lean_dec(v_as_3244_);
return v_res_3249_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFX__ProofDriver(uint8_t builtin) {
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
  res = initialize_NFX__ProofDriver(1 /* builtin */);
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
