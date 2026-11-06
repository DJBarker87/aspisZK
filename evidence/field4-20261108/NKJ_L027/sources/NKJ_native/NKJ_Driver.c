// Lean compiler output
// Module: NKJ_Driver
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAxiomVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstantVal_beq(lean_object*, lean_object*);
uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*);
uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_IO_FS_lines(lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_NER_quotTag(uint8_t);
LEAN_EXPORT lean_object* l_NER_quotTag___boxed(lean_object*);
LEAN_EXPORT uint8_t l_NER_sameDeclaration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NER_sameDeclaration___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "previous"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "current"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_identical"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reason"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "serialized declaration differs from selected owner"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__6_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "phase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "own_declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__2_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "loader_imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "imports_match"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dangling"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "duplicate_owners"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "cached_replicas"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__10_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declarations"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edges"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_NER_loadedScan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NER_loadedScan___closed__0;
static lean_once_cell_t l_NER_loadedScan___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NER_loadedScan___closed__1;
static lean_once_cell_t l_NER_loadedScan___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NER_loadedScan___closed__2;
LEAN_EXPORT lean_object* l_NER_loadedScan(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NER_loadedScan___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NKJ_LOADED_scan.jsonl"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "NFN_QUERY_LOADED_scan.jsonl"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "NKJ_EXPECTED_IMPORTS.jsonl"};
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
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NKJ_AUDIT_ROOTS.json"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NKJ_FIXTURE_ROOTS.json"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "NKJ_COMBINED_IMPORT"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_ctor_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__20_value),LEAN_SCALAR_PTR_LITERAL(99, 179, 126, 72, 245, 95, 222, 14)}};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_array_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__21_value)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_Planted"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(180, 186, 146, 59, 104, 29, 230, 143)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_string_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "NEP_Mutations"};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static const lean_ctor_object l_main___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__25_value),LEAN_SCALAR_PTR_LITERAL(179, 7, 234, 101, 142, 50, 205, 73)}};
static const lean_object* l_main___closed__26 = (const lean_object*)&l_main___closed__26_value;
static const lean_array_object l_main___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_main___closed__24_value),((lean_object*)&l_main___closed__26_value)}};
static const lean_object* l_main___closed__27 = (const lean_object*)&l_main___closed__27_value;
static const lean_string_object l_main___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__28 = (const lean_object*)&l_main___closed__28_value;
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
LEAN_EXPORT lean_object* l_NER_quotTag(uint8_t v_x_105_){
_start:
{
switch(v_x_105_)
{
case 0:
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(0u);
return v___x_106_;
}
case 1:
{
lean_object* v___x_107_; 
v___x_107_ = lean_unsigned_to_nat(1u);
return v___x_107_;
}
case 2:
{
lean_object* v___x_108_; 
v___x_108_ = lean_unsigned_to_nat(2u);
return v___x_108_;
}
default: 
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(3u);
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_NER_quotTag___boxed(lean_object* v_x_110_){
_start:
{
uint8_t v_x_44__boxed_111_; lean_object* v_res_112_; 
v_x_44__boxed_111_ = lean_unbox(v_x_110_);
v_res_112_ = l_NER_quotTag(v_x_44__boxed_111_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_NER_sameDeclaration(lean_object* v_a_113_, lean_object* v_b_114_){
_start:
{
uint8_t v___y_116_; uint8_t v___y_117_; uint8_t v___y_118_; uint8_t v___y_120_; uint8_t v___y_121_; uint8_t v___y_122_; uint8_t v___y_123_; uint8_t v___y_124_; 
switch(lean_obj_tag(v_a_113_))
{
case 0:
{
if (lean_obj_tag(v_b_114_) == 0)
{
lean_object* v_val_125_; lean_object* v_val_126_; uint8_t v___x_127_; 
v_val_125_ = lean_ctor_get(v_a_113_, 0);
v_val_126_ = lean_ctor_get(v_b_114_, 0);
v___x_127_ = l_Lean_instBEqAxiomVal_beq(v_val_125_, v_val_126_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
case 1:
{
if (lean_obj_tag(v_b_114_) == 1)
{
lean_object* v_val_129_; lean_object* v_val_130_; uint8_t v___x_131_; 
v_val_129_ = lean_ctor_get(v_a_113_, 0);
v_val_130_ = lean_ctor_get(v_b_114_, 0);
v___x_131_ = l_Lean_instBEqDefinitionVal_beq(v_val_129_, v_val_130_);
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
case 2:
{
if (lean_obj_tag(v_b_114_) == 2)
{
lean_object* v_val_133_; lean_object* v_val_134_; lean_object* v_toConstantVal_135_; lean_object* v_all_136_; lean_object* v_toConstantVal_137_; lean_object* v_all_138_; uint8_t v___x_139_; 
v_val_133_ = lean_ctor_get(v_a_113_, 0);
v_val_134_ = lean_ctor_get(v_b_114_, 0);
v_toConstantVal_135_ = lean_ctor_get(v_val_133_, 0);
v_all_136_ = lean_ctor_get(v_val_133_, 2);
v_toConstantVal_137_ = lean_ctor_get(v_val_134_, 0);
v_all_138_ = lean_ctor_get(v_val_134_, 2);
v___x_139_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_135_, v_toConstantVal_137_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_136_, v_all_138_);
return v___x_140_;
}
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 3:
{
if (lean_obj_tag(v_b_114_) == 3)
{
lean_object* v_val_142_; lean_object* v_val_143_; uint8_t v___x_144_; 
v_val_142_ = lean_ctor_get(v_a_113_, 0);
v_val_143_ = lean_ctor_get(v_b_114_, 0);
v___x_144_ = l_Lean_instBEqOpaqueVal_beq(v_val_142_, v_val_143_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
case 4:
{
if (lean_obj_tag(v_b_114_) == 4)
{
lean_object* v_val_146_; lean_object* v_val_147_; lean_object* v_toConstantVal_148_; uint8_t v_kind_149_; lean_object* v_toConstantVal_150_; uint8_t v_kind_151_; uint8_t v___x_152_; 
v_val_146_ = lean_ctor_get(v_a_113_, 0);
v_val_147_ = lean_ctor_get(v_b_114_, 0);
v_toConstantVal_148_ = lean_ctor_get(v_val_146_, 0);
v_kind_149_ = lean_ctor_get_uint8(v_val_146_, sizeof(void*)*1);
v_toConstantVal_150_ = lean_ctor_get(v_val_147_, 0);
v_kind_151_ = lean_ctor_get_uint8(v_val_147_, sizeof(void*)*1);
v___x_152_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_148_, v_toConstantVal_150_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_NER_quotTag(v_kind_149_);
v___x_154_ = l_NER_quotTag(v_kind_151_);
v___x_155_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
lean_dec(v___x_154_);
lean_dec(v___x_153_);
return v___x_155_;
}
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
case 5:
{
if (lean_obj_tag(v_b_114_) == 5)
{
lean_object* v_val_157_; lean_object* v_val_158_; lean_object* v_toConstantVal_159_; lean_object* v_numParams_160_; lean_object* v_numIndices_161_; lean_object* v_all_162_; lean_object* v_ctors_163_; lean_object* v_numNested_164_; uint8_t v_isRec_165_; uint8_t v_isUnsafe_166_; uint8_t v_isReflexive_167_; lean_object* v_toConstantVal_168_; lean_object* v_numParams_169_; lean_object* v_numIndices_170_; lean_object* v_all_171_; lean_object* v_ctors_172_; lean_object* v_numNested_173_; uint8_t v_isRec_174_; uint8_t v_isUnsafe_175_; uint8_t v_isReflexive_176_; uint8_t v___y_178_; uint8_t v___x_183_; 
v_val_157_ = lean_ctor_get(v_a_113_, 0);
v_val_158_ = lean_ctor_get(v_b_114_, 0);
v_toConstantVal_159_ = lean_ctor_get(v_val_157_, 0);
v_numParams_160_ = lean_ctor_get(v_val_157_, 1);
v_numIndices_161_ = lean_ctor_get(v_val_157_, 2);
v_all_162_ = lean_ctor_get(v_val_157_, 3);
v_ctors_163_ = lean_ctor_get(v_val_157_, 4);
v_numNested_164_ = lean_ctor_get(v_val_157_, 5);
v_isRec_165_ = lean_ctor_get_uint8(v_val_157_, sizeof(void*)*6);
v_isUnsafe_166_ = lean_ctor_get_uint8(v_val_157_, sizeof(void*)*6 + 1);
v_isReflexive_167_ = lean_ctor_get_uint8(v_val_157_, sizeof(void*)*6 + 2);
v_toConstantVal_168_ = lean_ctor_get(v_val_158_, 0);
v_numParams_169_ = lean_ctor_get(v_val_158_, 1);
v_numIndices_170_ = lean_ctor_get(v_val_158_, 2);
v_all_171_ = lean_ctor_get(v_val_158_, 3);
v_ctors_172_ = lean_ctor_get(v_val_158_, 4);
v_numNested_173_ = lean_ctor_get(v_val_158_, 5);
v_isRec_174_ = lean_ctor_get_uint8(v_val_158_, sizeof(void*)*6);
v_isUnsafe_175_ = lean_ctor_get_uint8(v_val_158_, sizeof(void*)*6 + 1);
v_isReflexive_176_ = lean_ctor_get_uint8(v_val_158_, sizeof(void*)*6 + 2);
v___x_183_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_159_, v_toConstantVal_168_);
if (v___x_183_ == 0)
{
v___y_178_ = v___x_183_;
goto v___jp_177_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_eq(v_numParams_160_, v_numParams_169_);
v___y_178_ = v___x_184_;
goto v___jp_177_;
}
v___jp_177_:
{
if (v___y_178_ == 0)
{
return v___y_178_;
}
else
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_eq(v_numIndices_161_, v_numIndices_170_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_162_, v_all_171_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_ctors_163_, v_ctors_172_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_eq(v_numNested_164_, v_numNested_173_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
if (v_isRec_165_ == 0)
{
if (v_isRec_174_ == 0)
{
v___y_120_ = v_isReflexive_176_;
v___y_121_ = v_isUnsafe_166_;
v___y_122_ = v___x_182_;
v___y_123_ = v_isReflexive_167_;
v___y_124_ = v_isUnsafe_175_;
goto v___jp_119_;
}
else
{
return v_isRec_165_;
}
}
else
{
if (v_isRec_174_ == 0)
{
return v_isRec_174_;
}
else
{
v___y_120_ = v_isReflexive_176_;
v___y_121_ = v_isUnsafe_166_;
v___y_122_ = v___x_182_;
v___y_123_ = v_isReflexive_167_;
v___y_124_ = v_isUnsafe_175_;
goto v___jp_119_;
}
}
}
}
}
}
}
}
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
case 6:
{
if (lean_obj_tag(v_b_114_) == 6)
{
lean_object* v_val_186_; lean_object* v_val_187_; uint8_t v___x_188_; 
v_val_186_ = lean_ctor_get(v_a_113_, 0);
v_val_187_ = lean_ctor_get(v_b_114_, 0);
v___x_188_ = l_Lean_instBEqConstructorVal_beq(v_val_186_, v_val_187_);
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
default: 
{
if (lean_obj_tag(v_b_114_) == 7)
{
lean_object* v_val_190_; lean_object* v_val_191_; uint8_t v___x_192_; 
v_val_190_ = lean_ctor_get(v_a_113_, 0);
v_val_191_ = lean_ctor_get(v_b_114_, 0);
v___x_192_ = l_Lean_instBEqRecursorVal_beq(v_val_190_, v_val_191_);
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
}
}
v___jp_115_:
{
if (v___y_118_ == 0)
{
if (v___y_116_ == 0)
{
return v___y_117_;
}
else
{
return v___y_118_;
}
}
else
{
return v___y_116_;
}
}
v___jp_119_:
{
if (v___y_121_ == 0)
{
if (v___y_124_ == 0)
{
v___y_116_ = v___y_120_;
v___y_117_ = v___y_122_;
v___y_118_ = v___y_123_;
goto v___jp_115_;
}
else
{
return v___y_121_;
}
}
else
{
if (v___y_124_ == 0)
{
return v___y_124_;
}
else
{
v___y_116_ = v___y_120_;
v___y_117_ = v___y_122_;
v___y_118_ = v___y_123_;
goto v___jp_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NER_sameDeclaration___boxed(lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_NER_sameDeclaration(v_a_194_, v_b_195_);
lean_dec_ref(v_b_195_);
lean_dec_ref(v_a_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(lean_object* v_env_200_, lean_object* v_val_201_, lean_object* v_as_202_, size_t v_sz_203_, size_t v_i_204_, lean_object* v_b_205_){
_start:
{
lean_object* v_a_208_; uint8_t v___x_212_; 
v___x_212_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v_env_200_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_b_205_);
return v___x_213_;
}
else
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
v_fst_214_ = lean_ctor_get(v_b_205_, 0);
v_snd_215_ = lean_ctor_get(v_b_205_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_b_205_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v_b_205_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_b_205_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_checked_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_checked_219_ = lean_ctor_get(v_env_200_, 2);
v___x_220_ = lean_unsigned_to_nat(1u);
v_a_221_ = lean_array_uget_borrowed(v_as_202_, v_i_204_);
v___x_222_ = lean_nat_add(v_snd_215_, v___x_220_);
lean_dec(v_snd_215_);
lean_inc_ref(v_checked_219_);
v___x_223_ = lean_task_get_own(v_checked_219_);
lean_inc(v_a_221_);
v___x_224_ = lean_environment_find(v___x_223_, v_a_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0));
v___x_226_ = l_Lean_ConstantInfo_name(v_val_201_);
v___x_227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_226_, v___x_212_);
v___x_228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_228_);
lean_ctor_set(v___x_217_, 0, v___x_225_);
v___x_230_ = v___x_217_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_241_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1));
lean_inc(v_a_221_);
v___x_232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_221_, v___x_212_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_231_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_230_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = l_Lean_Json_mkObj(v___x_237_);
lean_dec_ref_known(v___x_237_, 2);
v___x_239_ = lean_array_push(v_fst_214_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_222_);
v_a_208_ = v___x_240_;
goto v___jp_207_;
}
}
else
{
lean_object* v___x_243_; 
lean_dec_ref_known(v___x_224_, 1);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_222_);
v___x_243_ = v___x_217_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fst_214_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_222_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
v_a_208_ = v___x_243_;
goto v___jp_207_;
}
}
}
}
v___jp_207_:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_204_, v___x_209_);
v_i_204_ = v___x_210_;
v_b_205_ = v_a_208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___boxed(lean_object* v_env_246_, lean_object* v_val_247_, lean_object* v_as_248_, lean_object* v_sz_249_, lean_object* v_i_250_, lean_object* v_b_251_, lean_object* v___y_252_){
_start:
{
size_t v_sz_boxed_253_; size_t v_i_boxed_254_; lean_object* v_res_255_; 
v_sz_boxed_253_ = lean_unbox_usize(v_sz_249_);
lean_dec(v_sz_249_);
v_i_boxed_254_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(v_env_246_, v_val_247_, v_as_248_, v_sz_boxed_253_, v_i_boxed_254_, v_b_251_);
lean_dec_ref(v_as_248_);
lean_dec_ref(v_val_247_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(lean_object* v_env_280_, lean_object* v___x_281_, lean_object* v_as_282_, size_t v_sz_283_, size_t v_i_284_, lean_object* v_b_285_){
_start:
{
lean_object* v_a_288_; uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_lt(v_i_284_, v_sz_283_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v___x_281_);
lean_dec_ref(v_env_280_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_b_285_);
return v___x_293_;
}
else
{
lean_object* v_snd_294_; lean_object* v_snd_295_; lean_object* v_snd_296_; lean_object* v_fst_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_443_; 
v_snd_294_ = lean_ctor_get(v_b_285_, 1);
lean_inc(v_snd_294_);
v_snd_295_ = lean_ctor_get(v_snd_294_, 1);
lean_inc(v_snd_295_);
v_snd_296_ = lean_ctor_get(v_snd_295_, 1);
lean_inc(v_snd_296_);
v_fst_297_ = lean_ctor_get(v_b_285_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_b_285_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v_b_285_, 1);
lean_dec(v_unused_444_);
v___x_299_ = v_b_285_;
v_isShared_300_ = v_isSharedCheck_443_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_fst_297_);
lean_dec(v_b_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_443_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_fst_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_441_; 
v_fst_301_ = lean_ctor_get(v_snd_294_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_snd_294_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v_snd_294_, 1);
lean_dec(v_unused_442_);
v___x_303_ = v_snd_294_;
v_isShared_304_ = v_isSharedCheck_441_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_fst_301_);
lean_dec(v_snd_294_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_441_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fst_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_439_; 
v_fst_305_ = lean_ctor_get(v_snd_295_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v_snd_295_, 1);
lean_dec(v_unused_440_);
v___x_307_ = v_snd_295_;
v_isShared_308_ = v_isSharedCheck_439_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_fst_305_);
lean_dec(v_snd_295_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_439_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_438_; 
v_fst_309_ = lean_ctor_get(v_snd_296_, 0);
v_snd_310_ = lean_ctor_get(v_snd_296_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_snd_296_);
if (v_isSharedCheck_438_ == 0)
{
v___x_312_ = v_snd_296_;
v_isShared_313_ = v_isSharedCheck_438_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v_snd_296_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_438_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_checked_314_; lean_object* v_a_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_checked_314_ = lean_ctor_get(v_env_280_, 2);
v_a_315_ = lean_array_uget_borrowed(v_as_282_, v_i_284_);
lean_inc_ref(v_checked_314_);
v___x_316_ = lean_task_get_own(v_checked_314_);
v___x_317_ = l_Lean_ConstantInfo_name(v_a_315_);
lean_inc(v___x_317_);
v___x_318_ = lean_environment_find(v___x_316_, v___x_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_414_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_414_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_414_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_414_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_duplicateOwners_324_; lean_object* v_cachedReplicas_325_; lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__0___redArg(v_fst_297_, v___x_317_);
if (lean_obj_tag(v___x_361_) == 1)
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_397_; 
v_val_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_397_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_397_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_397_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0));
lean_inc(v___x_317_);
v___x_367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_317_, v___x_292_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 3);
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_396_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_366_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__1));
v___x_372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_362_, v___x_292_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
lean_ctor_set(v___x_321_, 0, v___x_372_);
v___x_374_ = v___x_321_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_395_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_371_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2));
lean_inc(v___x_281_);
v___x_377_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_281_, v___x_292_);
v___x_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__3));
lean_inc(v_a_315_);
v___x_381_ = l_Lean_ConstantInfo_value_x3f(v_a_315_, v___x_292_);
lean_inc(v_val_319_);
v___x_382_ = l_Lean_ConstantInfo_value_x3f(v_val_319_, v___x_292_);
v___x_383_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_381_, v___x_382_);
lean_dec(v___x_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_384_, 0, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_380_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_379_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_375_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_370_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_Json_mkObj(v___x_390_);
lean_dec_ref_known(v___x_390_, 2);
v___x_392_ = l_NER_sameDeclaration(v_a_315_, v_val_319_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_array_push(v_fst_305_, v___x_391_);
v_duplicateOwners_324_ = v___x_393_;
v_cachedReplicas_325_ = v_fst_309_;
goto v___jp_323_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_array_push(v_fst_309_, v___x_391_);
v_duplicateOwners_324_ = v_fst_305_;
v_cachedReplicas_325_ = v___x_394_;
goto v___jp_323_;
}
}
}
}
}
else
{
uint8_t v___x_398_; 
lean_dec(v___x_361_);
v___x_398_ = l_NER_sameDeclaration(v_a_315_, v_val_319_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__0));
lean_inc(v___x_317_);
v___x_400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_317_, v___x_292_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
lean_ctor_set(v___x_321_, 0, v___x_400_);
v___x_402_ = v___x_321_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_413_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_399_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__2));
lean_inc(v___x_281_);
v___x_405_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_281_, v___x_292_);
v___x_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_404_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__8));
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_403_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_Json_mkObj(v___x_410_);
lean_dec_ref_known(v___x_410_, 2);
v___x_412_ = lean_array_push(v_fst_305_, v___x_411_);
v_duplicateOwners_324_ = v___x_412_;
v_cachedReplicas_325_ = v_fst_309_;
goto v___jp_323_;
}
}
else
{
lean_del_object(v___x_321_);
v_duplicateOwners_324_ = v_fst_305_;
v_cachedReplicas_325_ = v_fst_309_;
goto v___jp_323_;
}
}
v___jp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_inc(v_val_319_);
v___x_326_ = l_NER_referenceNames(v_val_319_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_fst_301_);
v___x_328_ = v___x_312_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_fst_301_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_snd_310_);
v___x_328_ = v_reuseFailAlloc_360_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; 
v_sz_329_ = lean_array_size(v___x_326_);
v___x_330_ = ((size_t)0ULL);
lean_inc_ref(v_env_280_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0(v_env_280_, v_val_319_, v___x_326_, v_sz_329_, v___x_330_, v___x_328_);
lean_dec_ref(v___x_326_);
lean_dec(v_val_319_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_351_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_fst_333_ = lean_ctor_get(v_a_332_, 0);
v_snd_334_ = lean_ctor_get(v_a_332_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_351_ == 0)
{
v___x_336_ = v_a_332_;
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_inc(v_fst_333_);
lean_dec(v_a_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
lean_inc(v___x_281_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__1___redArg(v_fst_297_, v___x_317_, v___x_281_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v_cachedReplicas_325_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_cachedReplicas_325_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_snd_334_);
v___x_340_ = v_reuseFailAlloc_350_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_340_);
lean_ctor_set(v___x_307_, 0, v_duplicateOwners_324_);
v___x_342_ = v___x_307_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_duplicateOwners_324_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_349_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_342_);
lean_ctor_set(v___x_303_, 0, v_fst_333_);
v___x_344_ = v___x_303_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_fst_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_344_);
lean_ctor_set(v___x_299_, 0, v___x_338_);
v___x_346_ = v___x_299_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v_a_288_ = v___x_346_;
goto v___jp_287_;
}
}
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v_cachedReplicas_325_);
lean_dec_ref(v_duplicateOwners_324_);
lean_dec(v___x_317_);
lean_del_object(v___x_307_);
lean_del_object(v___x_303_);
lean_del_object(v___x_299_);
lean_dec(v_fst_297_);
lean_dec(v___x_281_);
lean_dec_ref(v_env_280_);
v_a_352_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_331_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v___x_318_);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__0));
v___x_416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_317_, v___x_292_);
v___x_417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_inc_ref(v___x_417_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_417_);
lean_ctor_set(v___x_312_, 0, v___x_415_);
v___x_419_ = v___x_312_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_417_);
v___x_419_ = v_reuseFailAlloc_437_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__0___closed__1));
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_417_);
lean_ctor_set(v___x_307_, 0, v___x_420_);
v___x_422_ = v___x_307_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_417_);
v___x_422_ = v_reuseFailAlloc_436_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___closed__13));
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_419_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_Json_mkObj(v___x_425_);
lean_dec_ref_known(v___x_425_, 2);
v___x_427_ = lean_array_push(v_fst_301_, v___x_426_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_snd_310_);
lean_ctor_set(v___x_303_, 0, v_fst_309_);
v___x_429_ = v___x_303_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_snd_310_);
v___x_429_ = v_reuseFailAlloc_435_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_429_);
lean_ctor_set(v___x_299_, 0, v_fst_305_);
v___x_431_ = v___x_299_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_fst_305_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_427_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_fst_297_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v_a_288_ = v___x_433_;
goto v___jp_287_;
}
}
}
}
}
}
}
}
}
}
v___jp_287_:
{
size_t v___x_289_; size_t v___x_290_; 
v___x_289_ = ((size_t)1ULL);
v___x_290_ = lean_usize_add(v_i_284_, v___x_289_);
v_i_284_ = v___x_290_;
v_b_285_ = v_a_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1___boxed(lean_object* v_env_445_, lean_object* v___x_446_, lean_object* v_as_447_, lean_object* v_sz_448_, lean_object* v_i_449_, lean_object* v_b_450_, lean_object* v___y_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_448_);
lean_dec(v_sz_448_);
v_i_boxed_453_ = lean_unbox_usize(v_i_449_);
lean_dec(v_i_449_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(v_env_445_, v___x_446_, v_as_447_, v_sz_boxed_452_, v_i_boxed_453_, v_b_450_);
lean_dec_ref(v_as_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(size_t v_sz_455_, size_t v_i_456_, lean_object* v_bs_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_456_, v_sz_455_);
if (v___x_458_ == 0)
{
return v_bs_457_;
}
else
{
lean_object* v_v_459_; lean_object* v_module_460_; lean_object* v___x_461_; lean_object* v_bs_x27_462_; lean_object* v___x_463_; size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; 
v_v_459_ = lean_array_uget_borrowed(v_bs_457_, v_i_456_);
v_module_460_ = lean_ctor_get(v_v_459_, 0);
lean_inc(v_module_460_);
v___x_461_ = lean_unsigned_to_nat(0u);
v_bs_x27_462_ = lean_array_uset(v_bs_457_, v_i_456_, v___x_461_);
v___x_463_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_460_, v___x_458_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_456_, v___x_464_);
v___x_466_ = lean_array_uset(v_bs_x27_462_, v_i_456_, v___x_463_);
v_i_456_ = v___x_465_;
v_bs_457_ = v___x_466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2___boxed(lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_bs_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(v_sz_boxed_471_, v_i_boxed_472_, v_bs_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg(lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v_env_496_, lean_object* v_a_497_, lean_object* v_expected_498_, lean_object* v_range_499_, lean_object* v_b_500_, lean_object* v_i_501_){
_start:
{
lean_object* v_stop_503_; lean_object* v_step_504_; uint8_t v___x_505_; 
v_stop_503_ = lean_ctor_get(v_range_499_, 1);
v_step_504_ = lean_ctor_get(v_range_499_, 2);
v___x_505_ = lean_nat_dec_lt(v_i_501_, v_stop_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec(v_i_501_);
lean_dec_ref(v_env_496_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v_b_500_);
return v___x_506_;
}
else
{
lean_object* v_fst_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_646_; 
v_fst_507_ = lean_ctor_get(v_b_500_, 0);
v_snd_508_ = lean_ctor_get(v_b_500_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_b_500_);
if (v_isSharedCheck_646_ == 0)
{
v___x_510_ = v_b_500_;
v_isShared_511_ = v_isSharedCheck_646_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_inc(v_fst_507_);
lean_dec(v_b_500_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_646_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_moduleData_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_imports_515_; lean_object* v_constants_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_moduleData_512_ = lean_ctor_get(v___x_495_, 6);
v___x_513_ = l_Lean_instInhabitedModuleData_default;
v___x_514_ = lean_array_get_borrowed(v___x_513_, v_moduleData_512_, v_i_501_);
v_imports_515_ = lean_ctor_get(v___x_514_, 0);
v_constants_516_ = lean_ctor_get(v___x_514_, 2);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_array_fget_borrowed(v___x_494_, v_i_501_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__3));
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_519_);
lean_ctor_set(v___x_510_, 0, v_snd_508_);
v___x_521_ = v___x_510_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_snd_508_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_645_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v_sz_522_ = lean_array_size(v_constants_516_);
v___x_523_ = ((size_t)0ULL);
lean_inc(v___x_518_);
lean_inc_ref(v_env_496_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(v_env_496_, v___x_518_, v_constants_516_, v_sz_522_, v___x_523_, v___x_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v_snd_526_; lean_object* v_snd_527_; lean_object* v_snd_528_; lean_object* v_fst_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_635_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v_snd_526_ = lean_ctor_get(v_a_525_, 1);
lean_inc(v_snd_526_);
v_snd_527_ = lean_ctor_get(v_snd_526_, 1);
lean_inc(v_snd_527_);
v_snd_528_ = lean_ctor_get(v_snd_527_, 1);
lean_inc(v_snd_528_);
v_fst_529_ = lean_ctor_get(v_a_525_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_a_525_, 1);
lean_dec(v_unused_636_);
v___x_531_ = v_a_525_;
v_isShared_532_ = v_isSharedCheck_635_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_fst_529_);
lean_dec(v_a_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_635_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_fst_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_633_; 
v_fst_533_ = lean_ctor_get(v_snd_526_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_snd_526_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_snd_526_, 1);
lean_dec(v_unused_634_);
v___x_535_ = v_snd_526_;
v_isShared_536_ = v_isSharedCheck_633_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_fst_533_);
lean_dec(v_snd_526_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_633_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_fst_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_631_; 
v_fst_537_ = lean_ctor_get(v_snd_527_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_snd_527_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_snd_527_, 1);
lean_dec(v_unused_632_);
v___x_539_ = v_snd_527_;
v_isShared_540_ = v_isSharedCheck_631_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_fst_537_);
lean_dec(v_snd_527_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_631_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_630_; 
v_fst_541_ = lean_ctor_get(v_snd_528_, 0);
v_snd_542_ = lean_ctor_get(v_snd_528_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_snd_528_);
if (v_isSharedCheck_630_ == 0)
{
v___x_544_ = v_snd_528_;
v_isShared_545_ = v_isSharedCheck_630_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v_snd_528_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_630_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v_failed_546_; size_t v_sz_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___y_552_; uint8_t v_failed_553_; uint8_t v___y_618_; lean_object* v___x_624_; 
v_failed_546_ = 0;
v_sz_547_ = lean_array_size(v_imports_515_);
lean_inc_ref(v_imports_515_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(v_sz_547_, v___x_523_, v_imports_515_);
v___x_549_ = l_NER_canonicalImports(v___x_548_);
lean_inc(v___x_518_);
v___x_550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_518_, v___x_505_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_expected_498_, v___x_550_);
if (lean_obj_tag(v___x_624_) == 0)
{
v___y_618_ = v_failed_546_;
goto v___jp_617_;
}
else
{
lean_object* v_val_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_array_get_size(v___x_549_);
v___x_627_ = lean_array_get_size(v_val_625_);
v___x_628_ = lean_nat_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_val_625_);
v___y_618_ = v_failed_546_;
goto v___jp_617_;
}
else
{
uint8_t v___x_629_; 
v___x_629_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v___x_549_, v_val_625_, v___x_626_);
lean_dec(v_val_625_);
v___y_618_ = v___x_629_;
goto v___jp_617_;
}
}
v___jp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_550_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_555_);
lean_ctor_set(v___x_544_, 0, v___x_554_);
v___x_557_ = v___x_544_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_616_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_559_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_549_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_559_);
lean_ctor_set(v___x_539_, 0, v___x_558_);
v___x_561_ = v___x_539_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_615_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__6));
v___x_563_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_548_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_563_);
lean_ctor_set(v___x_535_, 0, v___x_562_);
v___x_565_ = v___x_535_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_614_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__7));
v___x_567_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_567_, 0, v___y_552_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_567_);
lean_ctor_set(v___x_531_, 0, v___x_566_);
v___x_569_ = v___x_531_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_613_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_570_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__8));
v___x_571_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_533_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__9));
v___x_574_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_537_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__10));
v___x_577_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_541_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__11));
v___x_580_ = lean_array_get_size(v_constants_516_);
v___x_581_ = l_Lean_JsonNumber_fromNat(v___x_580_);
v___x_582_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_579_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__12));
v___x_585_ = l_Lean_JsonNumber_fromNat(v_snd_542_);
v___x_586_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_584_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_583_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_578_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_575_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_572_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_569_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_565_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_561_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_557_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Json_mkObj(v___x_597_);
lean_dec_ref_known(v___x_597_, 2);
v___x_599_ = l_Lean_Json_compress(v___x_598_);
v___x_600_ = l_IO_FS_Handle_putStrLn(v_a_497_, v___x_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec_ref_known(v___x_600_, 1);
v___x_601_ = lean_box(v_failed_553_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v_fst_529_);
v___x_603_ = lean_nat_add(v_i_501_, v_step_504_);
lean_dec(v_i_501_);
v_b_500_ = v___x_602_;
v_i_501_ = v___x_603_;
goto _start;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_fst_529_);
lean_dec(v_i_501_);
lean_dec_ref(v_env_496_);
v_a_605_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_600_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_600_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
}
v___jp_617_:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_fst_533_);
v___x_620_ = lean_nat_dec_eq(v___x_619_, v___x_517_);
if (v___x_620_ == 0)
{
lean_dec(v_fst_507_);
v___y_552_ = v___y_618_;
v_failed_553_ = v___x_505_;
goto v___jp_551_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_fst_537_);
v___x_622_ = lean_nat_dec_eq(v___x_621_, v___x_517_);
if (v___x_622_ == 0)
{
lean_dec(v_fst_507_);
v___y_552_ = v___y_618_;
v_failed_553_ = v___x_505_;
goto v___jp_551_;
}
else
{
if (v___y_618_ == 0)
{
lean_dec(v_fst_507_);
v___y_552_ = v___y_618_;
v_failed_553_ = v___x_505_;
goto v___jp_551_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = lean_unbox(v_fst_507_);
lean_dec(v_fst_507_);
v___y_552_ = v___y_618_;
v_failed_553_ = v___x_623_;
goto v___jp_551_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_fst_507_);
lean_dec(v_i_501_);
lean_dec_ref(v_env_496_);
v_a_637_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_524_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_524_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___boxed(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_env_649_, lean_object* v_a_650_, lean_object* v_expected_651_, lean_object* v_range_652_, lean_object* v_b_653_, lean_object* v_i_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg(v___x_647_, v___x_648_, v_env_649_, v_a_650_, v_expected_651_, v_range_652_, v_b_653_, v_i_654_);
lean_dec_ref(v_range_652_);
lean_dec_ref(v_expected_651_);
lean_dec(v_a_650_);
lean_dec_ref(v___x_648_);
lean_dec_ref(v___x_647_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(lean_object* v___x_657_, lean_object* v_env_658_, lean_object* v___x_659_, lean_object* v_a_660_, lean_object* v_expected_661_, lean_object* v_range_662_, lean_object* v_b_663_, lean_object* v_i_664_){
_start:
{
lean_object* v_stop_666_; lean_object* v_step_667_; uint8_t v___x_668_; 
v_stop_666_ = lean_ctor_get(v_range_662_, 1);
v_step_667_ = lean_ctor_get(v_range_662_, 2);
v___x_668_ = lean_nat_dec_lt(v_i_664_, v_stop_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec_ref(v_env_658_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_b_663_);
return v___x_669_;
}
else
{
lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_809_; 
v_fst_670_ = lean_ctor_get(v_b_663_, 0);
v_snd_671_ = lean_ctor_get(v_b_663_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_b_663_);
if (v_isSharedCheck_809_ == 0)
{
v___x_673_ = v_b_663_;
v_isShared_674_ = v_isSharedCheck_809_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_inc(v_fst_670_);
lean_dec(v_b_663_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_809_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_moduleData_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_imports_678_; lean_object* v_constants_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_moduleData_675_ = lean_ctor_get(v___x_659_, 6);
v___x_676_ = l_Lean_instInhabitedModuleData_default;
v___x_677_ = lean_array_get_borrowed(v___x_676_, v_moduleData_675_, v_i_664_);
v_imports_678_ = lean_ctor_get(v___x_677_, 0);
v_constants_679_ = lean_ctor_get(v___x_677_, 2);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_fget_borrowed(v___x_657_, v_i_664_);
v___x_682_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__3));
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_682_);
lean_ctor_set(v___x_673_, 0, v_snd_671_);
v___x_684_ = v___x_673_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_snd_671_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_808_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; 
v_sz_685_ = lean_array_size(v_constants_679_);
v___x_686_ = ((size_t)0ULL);
lean_inc(v___x_681_);
lean_inc_ref(v_env_658_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NER_loadedScan_spec__1(v_env_658_, v___x_681_, v_constants_679_, v_sz_685_, v___x_686_, v___x_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_snd_689_; lean_object* v_snd_690_; lean_object* v_snd_691_; lean_object* v_fst_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_798_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v_snd_689_ = lean_ctor_get(v_a_688_, 1);
lean_inc(v_snd_689_);
v_snd_690_ = lean_ctor_get(v_snd_689_, 1);
lean_inc(v_snd_690_);
v_snd_691_ = lean_ctor_get(v_snd_690_, 1);
lean_inc(v_snd_691_);
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_a_688_, 1);
lean_dec(v_unused_799_);
v___x_694_ = v_a_688_;
v_isShared_695_ = v_isSharedCheck_798_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_fst_692_);
lean_dec(v_a_688_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_798_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_796_; 
v_fst_696_ = lean_ctor_get(v_snd_689_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_snd_689_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_snd_689_, 1);
lean_dec(v_unused_797_);
v___x_698_ = v_snd_689_;
v_isShared_699_ = v_isSharedCheck_796_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_fst_696_);
lean_dec(v_snd_689_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_796_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_fst_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_794_; 
v_fst_700_ = lean_ctor_get(v_snd_690_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_snd_690_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_snd_690_, 1);
lean_dec(v_unused_795_);
v___x_702_ = v_snd_690_;
v_isShared_703_ = v_isSharedCheck_794_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_fst_700_);
lean_dec(v_snd_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_794_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_793_; 
v_fst_704_ = lean_ctor_get(v_snd_691_, 0);
v_snd_705_ = lean_ctor_get(v_snd_691_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_snd_691_);
if (v_isSharedCheck_793_ == 0)
{
v___x_707_ = v_snd_691_;
v_isShared_708_ = v_isSharedCheck_793_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_inc(v_fst_704_);
lean_dec(v_snd_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_793_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
uint8_t v_failed_709_; size_t v_sz_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___y_715_; uint8_t v_failed_716_; uint8_t v___y_781_; lean_object* v___x_787_; 
v_failed_709_ = 0;
v_sz_710_ = lean_array_size(v_imports_678_);
lean_inc_ref(v_imports_678_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NER_loadedScan_spec__2(v_sz_710_, v___x_686_, v_imports_678_);
v___x_712_ = l_NER_canonicalImports(v___x_711_);
lean_inc(v___x_681_);
v___x_713_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_681_, v___x_668_);
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_expected_661_, v___x_713_);
if (lean_obj_tag(v___x_787_) == 0)
{
v___y_781_ = v_failed_709_;
goto v___jp_780_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_val_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = lean_array_get_size(v___x_712_);
v___x_790_ = lean_array_get_size(v_val_788_);
v___x_791_ = lean_nat_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec(v_val_788_);
v___y_781_ = v_failed_709_;
goto v___jp_780_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v___x_712_, v_val_788_, v___x_789_);
lean_dec(v_val_788_);
v___y_781_ = v___x_792_;
goto v___jp_780_;
}
}
v___jp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_718_);
lean_ctor_set(v___x_707_, 0, v___x_717_);
v___x_720_ = v___x_707_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_779_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_722_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_712_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_722_);
lean_ctor_set(v___x_702_, 0, v___x_721_);
v___x_724_ = v___x_702_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_778_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__6));
v___x_726_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_711_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_726_);
lean_ctor_set(v___x_698_, 0, v___x_725_);
v___x_728_ = v___x_698_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_777_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__7));
v___x_730_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_730_, 0, v___y_715_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_730_);
lean_ctor_set(v___x_694_, 0, v___x_729_);
v___x_732_ = v___x_694_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_776_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_733_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__8));
v___x_734_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_696_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__9));
v___x_737_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_700_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__10));
v___x_740_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_704_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__11));
v___x_743_ = lean_array_get_size(v_constants_679_);
v___x_744_ = l_Lean_JsonNumber_fromNat(v___x_743_);
v___x_745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_742_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__12));
v___x_748_ = l_Lean_JsonNumber_fromNat(v_snd_705_);
v___x_749_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_747_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_746_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_741_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_738_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_735_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_732_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_728_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_724_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_720_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_Json_mkObj(v___x_760_);
lean_dec_ref_known(v___x_760_, 2);
v___x_762_ = l_Lean_Json_compress(v___x_761_);
v___x_763_ = l_IO_FS_Handle_putStrLn(v_a_660_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_764_ = lean_box(v_failed_716_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_fst_692_);
v___x_766_ = lean_nat_add(v_i_664_, v_step_667_);
v___x_767_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg(v___x_657_, v___x_659_, v_env_658_, v_a_660_, v_expected_661_, v_range_662_, v___x_765_, v___x_766_);
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_fst_692_);
lean_dec_ref(v_env_658_);
v_a_768_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_763_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_763_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
}
v___jp_780_:
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = lean_array_get_size(v_fst_696_);
v___x_783_ = lean_nat_dec_eq(v___x_782_, v___x_680_);
if (v___x_783_ == 0)
{
lean_dec(v_fst_670_);
v___y_715_ = v___y_781_;
v_failed_716_ = v___x_668_;
goto v___jp_714_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_array_get_size(v_fst_700_);
v___x_785_ = lean_nat_dec_eq(v___x_784_, v___x_680_);
if (v___x_785_ == 0)
{
lean_dec(v_fst_670_);
v___y_715_ = v___y_781_;
v_failed_716_ = v___x_668_;
goto v___jp_714_;
}
else
{
if (v___y_781_ == 0)
{
lean_dec(v_fst_670_);
v___y_715_ = v___y_781_;
v_failed_716_ = v___x_668_;
goto v___jp_714_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_unbox(v_fst_670_);
lean_dec(v_fst_670_);
v___y_715_ = v___y_781_;
v_failed_716_ = v___x_786_;
goto v___jp_714_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_fst_670_);
lean_dec_ref(v_env_658_);
v_a_800_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_687_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_687_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg___boxed(lean_object* v___x_810_, lean_object* v_env_811_, lean_object* v___x_812_, lean_object* v_a_813_, lean_object* v_expected_814_, lean_object* v_range_815_, lean_object* v_b_816_, lean_object* v_i_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_810_, v_env_811_, v___x_812_, v_a_813_, v_expected_814_, v_range_815_, v_b_816_, v_i_817_);
lean_dec(v_i_817_);
lean_dec_ref(v_range_815_);
lean_dec_ref(v_expected_814_);
lean_dec(v_a_813_);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_810_);
return v_res_819_;
}
}
static lean_object* _init_l_NER_loadedScan___closed__0(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
v___x_821_ = lean_unsigned_to_nat(16u);
v___x_822_ = lean_mk_array(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_NER_loadedScan___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_obj_once(&l_NER_loadedScan___closed__0, &l_NER_loadedScan___closed__0_once, _init_l_NER_loadedScan___closed__0);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_NER_loadedScan___closed__2(void){
_start:
{
lean_object* v___x_826_; uint8_t v_failed_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_obj_once(&l_NER_loadedScan___closed__1, &l_NER_loadedScan___closed__1_once, _init_l_NER_loadedScan___closed__1);
v_failed_827_ = 0;
v___x_828_ = lean_box(v_failed_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_NER_loadedScan(lean_object* v_env_830_, lean_object* v_output_831_, lean_object* v_expected_832_){
_start:
{
uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_834_ = 1;
v___x_835_ = lean_io_prim_handle_mk(v_output_831_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; uint8_t v_failed_837_; lean_object* v_env_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v_failed_837_ = 0;
v_env_838_ = l_Lean_Environment_setExporting(v_env_830_, v_failed_837_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = l_Lean_Environment_header(v_env_838_);
lean_inc_ref(v___x_840_);
v___x_841_ = l_Lean_EnvironmentHeader_moduleNames(v___x_840_);
v___x_842_ = lean_array_get_size(v___x_841_);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_844_, 0, v___x_839_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = lean_obj_once(&l_NER_loadedScan___closed__2, &l_NER_loadedScan___closed__2_once, _init_l_NER_loadedScan___closed__2);
v___x_846_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_841_, v_env_838_, v___x_840_, v_a_836_, v_expected_832_, v___x_844_, v___x_845_, v___x_839_);
lean_dec_ref_known(v___x_844_, 3);
lean_dec(v_a_836_);
lean_dec_ref(v___x_840_);
lean_dec_ref(v___x_841_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_fst_851_; lean_object* v___x_853_; 
v_fst_851_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_fst_851_);
lean_dec(v_a_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_fst_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_fst_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v_env_830_);
v_a_864_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_835_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_835_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NER_loadedScan___boxed(lean_object* v_env_872_, lean_object* v_output_873_, lean_object* v_expected_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_NER_loadedScan(v_env_872_, v_output_873_, v_expected_874_);
lean_dec_ref(v_expected_874_);
lean_dec_ref(v_output_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(lean_object* v___x_877_, lean_object* v_env_878_, lean_object* v___x_879_, lean_object* v_a_880_, lean_object* v_expected_881_, lean_object* v_range_882_, lean_object* v_b_883_, lean_object* v_i_884_, lean_object* v_hs_885_, lean_object* v_hl_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___redArg(v___x_877_, v_env_878_, v___x_879_, v_a_880_, v_expected_881_, v_range_882_, v_b_883_, v_i_884_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3___boxed(lean_object* v___x_889_, lean_object* v_env_890_, lean_object* v___x_891_, lean_object* v_a_892_, lean_object* v_expected_893_, lean_object* v_range_894_, lean_object* v_b_895_, lean_object* v_i_896_, lean_object* v_hs_897_, lean_object* v_hl_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3(v___x_889_, v_env_890_, v___x_891_, v_a_892_, v_expected_893_, v_range_894_, v_b_895_, v_i_896_, v_hs_897_, v_hl_898_);
lean_dec(v_i_896_);
lean_dec_ref(v_range_894_);
lean_dec_ref(v_expected_893_);
lean_dec(v_a_892_);
lean_dec_ref(v___x_891_);
lean_dec_ref(v___x_889_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v_env_903_, lean_object* v_a_904_, lean_object* v_expected_905_, lean_object* v_range_906_, lean_object* v_b_907_, lean_object* v_i_908_, lean_object* v_hs_909_, lean_object* v_hl_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg(v___x_901_, v___x_902_, v_env_903_, v_a_904_, v_expected_905_, v_range_906_, v_b_907_, v_i_908_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___boxed(lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_env_915_, lean_object* v_a_916_, lean_object* v_expected_917_, lean_object* v_range_918_, lean_object* v_b_919_, lean_object* v_i_920_, lean_object* v_hs_921_, lean_object* v_hl_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3(v___x_913_, v___x_914_, v_env_915_, v_a_916_, v_expected_917_, v_range_918_, v_b_919_, v_i_920_, v_hs_921_, v_hl_922_);
lean_dec_ref(v_range_918_);
lean_dec_ref(v_expected_917_);
lean_dec(v_a_916_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v___x_913_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(size_t v_sz_925_, size_t v_i_926_, lean_object* v_bs_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_lt(v_i_926_, v_sz_925_);
if (v___x_928_ == 0)
{
return v_bs_927_;
}
else
{
lean_object* v_v_929_; lean_object* v___x_930_; lean_object* v_bs_x27_931_; lean_object* v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v___x_935_; 
v_v_929_ = lean_array_uget(v_bs_927_, v_i_926_);
v___x_930_ = lean_unsigned_to_nat(0u);
v_bs_x27_931_ = lean_array_uset(v_bs_927_, v_i_926_, v___x_930_);
v___x_932_ = l_String_toName(v_v_929_);
v___x_933_ = ((size_t)1ULL);
v___x_934_ = lean_usize_add(v_i_926_, v___x_933_);
v___x_935_ = lean_array_uset(v_bs_x27_931_, v_i_926_, v___x_932_);
v_i_926_ = v___x_934_;
v_bs_927_ = v___x_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4___boxed(lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_bs_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_941_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_boxed_940_, v_i_boxed_941_, v_bs_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_943_, size_t v_i_944_, lean_object* v_bs_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_946_ == 0)
{
return v_bs_945_;
}
else
{
lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v_bs_x27_949_; uint8_t v___x_950_; lean_object* v___x_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_v_947_ = lean_array_uget(v_bs_945_, v_i_944_);
v___x_948_ = lean_unsigned_to_nat(0u);
v_bs_x27_949_ = lean_array_uset(v_bs_945_, v_i_944_, v___x_948_);
v___x_950_ = 0;
v___x_951_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_951_, 0, v_v_947_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_946_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1 + 1, v___x_946_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1 + 2, v___x_950_);
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_944_, v___x_952_);
v___x_954_ = lean_array_uset(v_bs_x27_949_, v_i_944_, v___x_951_);
v_i_944_ = v___x_953_;
v_bs_945_ = v___x_954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_bs_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_960_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_959_, v_i_boxed_960_, v_bs_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_as_962_, size_t v_sz_963_, size_t v_i_964_, lean_object* v_b_965_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_lt(v_i_964_, v_sz_963_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v_b_965_);
return v___x_968_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_array_uget_borrowed(v_as_962_, v_i_964_);
lean_inc(v_a_969_);
v___x_970_ = l_Lean_Json_parse(v_a_969_);
v___x_971_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_n(v_a_972_, 2);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_974_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(v_a_972_, v___x_973_);
v___x_975_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NER_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_978_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(v_a_972_, v___x_977_);
v___x_979_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; size_t v___x_982_; size_t v___x_983_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_b_965_, v_a_976_, v_a_980_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_964_, v___x_982_);
v_i_964_ = v___x_983_;
v_b_965_ = v___x_981_;
goto _start;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_976_);
lean_dec_ref(v_b_965_);
v_a_985_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_979_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_979_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_a_972_);
lean_dec_ref(v_b_965_);
v_a_993_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_975_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_975_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_b_965_);
v_a_1001_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_971_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_971_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_as_1009_, lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_){
_start:
{
size_t v_sz_boxed_1014_; size_t v_i_boxed_1015_; lean_object* v_res_1016_; 
v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1015_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_as_1009_, v_sz_boxed_1014_, v_i_boxed_1015_, v_b_1012_);
lean_dec_ref(v_as_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_1017_, lean_object* v_b_1018_){
_start:
{
if (lean_obj_tag(v_as_x27_1017_) == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_b_1018_);
return v___x_1020_;
}
else
{
lean_object* v_head_1021_; lean_object* v_tail_1022_; lean_object* v_data_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_head_1021_ = lean_ctor_get(v_as_x27_1017_, 0);
v_tail_1022_ = lean_ctor_get(v_as_x27_1017_, 1);
v_data_1023_ = lean_ctor_get(v_head_1021_, 4);
lean_inc(v_data_1023_);
v___x_1024_ = l_Lean_MessageData_toString(v_data_1023_);
v___x_1025_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref_known(v___x_1025_, 1);
v___x_1026_ = lean_box(0);
v_as_x27_1017_ = v_tail_1022_;
v_b_1018_ = v___x_1026_;
goto _start;
}
else
{
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1028_, v_b_1029_);
lean_dec(v_as_x27_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(lean_object* v___y_1046_, lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, uint8_t v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_snd_1055_; uint8_t v___x_1060_; lean_object* v_a_1062_; 
v___x_1060_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(v_b_1050_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Elab_Command_getRef___redArg(v___y_1051_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1051_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_quotContext_x3f_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1085_; 
lean_dec_ref_known(v___x_1080_, 1);
v_quotContext_x3f_1081_ = lean_ctor_get(v___y_1051_, 5);
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_1083_ = lean_string_dec_eq(v___y_1046_, v___x_1082_);
v_a_1084_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
v___x_1085_ = l_Lean_SourceInfo_fromRef(v_a_1079_, v___x_1083_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v_quotContext_x3f_1081_) == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_getMainModule___at___00Lean_Linter_Coe_coeLinter_spec__0___redArg(v___y_1052_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref_known(v___x_1105_, 1);
goto v___jp_1086_;
}
else
{
lean_object* v_a_1106_; 
lean_dec(v___x_1085_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_a_1062_ = v_a_1106_;
goto v___jp_1061_;
}
}
else
{
goto v___jp_1086_;
}
v___jp_1086_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__5));
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__6));
lean_inc_n(v___x_1085_, 2);
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1085_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__7));
v___x_1091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1085_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
lean_inc(v_a_1084_);
v___x_1092_ = lean_mk_syntax_ident(v_a_1084_);
v___x_1093_ = l_Lean_Syntax_node3(v___x_1085_, v___x_1087_, v___x_1089_, v___x_1091_, v___x_1092_);
v___x_1094_ = l_Lean_Elab_Command_elabCommand(v___x_1093_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1094_, 1);
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__8));
v___x_1096_ = lean_string_append(v___x_1095_, v___y_1046_);
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__9));
v___x_1098_ = lean_string_append(v___x_1096_, v___x_1097_);
lean_inc_n(v_a_1084_, 2);
v___x_1099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1084_, v___x_1060_);
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = l_NEP_audit(v_a_1084_, v___x_1100_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1101_, 1);
v___x_1102_ = lean_box(v_b_1050_);
v_snd_1055_ = v___x_1102_;
goto v___jp_1054_;
}
else
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1101_, 1);
v_a_1062_ = v_a_1103_;
goto v___jp_1061_;
}
}
else
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1094_, 1);
v_a_1062_ = v_a_1104_;
goto v___jp_1061_;
}
}
}
else
{
lean_object* v_a_1107_; 
lean_dec(v_a_1079_);
v_a_1107_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1080_, 1);
v_a_1062_ = v_a_1107_;
goto v___jp_1061_;
}
}
else
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1078_, 1);
v_a_1062_ = v_a_1108_;
goto v___jp_1061_;
}
}
v___jp_1054_:
{
size_t v___x_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_i_1049_, v___x_1056_);
v___x_1058_ = lean_unbox(v_snd_1055_);
lean_dec(v_snd_1055_);
v_i_1049_ = v___x_1057_;
v_b_1050_ = v___x_1058_;
goto _start;
}
v___jp_1061_:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_Exception_isInterrupt(v_a_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = l_Lean_Exception_toMessageData(v_a_1062_);
v___x_1065_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_1064_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1065_, 1);
v___x_1066_ = lean_box(v___x_1060_);
v_snd_1055_ = v___x_1066_;
goto v___jp_1054_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1065_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
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
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1062_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___boxed(lean_object* v___y_1109_, lean_object* v_as_1110_, lean_object* v_sz_1111_, lean_object* v_i_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
size_t v_sz_boxed_1117_; size_t v_i_boxed_1118_; uint8_t v_b_boxed_1119_; lean_object* v_res_1120_; 
v_sz_boxed_1117_ = lean_unbox_usize(v_sz_1111_);
lean_dec(v_sz_1111_);
v_i_boxed_1118_ = lean_unbox_usize(v_i_1112_);
lean_dec(v_i_1112_);
v_b_boxed_1119_ = lean_unbox(v_b_1113_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_1109_, v_as_1110_, v_sz_boxed_1117_, v_i_boxed_1118_, v_b_boxed_1119_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_as_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1120_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_unsigned_to_nat(16u);
v___x_1127_ = lean_mk_array(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l_main___closed__11(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_main___closed__10));
v___x_1136_ = l_Lean_FileMap_ofString(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_main___closed__12(void){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1137_ = 0;
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_obj_once(&l_main___closed__11, &l_main___closed__11_once, _init_l_main___closed__11);
v___x_1144_ = ((lean_object*)(l_main___closed__9));
v___x_1145_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___x_1143_);
lean_ctor_set(v___x_1145_, 2, v___x_1142_);
lean_ctor_set(v___x_1145_, 3, v___x_1142_);
lean_ctor_set(v___x_1145_, 4, v___x_1141_);
lean_ctor_set(v___x_1145_, 5, v___x_1140_);
lean_ctor_set(v___x_1145_, 6, v___x_1139_);
lean_ctor_set(v___x_1145_, 7, v___x_1138_);
lean_ctor_set(v___x_1145_, 8, v___x_1140_);
lean_ctor_set(v___x_1145_, 9, v___x_1140_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*10, v___x_1137_);
return v___x_1145_;
}
}
static lean_object* _init_l_main___closed__13(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_unsigned_to_nat(32u);
v___x_1147_ = lean_mk_empty_array_with_capacity(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1149_ = ((size_t)5ULL);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_unsigned_to_nat(32u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_obj_once(&l_main___closed__13, &l_main___closed__13_once, _init_l_main___closed__13);
v___x_1154_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v___x_1150_);
lean_ctor_set(v___x_1154_, 3, v___x_1150_);
lean_ctor_set_usize(v___x_1154_, 4, v___x_1149_);
return v___x_1154_;
}
}
static lean_object* _init_l_main___closed__15(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_box(1);
v___x_1156_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
v___x_1157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_ctor_set(v___x_1157_, 2, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = 1;
v___x_1183_ = lean_box_uint32(v___x_1182_);
return v___x_1183_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = 0;
v___x_1185_ = lean_box_uint32(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l_main___boxed__const__3(void){
_start:
{
uint32_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = 2;
v___x_1187_ = lean_box_uint32(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1188_){
_start:
{
uint8_t v___y_1191_; uint32_t v___y_1192_; lean_object* v___y_1193_; uint32_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1237_; size_t v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint32_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1268_; size_t v___y_1269_; uint32_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v_roots_1282_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = l_NFA__MemoryLimit_set();
v___x_1364_ = ((lean_object*)(l_main___closed__16));
v___x_1365_ = l_Lean_findSysroot(v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = lean_box(0);
v___x_1368_ = l_Lean_initSearchPath(v_a_1366_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
lean_dec_ref_known(v___x_1368_, 1);
v___x_1369_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___y_1420_; 
lean_dec_ref_known(v___x_1369_, 1);
if (lean_obj_tag(v_args_1188_) == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l_main___closed__28));
v___y_1420_ = v___x_1431_;
goto v___jp_1419_;
}
else
{
lean_object* v_head_1432_; 
v_head_1432_ = lean_ctor_get(v_args_1188_, 0);
lean_inc(v_head_1432_);
lean_dec_ref_known(v_args_1188_, 2);
v___y_1420_ = v_head_1432_;
goto v___jp_1419_;
}
v___jp_1370_:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_IO_FS_readFile(v___y_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Json_parse(v_a_1375_);
v___x_1377_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1_spec__2(v_a_1378_);
v___x_1380_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; size_t v_sz_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_sz_1382_ = lean_array_size(v_a_1381_);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_1382_, v___x_1383_, v_a_1381_);
v___y_1280_ = v___y_1371_;
v___y_1281_ = v___y_1372_;
v_roots_1282_ = v___x_1384_;
goto v___jp_1279_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v___y_1372_);
v_a_1385_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1380_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v___y_1372_);
v_a_1393_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1377_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1377_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___y_1372_);
v_a_1401_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1374_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1374_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
v___jp_1409_:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_main___closed__8));
v___x_1414_ = lean_string_dec_eq(v___y_1410_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_main___closed__17));
v___x_1416_ = lean_string_dec_eq(v___y_1410_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = ((lean_object*)(l_main___closed__18));
v___y_1371_ = v_fst_1411_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___x_1417_;
goto v___jp_1370_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = ((lean_object*)(l_main___closed__19));
v___y_1371_ = v_fst_1411_;
v___y_1372_ = v___y_1410_;
v___y_1373_ = v___x_1418_;
goto v___jp_1370_;
}
}
else
{
lean_inc_ref(v_snd_1412_);
v___y_1280_ = v_fst_1411_;
v___y_1281_ = v___y_1410_;
v_roots_1282_ = v_snd_1412_;
goto v___jp_1279_;
}
}
v___jp_1419_:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_main___closed__8));
v___x_1422_ = lean_string_dec_eq(v___y_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_main___closed__17));
v___x_1424_ = lean_string_dec_eq(v___y_1420_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_main___closed__22));
v___x_1426_ = ((lean_object*)(l_NER_referenceNames___closed__0));
v___y_1410_ = v___y_1420_;
v_fst_1411_ = v___x_1425_;
v_snd_1412_ = v___x_1426_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_main___closed__27));
v___x_1428_ = ((lean_object*)(l_NER_referenceNames___closed__0));
v___y_1410_ = v___y_1420_;
v_fst_1411_ = v___x_1427_;
v_snd_1412_ = v___x_1428_;
goto v___jp_1409_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_main___closed__22));
v___x_1430_ = ((lean_object*)(l_NER_referenceNames___closed__0));
v___y_1410_ = v___y_1420_;
v_fst_1411_ = v___x_1429_;
v_snd_1412_ = v___x_1430_;
goto v___jp_1409_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_args_1188_);
v_a_1433_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1369_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1369_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_args_1188_);
v_a_1441_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1368_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1368_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_args_1188_);
v_a_1449_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1365_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1365_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
v___jp_1190_:
{
lean_object* v___x_1194_; 
lean_inc_ref(v___y_1193_);
v___x_1194_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___y_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v___x_1194_, 0);
lean_dec(v_unused_1207_);
v___x_1196_ = v___x_1194_;
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v___x_1194_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
if (v___y_1191_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box_uint32(v___y_1192_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = l_main___boxed__const__1;
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1202_);
v___x_1204_ = v___x_1196_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1194_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1194_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
v___jp_1216_:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_NER_loadedScan(v___y_1218_, v___y_1220_, v___y_1219_);
lean_dec_ref(v___y_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; uint8_t v___x_1223_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_unbox(v_a_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_main___closed__0));
v___x_1225_ = lean_unbox(v_a_1222_);
lean_dec(v_a_1222_);
v___y_1191_ = v___x_1225_;
v___y_1192_ = v___y_1217_;
v___y_1193_ = v___x_1224_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_main___closed__1));
v___x_1227_ = lean_unbox(v_a_1222_);
lean_dec(v_a_1222_);
v___y_1191_ = v___x_1227_;
v___y_1192_ = v___y_1217_;
v___y_1193_ = v___x_1226_;
goto v___jp_1190_;
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1228_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1221_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1221_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_IO_FS_lines(v___y_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; size_t v_sz_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v_sz_1245_ = lean_array_size(v_a_1244_);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_a_1244_, v_sz_1245_, v___y_1238_, v___y_1239_);
lean_dec(v_a_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
if (v___y_1237_ == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = ((lean_object*)(l_main___closed__2));
v___y_1217_ = v___y_1241_;
v___y_1218_ = v___y_1240_;
v___y_1219_ = v_a_1247_;
v___y_1220_ = v___x_1248_;
goto v___jp_1216_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1250_ = ((lean_object*)(l_main___closed__3));
v___y_1217_ = v___y_1241_;
v___y_1218_ = v___y_1240_;
v___y_1219_ = v_a_1249_;
v___y_1220_ = v___x_1250_;
goto v___jp_1216_;
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v___y_1240_);
v_a_1251_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1246_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___y_1240_);
lean_dec_ref(v___y_1239_);
v_a_1259_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1243_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1243_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___y_1268_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_1276_ = lean_string_dec_eq(v___y_1272_, v___x_1275_);
lean_dec_ref(v___y_1272_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = ((lean_object*)(l_main___closed__5));
v___y_1237_ = v___x_1276_;
v___y_1238_ = v___y_1269_;
v___y_1239_ = v___x_1274_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1270_;
v___y_1242_ = v___x_1277_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = ((lean_object*)(l_main___closed__6));
v___y_1237_ = v___x_1276_;
v___y_1238_ = v___y_1269_;
v___y_1239_ = v___x_1274_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1270_;
v___y_1242_ = v___x_1278_;
goto v___jp_1236_;
}
}
v___jp_1279_:
{
size_t v_sz_1283_; size_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint32_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; uint8_t v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_sz_1283_ = lean_array_size(v___y_1280_);
v___x_1284_ = ((size_t)0ULL);
lean_inc_ref(v___y_1280_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_1283_, v___x_1284_, v___y_1280_);
v___x_1286_ = l_Lean_Options_empty;
v___x_1287_ = 0;
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = ((lean_object*)(l_main___closed__7));
v___x_1290_ = 0;
v___x_1291_ = 1;
v___x_1292_ = 2;
v___x_1293_ = lean_box(1);
v___x_1294_ = l_Lean_importModules(v___x_1285_, v___x_1286_, v___x_1287_, v___x_1289_, v___x_1290_, v___x_1291_, v___x_1292_, v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = ((lean_object*)(l_main___closed__8));
v___x_1297_ = lean_string_dec_eq(v___y_1281_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2___closed__0));
v___x_1299_ = lean_string_dec_eq(v___y_1281_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; size_t v_sz_1304_; lean_object* v___x_1305_; 
v___x_1300_ = lean_obj_once(&l_main___closed__12, &l_main___closed__12_once, _init_l_main___closed__12);
v___x_1301_ = lean_obj_once(&l_main___closed__15, &l_main___closed__15_once, _init_l_main___closed__15);
v___x_1302_ = l_Lean_Elab_Command_mkState(v_a_1295_, v___x_1301_, v___x_1286_);
v___x_1303_ = lean_st_mk_ref(v___x_1302_);
v_sz_1304_ = lean_array_size(v_roots_1282_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__2(v___y_1281_, v_roots_1282_, v_sz_1304_, v___x_1284_, v___x_1290_, v___x_1300_, v___x_1303_);
lean_dec_ref(v_roots_1282_);
lean_dec_ref(v___y_1281_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v_messages_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = lean_st_ref_get(v___x_1303_);
lean_dec(v___x_1303_);
v_messages_1308_ = lean_ctor_get(v___x_1307_, 1);
lean_inc_ref(v_messages_1308_);
lean_dec(v___x_1307_);
v___x_1309_ = l_Lean_MessageLog_toList(v_messages_1308_);
lean_dec_ref(v_messages_1308_);
v___x_1310_ = lean_box(0);
v___x_1311_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v___x_1309_, v___x_1310_);
lean_dec(v___x_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1324_; 
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1325_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1324_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1324_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = l_main___boxed__const__2;
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1316_);
v___x_1318_ = v___x_1313_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = l_main___boxed__const__1;
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_a_1306_);
v_a_1326_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1311_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1311_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v___x_1303_);
v_a_1334_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1335_ = l_Lean_Exception_toMessageData(v_a_1334_);
v___x_1336_ = l_Lean_MessageData_toString(v___x_1335_);
v___x_1337_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1346_);
v___x_1339_ = v___x_1337_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = l_main___boxed__const__3;
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_dec_ref(v_roots_1282_);
v___y_1268_ = v___x_1288_;
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1287_;
v___y_1271_ = v_a_1295_;
v___y_1272_ = v___y_1281_;
goto v___jp_1267_;
}
}
else
{
lean_dec_ref(v_roots_1282_);
v___y_1268_ = v___x_1288_;
v___y_1269_ = v___x_1284_;
v___y_1270_ = v___x_1287_;
v___y_1271_ = v_a_1295_;
v___y_1272_ = v___y_1281_;
goto v___jp_1267_;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_roots_1282_);
lean_dec_ref(v___y_1281_);
v_a_1355_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1294_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1294_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = _lean_main(v_args_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_1460_, lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1461_, v_b_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_1466_, lean_object* v_as_x27_1467_, lean_object* v_b_1468_, lean_object* v_a_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_1466_, v_as_x27_1467_, v_b_1468_, v_a_1469_);
lean_dec(v_as_x27_1467_);
lean_dec(v_as_1466_);
return v_res_1471_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_NFA__WALKER(uint8_t builtin);
lean_object* initialize_NFA__MemoryLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NKJ__Driver(uint8_t builtin) {
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
  res = initialize_NKJ__Driver(1 /* builtin */);
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
