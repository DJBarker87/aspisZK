// Lean compiler output
// Module: NNH8_RuntimeScan
// Imports: public import Init public meta import Init public import Lean
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
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
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Array_contains___at___00Lean_Server_FileWorker_handlePostRequestSpecialCases_spec__3(lean_object*, lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*);
lean_object* l_IO_FS_lines(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_NNH8__RuntimeScan_referenceNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NNH8__RuntimeScan_referenceNames___closed__0 = (const lean_object*)&l_NNH8__RuntimeScan_referenceNames___closed__0_value;
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_referenceNames(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_NNH8__RuntimeScan_canonicalImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NNH8__RuntimeScan_canonicalImports___closed__0 = (const lean_object*)&l_NNH8__RuntimeScan_canonicalImports___closed__0_value;
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_canonicalImports(lean_object*);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_canonicalImports___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_NNH8__RuntimeScan_importsMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_importsMatch___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_quotTag(uint8_t);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_quotTag___boxed(lean_object*);
LEAN_EXPORT uint8_t l_NNH8__RuntimeScan_sameDeclaration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_sameDeclaration___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "previous"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "current"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_identical"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reason"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "serialized declaration differs from selected owner"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__6_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "phase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "own_declaration"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__2_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "loader_imports"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "imports_match"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dangling"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "duplicate_owners"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "cached_replicas"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__10_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declarations"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edges"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_NNH8__RuntimeScan_loadedScan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NNH8__RuntimeScan_loadedScan___closed__0;
static lean_once_cell_t l_NNH8__RuntimeScan_loadedScan___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NNH8__RuntimeScan_loadedScan___closed__1;
static lean_once_cell_t l_NNH8__RuntimeScan_loadedScan___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NNH8__RuntimeScan_loadedScan___closed__2;
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_loadedScan(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_loadedScan___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "NNH8_EXPECTED_IMPORTS.jsonl"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static lean_once_cell_t l_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__1;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NNH8_LOADED_scan.jsonl"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NFN_SCAN_ZERO_DANGLING"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_string_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "NFN_SCAN_FAILED"};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_array_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "queryscan"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "scan"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_string_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "TAS_G0_COMBINED_IMPORT"};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_ctor_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__9_value),LEAN_SCALAR_PTR_LITERAL(112, 152, 173, 95, 81, 141, 242, 188)}};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_array_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__10_value)}};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "small"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg(lean_object* v_as_x27_1_, lean_object* v_b_2_){
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg___boxed(lean_object* v_as_x27_11_, lean_object* v_b_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg(v_as_x27_11_, v_b_12_);
lean_dec(v_as_x27_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_referenceNames(lean_object* v_c_16_){
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
v___x_52_ = ((lean_object*)(l_NNH8__RuntimeScan_referenceNames___closed__0));
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
v___x_49_ = l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg(v_rules_46_, v_refs_48_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0(lean_object* v_as_55_, lean_object* v_as_x27_56_, lean_object* v_b_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___redArg(v_as_x27_56_, v_b_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0___boxed(lean_object* v_as_60_, lean_object* v_as_x27_61_, lean_object* v_b_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_forIn_x27_loop___at___00NNH8__RuntimeScan_referenceNames_spec__0(v_as_60_, v_as_x27_61_, v_b_62_, v_a_63_);
lean_dec(v_as_x27_61_);
lean_dec(v_as_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0(lean_object* v_as_65_, size_t v_sz_66_, size_t v_i_67_, lean_object* v_b_68_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0___boxed(lean_object* v_as_78_, lean_object* v_sz_79_, lean_object* v_i_80_, lean_object* v_b_81_){
_start:
{
size_t v_sz_boxed_82_; size_t v_i_boxed_83_; lean_object* v_res_84_; 
v_sz_boxed_82_ = lean_unbox_usize(v_sz_79_);
lean_dec(v_sz_79_);
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0(v_as_78_, v_sz_boxed_82_, v_i_boxed_83_, v_b_81_);
lean_dec_ref(v_as_78_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_canonicalImports(lean_object* v_xs_87_){
_start:
{
lean_object* v_result_88_; size_t v_sz_89_; size_t v___x_90_; lean_object* v___x_91_; 
v_result_88_ = ((lean_object*)(l_NNH8__RuntimeScan_canonicalImports___closed__0));
v_sz_89_ = lean_array_size(v_xs_87_);
v___x_90_ = ((size_t)0ULL);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_canonicalImports_spec__0(v_xs_87_, v_sz_89_, v___x_90_, v_result_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_canonicalImports___boxed(lean_object* v_xs_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_NNH8__RuntimeScan_canonicalImports(v_xs_92_);
lean_dec_ref(v_xs_92_);
return v_res_93_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(lean_object* v_xs_94_, lean_object* v_ys_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_zero_97_; uint8_t v_isZero_98_; 
v_zero_97_ = lean_unsigned_to_nat(0u);
v_isZero_98_ = lean_nat_dec_eq(v_x_96_, v_zero_97_);
if (v_isZero_98_ == 1)
{
lean_dec(v_x_96_);
return v_isZero_98_;
}
else
{
lean_object* v_one_99_; lean_object* v_n_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_one_99_ = lean_unsigned_to_nat(1u);
v_n_100_ = lean_nat_sub(v_x_96_, v_one_99_);
lean_dec(v_x_96_);
v___x_101_ = lean_array_fget_borrowed(v_xs_94_, v_n_100_);
v___x_102_ = lean_array_fget_borrowed(v_ys_95_, v_n_100_);
v___x_103_ = lean_string_dec_eq(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_n_100_);
return v___x_103_;
}
else
{
v_x_96_ = v_n_100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg___boxed(lean_object* v_xs_105_, lean_object* v_ys_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(v_xs_105_, v_ys_106_, v_x_107_);
lean_dec_ref(v_ys_106_);
lean_dec_ref(v_xs_105_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_NNH8__RuntimeScan_importsMatch(lean_object* v_actual_110_, lean_object* v_expected_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_112_ = l_NNH8__RuntimeScan_canonicalImports(v_actual_110_);
v___x_113_ = lean_array_get_size(v___x_112_);
v___x_114_ = lean_array_get_size(v_expected_111_);
v___x_115_ = lean_nat_dec_eq(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec_ref(v___x_112_);
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(v___x_112_, v_expected_111_, v___x_113_);
lean_dec_ref(v___x_112_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_importsMatch___boxed(lean_object* v_actual_117_, lean_object* v_expected_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_NNH8__RuntimeScan_importsMatch(v_actual_117_, v_expected_118_);
lean_dec_ref(v_expected_118_);
lean_dec_ref(v_actual_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0(lean_object* v_xs_121_, lean_object* v_ys_122_, lean_object* v_hsz_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(v_xs_121_, v_ys_122_, v_x_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___boxed(lean_object* v_xs_127_, lean_object* v_ys_128_, lean_object* v_hsz_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0(v_xs_127_, v_ys_128_, v_hsz_129_, v_x_130_, v_x_131_);
lean_dec_ref(v_ys_128_);
lean_dec_ref(v_xs_127_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_quotTag(uint8_t v_x_134_){
_start:
{
switch(v_x_134_)
{
case 0:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(0u);
return v___x_135_;
}
case 1:
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(1u);
return v___x_136_;
}
case 2:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(2u);
return v___x_137_;
}
default: 
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(3u);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_quotTag___boxed(lean_object* v_x_139_){
_start:
{
uint8_t v_x_44__boxed_140_; lean_object* v_res_141_; 
v_x_44__boxed_140_ = lean_unbox(v_x_139_);
v_res_141_ = l_NNH8__RuntimeScan_quotTag(v_x_44__boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT uint8_t l_NNH8__RuntimeScan_sameDeclaration(lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
uint8_t v___y_145_; uint8_t v___y_146_; uint8_t v___y_147_; uint8_t v___y_149_; uint8_t v___y_150_; uint8_t v___y_151_; uint8_t v___y_152_; uint8_t v___y_153_; 
switch(lean_obj_tag(v_a_142_))
{
case 0:
{
if (lean_obj_tag(v_b_143_) == 0)
{
lean_object* v_val_154_; lean_object* v_val_155_; uint8_t v___x_156_; 
v_val_154_ = lean_ctor_get(v_a_142_, 0);
v_val_155_ = lean_ctor_get(v_b_143_, 0);
v___x_156_ = l_Lean_instBEqAxiomVal_beq(v_val_154_, v_val_155_);
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
case 1:
{
if (lean_obj_tag(v_b_143_) == 1)
{
lean_object* v_val_158_; lean_object* v_val_159_; uint8_t v___x_160_; 
v_val_158_ = lean_ctor_get(v_a_142_, 0);
v_val_159_ = lean_ctor_get(v_b_143_, 0);
v___x_160_ = l_Lean_instBEqDefinitionVal_beq(v_val_158_, v_val_159_);
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
}
case 2:
{
if (lean_obj_tag(v_b_143_) == 2)
{
lean_object* v_val_162_; lean_object* v_val_163_; lean_object* v_toConstantVal_164_; lean_object* v_all_165_; lean_object* v_toConstantVal_166_; lean_object* v_all_167_; uint8_t v___x_168_; 
v_val_162_ = lean_ctor_get(v_a_142_, 0);
v_val_163_ = lean_ctor_get(v_b_143_, 0);
v_toConstantVal_164_ = lean_ctor_get(v_val_162_, 0);
v_all_165_ = lean_ctor_get(v_val_162_, 2);
v_toConstantVal_166_ = lean_ctor_get(v_val_163_, 0);
v_all_167_ = lean_ctor_get(v_val_163_, 2);
v___x_168_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_164_, v_toConstantVal_166_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_165_, v_all_167_);
return v___x_169_;
}
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
case 3:
{
if (lean_obj_tag(v_b_143_) == 3)
{
lean_object* v_val_171_; lean_object* v_val_172_; uint8_t v___x_173_; 
v_val_171_ = lean_ctor_get(v_a_142_, 0);
v_val_172_ = lean_ctor_get(v_b_143_, 0);
v___x_173_ = l_Lean_instBEqOpaqueVal_beq(v_val_171_, v_val_172_);
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
case 4:
{
if (lean_obj_tag(v_b_143_) == 4)
{
lean_object* v_val_175_; lean_object* v_val_176_; lean_object* v_toConstantVal_177_; uint8_t v_kind_178_; lean_object* v_toConstantVal_179_; uint8_t v_kind_180_; uint8_t v___x_181_; 
v_val_175_ = lean_ctor_get(v_a_142_, 0);
v_val_176_ = lean_ctor_get(v_b_143_, 0);
v_toConstantVal_177_ = lean_ctor_get(v_val_175_, 0);
v_kind_178_ = lean_ctor_get_uint8(v_val_175_, sizeof(void*)*1);
v_toConstantVal_179_ = lean_ctor_get(v_val_176_, 0);
v_kind_180_ = lean_ctor_get_uint8(v_val_176_, sizeof(void*)*1);
v___x_181_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_177_, v_toConstantVal_179_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_NNH8__RuntimeScan_quotTag(v_kind_178_);
v___x_183_ = l_NNH8__RuntimeScan_quotTag(v_kind_180_);
v___x_184_ = lean_nat_dec_eq(v___x_182_, v___x_183_);
lean_dec(v___x_183_);
lean_dec(v___x_182_);
return v___x_184_;
}
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
case 5:
{
if (lean_obj_tag(v_b_143_) == 5)
{
lean_object* v_val_186_; lean_object* v_val_187_; lean_object* v_toConstantVal_188_; lean_object* v_numParams_189_; lean_object* v_numIndices_190_; lean_object* v_all_191_; lean_object* v_ctors_192_; lean_object* v_numNested_193_; uint8_t v_isRec_194_; uint8_t v_isUnsafe_195_; uint8_t v_isReflexive_196_; lean_object* v_toConstantVal_197_; lean_object* v_numParams_198_; lean_object* v_numIndices_199_; lean_object* v_all_200_; lean_object* v_ctors_201_; lean_object* v_numNested_202_; uint8_t v_isRec_203_; uint8_t v_isUnsafe_204_; uint8_t v_isReflexive_205_; uint8_t v___y_207_; uint8_t v___x_212_; 
v_val_186_ = lean_ctor_get(v_a_142_, 0);
v_val_187_ = lean_ctor_get(v_b_143_, 0);
v_toConstantVal_188_ = lean_ctor_get(v_val_186_, 0);
v_numParams_189_ = lean_ctor_get(v_val_186_, 1);
v_numIndices_190_ = lean_ctor_get(v_val_186_, 2);
v_all_191_ = lean_ctor_get(v_val_186_, 3);
v_ctors_192_ = lean_ctor_get(v_val_186_, 4);
v_numNested_193_ = lean_ctor_get(v_val_186_, 5);
v_isRec_194_ = lean_ctor_get_uint8(v_val_186_, sizeof(void*)*6);
v_isUnsafe_195_ = lean_ctor_get_uint8(v_val_186_, sizeof(void*)*6 + 1);
v_isReflexive_196_ = lean_ctor_get_uint8(v_val_186_, sizeof(void*)*6 + 2);
v_toConstantVal_197_ = lean_ctor_get(v_val_187_, 0);
v_numParams_198_ = lean_ctor_get(v_val_187_, 1);
v_numIndices_199_ = lean_ctor_get(v_val_187_, 2);
v_all_200_ = lean_ctor_get(v_val_187_, 3);
v_ctors_201_ = lean_ctor_get(v_val_187_, 4);
v_numNested_202_ = lean_ctor_get(v_val_187_, 5);
v_isRec_203_ = lean_ctor_get_uint8(v_val_187_, sizeof(void*)*6);
v_isUnsafe_204_ = lean_ctor_get_uint8(v_val_187_, sizeof(void*)*6 + 1);
v_isReflexive_205_ = lean_ctor_get_uint8(v_val_187_, sizeof(void*)*6 + 2);
v___x_212_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_188_, v_toConstantVal_197_);
if (v___x_212_ == 0)
{
v___y_207_ = v___x_212_;
goto v___jp_206_;
}
else
{
uint8_t v___x_213_; 
v___x_213_ = lean_nat_dec_eq(v_numParams_189_, v_numParams_198_);
v___y_207_ = v___x_213_;
goto v___jp_206_;
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
return v___y_207_;
}
else
{
uint8_t v___x_208_; 
v___x_208_ = lean_nat_dec_eq(v_numIndices_190_, v_numIndices_199_);
if (v___x_208_ == 0)
{
return v___x_208_;
}
else
{
uint8_t v___x_209_; 
v___x_209_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_all_191_, v_all_200_);
if (v___x_209_ == 0)
{
return v___x_209_;
}
else
{
uint8_t v___x_210_; 
v___x_210_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Environment_Replay_replayConstant_spec__4(v_ctors_192_, v_ctors_201_);
if (v___x_210_ == 0)
{
return v___x_210_;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = lean_nat_dec_eq(v_numNested_193_, v_numNested_202_);
if (v___x_211_ == 0)
{
return v___x_211_;
}
else
{
if (v_isRec_194_ == 0)
{
if (v_isRec_203_ == 0)
{
v___y_149_ = v_isReflexive_205_;
v___y_150_ = v_isReflexive_196_;
v___y_151_ = v_isUnsafe_195_;
v___y_152_ = v___x_211_;
v___y_153_ = v_isUnsafe_204_;
goto v___jp_148_;
}
else
{
return v_isRec_194_;
}
}
else
{
if (v_isRec_203_ == 0)
{
return v_isRec_203_;
}
else
{
v___y_149_ = v_isReflexive_205_;
v___y_150_ = v_isReflexive_196_;
v___y_151_ = v_isUnsafe_195_;
v___y_152_ = v___x_211_;
v___y_153_ = v_isUnsafe_204_;
goto v___jp_148_;
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
uint8_t v___x_214_; 
v___x_214_ = 0;
return v___x_214_;
}
}
case 6:
{
if (lean_obj_tag(v_b_143_) == 6)
{
lean_object* v_val_215_; lean_object* v_val_216_; uint8_t v___x_217_; 
v_val_215_ = lean_ctor_get(v_a_142_, 0);
v_val_216_ = lean_ctor_get(v_b_143_, 0);
v___x_217_ = l_Lean_instBEqConstructorVal_beq(v_val_215_, v_val_216_);
return v___x_217_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
}
default: 
{
if (lean_obj_tag(v_b_143_) == 7)
{
lean_object* v_val_219_; lean_object* v_val_220_; uint8_t v___x_221_; 
v_val_219_ = lean_ctor_get(v_a_142_, 0);
v_val_220_ = lean_ctor_get(v_b_143_, 0);
v___x_221_ = l_Lean_instBEqRecursorVal_beq(v_val_219_, v_val_220_);
return v___x_221_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
v___jp_144_:
{
if (v___y_146_ == 0)
{
if (v___y_145_ == 0)
{
return v___y_147_;
}
else
{
return v___y_146_;
}
}
else
{
return v___y_145_;
}
}
v___jp_148_:
{
if (v___y_151_ == 0)
{
if (v___y_153_ == 0)
{
v___y_145_ = v___y_149_;
v___y_146_ = v___y_150_;
v___y_147_ = v___y_152_;
goto v___jp_144_;
}
else
{
return v___y_151_;
}
}
else
{
if (v___y_153_ == 0)
{
return v___y_153_;
}
else
{
v___y_145_ = v___y_149_;
v___y_146_ = v___y_150_;
v___y_147_ = v___y_152_;
goto v___jp_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_sameDeclaration___boxed(lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_NNH8__RuntimeScan_sameDeclaration(v_a_223_, v_b_224_);
lean_dec_ref(v_b_224_);
lean_dec_ref(v_a_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0(lean_object* v_env_229_, lean_object* v_val_230_, lean_object* v_as_231_, size_t v_sz_232_, size_t v_i_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_a_237_; uint8_t v___x_241_; 
v___x_241_ = lean_usize_dec_lt(v_i_233_, v_sz_232_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec_ref(v_env_229_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v_b_234_);
return v___x_242_;
}
else
{
lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_274_; 
v_fst_243_ = lean_ctor_get(v_b_234_, 0);
v_snd_244_ = lean_ctor_get(v_b_234_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_b_234_);
if (v_isSharedCheck_274_ == 0)
{
v___x_246_ = v_b_234_;
v_isShared_247_ = v_isSharedCheck_274_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_inc(v_fst_243_);
lean_dec(v_b_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_274_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_checked_248_; lean_object* v___x_249_; lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_checked_248_ = lean_ctor_get(v_env_229_, 2);
v___x_249_ = lean_unsigned_to_nat(1u);
v_a_250_ = lean_array_uget_borrowed(v_as_231_, v_i_233_);
v___x_251_ = lean_nat_add(v_snd_244_, v___x_249_);
lean_dec(v_snd_244_);
lean_inc_ref(v_checked_248_);
v___x_252_ = lean_task_get_own(v_checked_248_);
lean_inc(v_a_250_);
v___x_253_ = lean_environment_find(v___x_252_, v_a_250_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__0));
v___x_255_ = l_Lean_ConstantInfo_name(v_val_230_);
v___x_256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_255_, v___x_241_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_257_);
lean_ctor_set(v___x_246_, 0, v___x_254_);
v___x_259_ = v___x_246_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_270_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__1));
lean_inc(v_a_250_);
v___x_261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_250_, v___x_241_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_259_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_Json_mkObj(v___x_266_);
lean_dec_ref_known(v___x_266_, 2);
v___x_268_ = lean_array_push(v_fst_243_, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_251_);
v_a_237_ = v___x_269_;
goto v___jp_236_;
}
}
else
{
lean_object* v___x_272_; 
lean_dec_ref_known(v___x_253_, 1);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_251_);
v___x_272_ = v___x_246_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_243_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_251_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_a_237_ = v___x_272_;
goto v___jp_236_;
}
}
}
}
v___jp_236_:
{
size_t v___x_238_; size_t v___x_239_; 
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_233_, v___x_238_);
v_i_233_ = v___x_239_;
v_b_234_ = v_a_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___boxed(lean_object* v_env_275_, lean_object* v_val_276_, lean_object* v_as_277_, lean_object* v_sz_278_, lean_object* v_i_279_, lean_object* v_b_280_, lean_object* v___y_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_i_boxed_283_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0(v_env_275_, v_val_276_, v_as_277_, v_sz_boxed_282_, v_i_boxed_283_, v_b_280_);
lean_dec_ref(v_as_277_);
lean_dec_ref(v_val_276_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1(lean_object* v_env_309_, lean_object* v___x_310_, lean_object* v_as_311_, size_t v_sz_312_, size_t v_i_313_, lean_object* v_b_314_){
_start:
{
lean_object* v_a_317_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_313_, v_sz_312_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v___x_310_);
lean_dec_ref(v_env_309_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_b_314_);
return v___x_322_;
}
else
{
lean_object* v_snd_323_; lean_object* v_snd_324_; lean_object* v_snd_325_; lean_object* v_fst_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_472_; 
v_snd_323_ = lean_ctor_get(v_b_314_, 1);
lean_inc(v_snd_323_);
v_snd_324_ = lean_ctor_get(v_snd_323_, 1);
lean_inc(v_snd_324_);
v_snd_325_ = lean_ctor_get(v_snd_324_, 1);
lean_inc(v_snd_325_);
v_fst_326_ = lean_ctor_get(v_b_314_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_b_314_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_b_314_, 1);
lean_dec(v_unused_473_);
v___x_328_ = v_b_314_;
v_isShared_329_ = v_isSharedCheck_472_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_fst_326_);
lean_dec(v_b_314_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_472_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fst_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_470_; 
v_fst_330_ = lean_ctor_get(v_snd_323_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_snd_323_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_snd_323_, 1);
lean_dec(v_unused_471_);
v___x_332_ = v_snd_323_;
v_isShared_333_ = v_isSharedCheck_470_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_fst_330_);
lean_dec(v_snd_323_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_470_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fst_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_468_; 
v_fst_334_ = lean_ctor_get(v_snd_324_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_snd_324_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v_snd_324_, 1);
lean_dec(v_unused_469_);
v___x_336_ = v_snd_324_;
v_isShared_337_ = v_isSharedCheck_468_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_fst_334_);
lean_dec(v_snd_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_468_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_467_; 
v_fst_338_ = lean_ctor_get(v_snd_325_, 0);
v_snd_339_ = lean_ctor_get(v_snd_325_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_snd_325_);
if (v_isSharedCheck_467_ == 0)
{
v___x_341_ = v_snd_325_;
v_isShared_342_ = v_isSharedCheck_467_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_inc(v_fst_338_);
lean_dec(v_snd_325_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_467_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_checked_343_; lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_checked_343_ = lean_ctor_get(v_env_309_, 2);
v_a_344_ = lean_array_uget_borrowed(v_as_311_, v_i_313_);
lean_inc_ref(v_checked_343_);
v___x_345_ = lean_task_get_own(v_checked_343_);
v___x_346_ = l_Lean_ConstantInfo_name(v_a_344_);
lean_inc(v___x_346_);
v___x_347_ = lean_environment_find(v___x_345_, v___x_346_);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_443_; 
v_val_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_443_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_443_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_443_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_duplicateOwners_353_; lean_object* v_cachedReplicas_354_; lean_object* v___x_390_; 
v___x_390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__0___redArg(v_fst_326_, v___x_346_);
if (lean_obj_tag(v___x_390_) == 1)
{
lean_object* v_val_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_426_; 
v_val_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_426_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_426_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_val_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_426_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__0));
lean_inc(v___x_346_);
v___x_396_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_346_, v___x_321_);
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 3);
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_425_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__1));
v___x_401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_391_, v___x_321_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 3);
lean_ctor_set(v___x_350_, 0, v___x_401_);
v___x_403_ = v___x_350_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_424_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_400_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__2));
lean_inc(v___x_310_);
v___x_406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_310_, v___x_321_);
v___x_407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__3));
lean_inc(v_a_344_);
v___x_410_ = l_Lean_ConstantInfo_value_x3f(v_a_344_, v___x_321_);
lean_inc(v_val_348_);
v___x_411_ = l_Lean_ConstantInfo_value_x3f(v_val_348_, v___x_321_);
v___x_412_ = l_Option_instBEq_beq___at___00Lean_Meta_Grind_Arith_Linear_propagateIneq_spec__0(v___x_410_, v___x_411_);
lean_dec(v___x_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_413_, 0, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_409_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_408_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_404_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_399_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Lean_Json_mkObj(v___x_419_);
lean_dec_ref_known(v___x_419_, 2);
v___x_421_ = l_NNH8__RuntimeScan_sameDeclaration(v_a_344_, v_val_348_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_array_push(v_fst_334_, v___x_420_);
v_duplicateOwners_353_ = v___x_422_;
v_cachedReplicas_354_ = v_fst_338_;
goto v___jp_352_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = lean_array_push(v_fst_338_, v___x_420_);
v_duplicateOwners_353_ = v_fst_334_;
v_cachedReplicas_354_ = v___x_423_;
goto v___jp_352_;
}
}
}
}
}
else
{
uint8_t v___x_427_; 
lean_dec(v___x_390_);
v___x_427_ = l_NNH8__RuntimeScan_sameDeclaration(v_a_344_, v_val_348_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__0));
lean_inc(v___x_346_);
v___x_429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_346_, v___x_321_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 3);
lean_ctor_set(v___x_350_, 0, v___x_429_);
v___x_431_ = v___x_350_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_442_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_428_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__2));
lean_inc(v___x_310_);
v___x_434_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_310_, v___x_321_);
v___x_435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_433_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__8));
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_432_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_Json_mkObj(v___x_439_);
lean_dec_ref_known(v___x_439_, 2);
v___x_441_ = lean_array_push(v_fst_334_, v___x_440_);
v_duplicateOwners_353_ = v___x_441_;
v_cachedReplicas_354_ = v_fst_338_;
goto v___jp_352_;
}
}
else
{
lean_del_object(v___x_350_);
v_duplicateOwners_353_ = v_fst_334_;
v_cachedReplicas_354_ = v_fst_338_;
goto v___jp_352_;
}
}
v___jp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_inc(v_val_348_);
v___x_355_ = l_NNH8__RuntimeScan_referenceNames(v_val_348_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_fst_330_);
v___x_357_ = v___x_341_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_snd_339_);
v___x_357_ = v_reuseFailAlloc_389_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
size_t v_sz_358_; size_t v___x_359_; lean_object* v___x_360_; 
v_sz_358_ = lean_array_size(v___x_355_);
v___x_359_ = ((size_t)0ULL);
lean_inc_ref(v_env_309_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0(v_env_309_, v_val_348_, v___x_355_, v_sz_358_, v___x_359_, v___x_357_);
lean_dec_ref(v___x_355_);
lean_dec(v_val_348_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_380_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v_fst_362_ = lean_ctor_get(v_a_361_, 0);
v_snd_363_ = lean_ctor_get(v_a_361_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_365_ = v_a_361_;
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v_a_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
lean_inc(v___x_310_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_EmitC_0__Lean_Compiler_LCNF_Arg_toCString_spec__1___redArg(v_fst_326_, v___x_346_, v___x_310_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v_cachedReplicas_354_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_cachedReplicas_354_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_snd_363_);
v___x_369_ = v_reuseFailAlloc_379_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_369_);
lean_ctor_set(v___x_336_, 0, v_duplicateOwners_353_);
v___x_371_ = v___x_336_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_duplicateOwners_353_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_371_);
lean_ctor_set(v___x_332_, 0, v_fst_362_);
v___x_373_ = v___x_332_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_fst_362_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_373_);
lean_ctor_set(v___x_328_, 0, v___x_367_);
v___x_375_ = v___x_328_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v_a_317_ = v___x_375_;
goto v___jp_316_;
}
}
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_cachedReplicas_354_);
lean_dec_ref(v_duplicateOwners_353_);
lean_dec(v___x_346_);
lean_del_object(v___x_336_);
lean_del_object(v___x_332_);
lean_del_object(v___x_328_);
lean_dec(v_fst_326_);
lean_dec(v___x_310_);
lean_dec_ref(v_env_309_);
v_a_381_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_360_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_360_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
lean_dec(v___x_347_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__0));
v___x_445_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_346_, v___x_321_);
v___x_446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_inc_ref(v___x_446_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_446_);
lean_ctor_set(v___x_341_, 0, v___x_444_);
v___x_448_ = v___x_341_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_466_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__0___closed__1));
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_446_);
lean_ctor_set(v___x_336_, 0, v___x_449_);
v___x_451_ = v___x_336_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_446_);
v___x_451_ = v_reuseFailAlloc_465_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___closed__13));
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_448_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_Json_mkObj(v___x_454_);
lean_dec_ref_known(v___x_454_, 2);
v___x_456_ = lean_array_push(v_fst_330_, v___x_455_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_snd_339_);
lean_ctor_set(v___x_332_, 0, v_fst_338_);
v___x_458_ = v___x_332_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_fst_338_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_snd_339_);
v___x_458_ = v_reuseFailAlloc_464_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_458_);
lean_ctor_set(v___x_328_, 0, v_fst_334_);
v___x_460_ = v___x_328_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_334_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_456_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_fst_326_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v_a_317_ = v___x_462_;
goto v___jp_316_;
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
v___jp_316_:
{
size_t v___x_318_; size_t v___x_319_; 
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_313_, v___x_318_);
v_i_313_ = v___x_319_;
v_b_314_ = v_a_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1___boxed(lean_object* v_env_474_, lean_object* v___x_475_, lean_object* v_as_476_, lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_482_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1(v_env_474_, v___x_475_, v_as_476_, v_sz_boxed_481_, v_i_boxed_482_, v_b_479_);
lean_dec_ref(v_as_476_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2(size_t v_sz_484_, size_t v_i_485_, lean_object* v_bs_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_487_ == 0)
{
return v_bs_486_;
}
else
{
lean_object* v_v_488_; lean_object* v_module_489_; lean_object* v___x_490_; lean_object* v_bs_x27_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_v_488_ = lean_array_uget_borrowed(v_bs_486_, v_i_485_);
v_module_489_ = lean_ctor_get(v_v_488_, 0);
lean_inc(v_module_489_);
v___x_490_ = lean_unsigned_to_nat(0u);
v_bs_x27_491_ = lean_array_uset(v_bs_486_, v_i_485_, v___x_490_);
v___x_492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_489_, v___x_487_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_485_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_491_, v_i_485_, v___x_492_);
v_i_485_ = v___x_494_;
v_bs_486_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2___boxed(lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_bs_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2(v_sz_boxed_500_, v_i_boxed_501_, v_bs_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg(lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v_env_525_, lean_object* v_a_526_, lean_object* v_expected_527_, lean_object* v_range_528_, lean_object* v_b_529_, lean_object* v_i_530_){
_start:
{
lean_object* v_stop_532_; lean_object* v_step_533_; uint8_t v___x_534_; 
v_stop_532_ = lean_ctor_get(v_range_528_, 1);
v_step_533_ = lean_ctor_get(v_range_528_, 2);
v___x_534_ = lean_nat_dec_lt(v_i_530_, v_stop_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v_i_530_);
lean_dec_ref(v_env_525_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v_b_529_);
return v___x_535_;
}
else
{
lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_675_; 
v_fst_536_ = lean_ctor_get(v_b_529_, 0);
v_snd_537_ = lean_ctor_get(v_b_529_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_b_529_);
if (v_isSharedCheck_675_ == 0)
{
v___x_539_ = v_b_529_;
v_isShared_540_ = v_isSharedCheck_675_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_inc(v_fst_536_);
lean_dec(v_b_529_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_675_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_moduleData_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_imports_544_; lean_object* v_constants_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_moduleData_541_ = lean_ctor_get(v___x_524_, 6);
v___x_542_ = l_Lean_instInhabitedModuleData_default;
v___x_543_ = lean_array_get_borrowed(v___x_542_, v_moduleData_541_, v_i_530_);
v_imports_544_ = lean_ctor_get(v___x_543_, 0);
v_constants_545_ = lean_ctor_get(v___x_543_, 2);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_array_fget_borrowed(v___x_523_, v_i_530_);
v___x_548_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__3));
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_548_);
lean_ctor_set(v___x_539_, 0, v_snd_537_);
v___x_550_ = v___x_539_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_snd_537_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_674_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
size_t v_sz_551_; size_t v___x_552_; lean_object* v___x_553_; 
v_sz_551_ = lean_array_size(v_constants_545_);
v___x_552_ = ((size_t)0ULL);
lean_inc(v___x_547_);
lean_inc_ref(v_env_525_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1(v_env_525_, v___x_547_, v_constants_545_, v_sz_551_, v___x_552_, v___x_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v_snd_555_; lean_object* v_snd_556_; lean_object* v_snd_557_; lean_object* v_fst_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_664_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v_snd_555_ = lean_ctor_get(v_a_554_, 1);
lean_inc(v_snd_555_);
v_snd_556_ = lean_ctor_get(v_snd_555_, 1);
lean_inc(v_snd_556_);
v_snd_557_ = lean_ctor_get(v_snd_556_, 1);
lean_inc(v_snd_557_);
v_fst_558_ = lean_ctor_get(v_a_554_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_a_554_, 1);
lean_dec(v_unused_665_);
v___x_560_ = v_a_554_;
v_isShared_561_ = v_isSharedCheck_664_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_fst_558_);
lean_dec(v_a_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_664_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_fst_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_662_; 
v_fst_562_ = lean_ctor_get(v_snd_555_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_snd_555_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_snd_555_, 1);
lean_dec(v_unused_663_);
v___x_564_ = v_snd_555_;
v_isShared_565_ = v_isSharedCheck_662_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_fst_562_);
lean_dec(v_snd_555_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_662_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_fst_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_660_; 
v_fst_566_ = lean_ctor_get(v_snd_556_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_snd_556_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_snd_556_, 1);
lean_dec(v_unused_661_);
v___x_568_ = v_snd_556_;
v_isShared_569_ = v_isSharedCheck_660_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_fst_566_);
lean_dec(v_snd_556_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_660_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_659_; 
v_fst_570_ = lean_ctor_get(v_snd_557_, 0);
v_snd_571_ = lean_ctor_get(v_snd_557_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_snd_557_);
if (v_isSharedCheck_659_ == 0)
{
v___x_573_ = v_snd_557_;
v_isShared_574_ = v_isSharedCheck_659_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_snd_557_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_659_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
uint8_t v_failed_575_; size_t v_sz_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___y_581_; uint8_t v_failed_582_; uint8_t v___y_647_; lean_object* v___x_653_; 
v_failed_575_ = 0;
v_sz_576_ = lean_array_size(v_imports_544_);
lean_inc_ref(v_imports_544_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2(v_sz_576_, v___x_552_, v_imports_544_);
v___x_578_ = l_NNH8__RuntimeScan_canonicalImports(v___x_577_);
lean_inc(v___x_547_);
v___x_579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_547_, v___x_534_);
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_expected_527_, v___x_579_);
if (lean_obj_tag(v___x_653_) == 0)
{
v___y_647_ = v_failed_575_;
goto v___jp_646_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_array_get_size(v___x_578_);
v___x_656_ = lean_array_get_size(v_val_654_);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v_val_654_);
v___y_647_ = v_failed_575_;
goto v___jp_646_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(v___x_578_, v_val_654_, v___x_655_);
lean_dec(v_val_654_);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
}
v___jp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_584_);
lean_ctor_set(v___x_573_, 0, v___x_583_);
v___x_586_ = v___x_573_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_645_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_588_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_578_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v___x_588_);
lean_ctor_set(v___x_568_, 0, v___x_587_);
v___x_590_ = v___x_568_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_644_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__6));
v___x_592_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_577_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_592_);
lean_ctor_set(v___x_564_, 0, v___x_591_);
v___x_594_ = v___x_564_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_592_);
v___x_594_ = v_reuseFailAlloc_643_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__7));
v___x_596_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_596_, 0, v___y_581_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_596_);
lean_ctor_set(v___x_560_, 0, v___x_595_);
v___x_598_ = v___x_560_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_642_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_599_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__8));
v___x_600_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_562_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__9));
v___x_603_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_566_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__10));
v___x_606_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_570_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__11));
v___x_609_ = lean_array_get_size(v_constants_545_);
v___x_610_ = l_Lean_JsonNumber_fromNat(v___x_609_);
v___x_611_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_608_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__12));
v___x_614_ = l_Lean_JsonNumber_fromNat(v_snd_571_);
v___x_615_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_613_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_box(0);
v___x_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_612_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_607_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_604_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_601_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_598_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_594_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_590_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_586_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_Json_mkObj(v___x_626_);
lean_dec_ref_known(v___x_626_, 2);
v___x_628_ = l_Lean_Json_compress(v___x_627_);
v___x_629_ = l_IO_FS_Handle_putStrLn(v_a_526_, v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref_known(v___x_629_, 1);
v___x_630_ = lean_box(v_failed_582_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_fst_558_);
v___x_632_ = lean_nat_add(v_i_530_, v_step_533_);
lean_dec(v_i_530_);
v_b_529_ = v___x_631_;
v_i_530_ = v___x_632_;
goto _start;
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_fst_558_);
lean_dec(v_i_530_);
lean_dec_ref(v_env_525_);
v_a_634_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_629_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_629_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
}
}
v___jp_646_:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_array_get_size(v_fst_562_);
v___x_649_ = lean_nat_dec_eq(v___x_648_, v___x_546_);
if (v___x_649_ == 0)
{
lean_dec(v_fst_536_);
v___y_581_ = v___y_647_;
v_failed_582_ = v___x_534_;
goto v___jp_580_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_array_get_size(v_fst_566_);
v___x_651_ = lean_nat_dec_eq(v___x_650_, v___x_546_);
if (v___x_651_ == 0)
{
lean_dec(v_fst_536_);
v___y_581_ = v___y_647_;
v_failed_582_ = v___x_534_;
goto v___jp_580_;
}
else
{
if (v___y_647_ == 0)
{
lean_dec(v_fst_536_);
v___y_581_ = v___y_647_;
v_failed_582_ = v___x_534_;
goto v___jp_580_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_unbox(v_fst_536_);
lean_dec(v_fst_536_);
v___y_581_ = v___y_647_;
v_failed_582_ = v___x_652_;
goto v___jp_580_;
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
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_fst_536_);
lean_dec(v_i_530_);
lean_dec_ref(v_env_525_);
v_a_666_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_553_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_553_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___boxed(lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v_env_678_, lean_object* v_a_679_, lean_object* v_expected_680_, lean_object* v_range_681_, lean_object* v_b_682_, lean_object* v_i_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg(v___x_676_, v___x_677_, v_env_678_, v_a_679_, v_expected_680_, v_range_681_, v_b_682_, v_i_683_);
lean_dec_ref(v_range_681_);
lean_dec_ref(v_expected_680_);
lean_dec(v_a_679_);
lean_dec_ref(v___x_677_);
lean_dec_ref(v___x_676_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg(lean_object* v___x_686_, lean_object* v_env_687_, lean_object* v___x_688_, lean_object* v_a_689_, lean_object* v_expected_690_, lean_object* v_range_691_, lean_object* v_b_692_, lean_object* v_i_693_){
_start:
{
lean_object* v_stop_695_; lean_object* v_step_696_; uint8_t v___x_697_; 
v_stop_695_ = lean_ctor_get(v_range_691_, 1);
v_step_696_ = lean_ctor_get(v_range_691_, 2);
v___x_697_ = lean_nat_dec_lt(v_i_693_, v_stop_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec_ref(v_env_687_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v_b_692_);
return v___x_698_;
}
else
{
lean_object* v_fst_699_; lean_object* v_snd_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_838_; 
v_fst_699_ = lean_ctor_get(v_b_692_, 0);
v_snd_700_ = lean_ctor_get(v_b_692_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_692_);
if (v_isSharedCheck_838_ == 0)
{
v___x_702_ = v_b_692_;
v_isShared_703_ = v_isSharedCheck_838_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_snd_700_);
lean_inc(v_fst_699_);
lean_dec(v_b_692_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_838_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_moduleData_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_imports_707_; lean_object* v_constants_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v_moduleData_704_ = lean_ctor_get(v___x_688_, 6);
v___x_705_ = l_Lean_instInhabitedModuleData_default;
v___x_706_ = lean_array_get_borrowed(v___x_705_, v_moduleData_704_, v_i_693_);
v_imports_707_ = lean_ctor_get(v___x_706_, 0);
v_constants_708_ = lean_ctor_get(v___x_706_, 2);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_array_fget_borrowed(v___x_686_, v_i_693_);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__3));
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_711_);
lean_ctor_set(v___x_702_, 0, v_snd_700_);
v___x_713_ = v___x_702_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_snd_700_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_837_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
size_t v_sz_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_sz_714_ = lean_array_size(v_constants_708_);
v___x_715_ = ((size_t)0ULL);
lean_inc(v___x_710_);
lean_inc_ref(v_env_687_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NNH8__RuntimeScan_loadedScan_spec__1(v_env_687_, v___x_710_, v_constants_708_, v_sz_714_, v___x_715_, v___x_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_snd_718_; lean_object* v_snd_719_; lean_object* v_snd_720_; lean_object* v_fst_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_827_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v_snd_718_ = lean_ctor_get(v_a_717_, 1);
lean_inc(v_snd_718_);
v_snd_719_ = lean_ctor_get(v_snd_718_, 1);
lean_inc(v_snd_719_);
v_snd_720_ = lean_ctor_get(v_snd_719_, 1);
lean_inc(v_snd_720_);
v_fst_721_ = lean_ctor_get(v_a_717_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_a_717_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_a_717_, 1);
lean_dec(v_unused_828_);
v___x_723_ = v_a_717_;
v_isShared_724_ = v_isSharedCheck_827_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_fst_721_);
lean_dec(v_a_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_827_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_fst_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_825_; 
v_fst_725_ = lean_ctor_get(v_snd_718_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_snd_718_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v_snd_718_, 1);
lean_dec(v_unused_826_);
v___x_727_ = v_snd_718_;
v_isShared_728_ = v_isSharedCheck_825_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_fst_725_);
lean_dec(v_snd_718_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_825_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_fst_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_823_; 
v_fst_729_ = lean_ctor_get(v_snd_719_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_snd_719_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_snd_719_, 1);
lean_dec(v_unused_824_);
v___x_731_ = v_snd_719_;
v_isShared_732_ = v_isSharedCheck_823_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_fst_729_);
lean_dec(v_snd_719_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_823_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_822_; 
v_fst_733_ = lean_ctor_get(v_snd_720_, 0);
v_snd_734_ = lean_ctor_get(v_snd_720_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_snd_720_);
if (v_isSharedCheck_822_ == 0)
{
v___x_736_ = v_snd_720_;
v_isShared_737_ = v_isSharedCheck_822_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v_snd_720_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_822_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v_failed_738_; size_t v_sz_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___y_744_; uint8_t v_failed_745_; uint8_t v___y_810_; lean_object* v___x_816_; 
v_failed_738_ = 0;
v_sz_739_ = lean_array_size(v_imports_707_);
lean_inc_ref(v_imports_707_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NNH8__RuntimeScan_loadedScan_spec__2(v_sz_739_, v___x_715_, v_imports_707_);
v___x_741_ = l_NNH8__RuntimeScan_canonicalImports(v___x_740_);
lean_inc(v___x_710_);
v___x_742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_710_, v___x_697_);
v___x_816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_expected_690_, v___x_742_);
if (lean_obj_tag(v___x_816_) == 0)
{
v___y_810_ = v_failed_738_;
goto v___jp_809_;
}
else
{
lean_object* v_val_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_val_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = lean_array_get_size(v___x_741_);
v___x_819_ = lean_array_get_size(v_val_817_);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_dec(v_val_817_);
v___y_810_ = v_failed_738_;
goto v___jp_809_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = l_Array_isEqvAux___at___00NNH8__RuntimeScan_importsMatch_spec__0___redArg(v___x_741_, v_val_817_, v___x_818_);
lean_dec(v_val_817_);
v___y_810_ = v___x_821_;
goto v___jp_809_;
}
}
v___jp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_742_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_747_);
lean_ctor_set(v___x_736_, 0, v___x_746_);
v___x_749_ = v___x_736_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_808_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_751_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_741_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_751_);
lean_ctor_set(v___x_731_, 0, v___x_750_);
v___x_753_ = v___x_731_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_751_);
v___x_753_ = v_reuseFailAlloc_807_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__6));
v___x_755_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___x_740_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_755_);
lean_ctor_set(v___x_727_, 0, v___x_754_);
v___x_757_ = v___x_727_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_806_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__7));
v___x_759_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_759_, 0, v___y_744_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_759_);
lean_ctor_set(v___x_723_, 0, v___x_758_);
v___x_761_ = v___x_723_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_805_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_762_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__8));
v___x_763_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_725_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__9));
v___x_766_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_729_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__10));
v___x_769_ = l_Array_toJson___at___00Lean_Server_FileWorker_handlePreRequestSpecialCases_x3f_spec__6(v_fst_733_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__11));
v___x_772_ = lean_array_get_size(v_constants_708_);
v___x_773_ = l_Lean_JsonNumber_fromNat(v___x_772_);
v___x_774_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_771_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__12));
v___x_777_ = l_Lean_JsonNumber_fromNat(v_snd_734_);
v___x_778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_776_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_775_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_770_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_767_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_764_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_761_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_757_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_753_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_749_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_Json_mkObj(v___x_789_);
lean_dec_ref_known(v___x_789_, 2);
v___x_791_ = l_Lean_Json_compress(v___x_790_);
v___x_792_ = l_IO_FS_Handle_putStrLn(v_a_689_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = lean_box(v_failed_745_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v_fst_721_);
v___x_795_ = lean_nat_add(v_i_693_, v_step_696_);
v___x_796_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg(v___x_686_, v___x_688_, v_env_687_, v_a_689_, v_expected_690_, v_range_691_, v___x_794_, v___x_795_);
return v___x_796_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_fst_721_);
lean_dec_ref(v_env_687_);
v_a_797_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_792_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
}
v___jp_809_:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_fst_725_);
v___x_812_ = lean_nat_dec_eq(v___x_811_, v___x_709_);
if (v___x_812_ == 0)
{
lean_dec(v_fst_699_);
v___y_744_ = v___y_810_;
v_failed_745_ = v___x_697_;
goto v___jp_743_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_array_get_size(v_fst_729_);
v___x_814_ = lean_nat_dec_eq(v___x_813_, v___x_709_);
if (v___x_814_ == 0)
{
lean_dec(v_fst_699_);
v___y_744_ = v___y_810_;
v_failed_745_ = v___x_697_;
goto v___jp_743_;
}
else
{
if (v___y_810_ == 0)
{
lean_dec(v_fst_699_);
v___y_744_ = v___y_810_;
v_failed_745_ = v___x_697_;
goto v___jp_743_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = lean_unbox(v_fst_699_);
lean_dec(v_fst_699_);
v___y_744_ = v___y_810_;
v_failed_745_ = v___x_815_;
goto v___jp_743_;
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
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_fst_699_);
lean_dec_ref(v_env_687_);
v_a_829_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_716_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_716_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg___boxed(lean_object* v___x_839_, lean_object* v_env_840_, lean_object* v___x_841_, lean_object* v_a_842_, lean_object* v_expected_843_, lean_object* v_range_844_, lean_object* v_b_845_, lean_object* v_i_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg(v___x_839_, v_env_840_, v___x_841_, v_a_842_, v_expected_843_, v_range_844_, v_b_845_, v_i_846_);
lean_dec(v_i_846_);
lean_dec_ref(v_range_844_);
lean_dec_ref(v_expected_843_);
lean_dec(v_a_842_);
lean_dec_ref(v___x_841_);
lean_dec_ref(v___x_839_);
return v_res_848_;
}
}
static lean_object* _init_l_NNH8__RuntimeScan_loadedScan___closed__0(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_unsigned_to_nat(16u);
v___x_851_ = lean_mk_array(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_NNH8__RuntimeScan_loadedScan___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_NNH8__RuntimeScan_loadedScan___closed__0, &l_NNH8__RuntimeScan_loadedScan___closed__0_once, _init_l_NNH8__RuntimeScan_loadedScan___closed__0);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_NNH8__RuntimeScan_loadedScan___closed__2(void){
_start:
{
lean_object* v___x_855_; uint8_t v_failed_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_obj_once(&l_NNH8__RuntimeScan_loadedScan___closed__1, &l_NNH8__RuntimeScan_loadedScan___closed__1_once, _init_l_NNH8__RuntimeScan_loadedScan___closed__1);
v_failed_856_ = 0;
v___x_857_ = lean_box(v_failed_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_855_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_loadedScan(lean_object* v_env_859_, lean_object* v_output_860_, lean_object* v_expected_861_){
_start:
{
uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_863_ = 1;
v___x_864_ = lean_io_prim_handle_mk(v_output_860_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; uint8_t v_failed_866_; lean_object* v_env_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_failed_866_ = 0;
v_env_867_ = l_Lean_Environment_setExporting(v_env_859_, v_failed_866_);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = l_Lean_Environment_header(v_env_867_);
lean_inc_ref(v___x_869_);
v___x_870_ = l_Lean_EnvironmentHeader_moduleNames(v___x_869_);
v___x_871_ = lean_array_get_size(v___x_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_873_, 0, v___x_868_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
v___x_874_ = lean_obj_once(&l_NNH8__RuntimeScan_loadedScan___closed__2, &l_NNH8__RuntimeScan_loadedScan___closed__2_once, _init_l_NNH8__RuntimeScan_loadedScan___closed__2);
v___x_875_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg(v___x_870_, v_env_867_, v___x_869_, v_a_865_, v_expected_861_, v___x_873_, v___x_874_, v___x_868_);
lean_dec_ref_known(v___x_873_, 3);
lean_dec(v_a_865_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_884_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_fst_880_; lean_object* v___x_882_; 
v_fst_880_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_fst_880_);
lean_dec(v_a_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_fst_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_875_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_875_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_env_859_);
v_a_893_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_864_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_864_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NNH8__RuntimeScan_loadedScan___boxed(lean_object* v_env_901_, lean_object* v_output_902_, lean_object* v_expected_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_NNH8__RuntimeScan_loadedScan(v_env_901_, v_output_902_, v_expected_903_);
lean_dec_ref(v_expected_903_);
lean_dec_ref(v_output_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3(lean_object* v___x_906_, lean_object* v_env_907_, lean_object* v___x_908_, lean_object* v_a_909_, lean_object* v_expected_910_, lean_object* v_range_911_, lean_object* v_b_912_, lean_object* v_i_913_, lean_object* v_hs_914_, lean_object* v_hl_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___redArg(v___x_906_, v_env_907_, v___x_908_, v_a_909_, v_expected_910_, v_range_911_, v_b_912_, v_i_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3___boxed(lean_object* v___x_918_, lean_object* v_env_919_, lean_object* v___x_920_, lean_object* v_a_921_, lean_object* v_expected_922_, lean_object* v_range_923_, lean_object* v_b_924_, lean_object* v_i_925_, lean_object* v_hs_926_, lean_object* v_hl_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3(v___x_918_, v_env_919_, v___x_920_, v_a_921_, v_expected_922_, v_range_923_, v_b_924_, v_i_925_, v_hs_926_, v_hl_927_);
lean_dec(v_i_925_);
lean_dec_ref(v_range_923_);
lean_dec_ref(v_expected_922_);
lean_dec(v_a_921_);
lean_dec_ref(v___x_920_);
lean_dec_ref(v___x_918_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3(lean_object* v___x_930_, lean_object* v___x_931_, lean_object* v_env_932_, lean_object* v_a_933_, lean_object* v_expected_934_, lean_object* v_range_935_, lean_object* v_b_936_, lean_object* v_i_937_, lean_object* v_hs_938_, lean_object* v_hl_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg(v___x_930_, v___x_931_, v_env_932_, v_a_933_, v_expected_934_, v_range_935_, v_b_936_, v_i_937_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___boxed(lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v_env_944_, lean_object* v_a_945_, lean_object* v_expected_946_, lean_object* v_range_947_, lean_object* v_b_948_, lean_object* v_i_949_, lean_object* v_hs_950_, lean_object* v_hl_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3(v___x_942_, v___x_943_, v_env_944_, v_a_945_, v_expected_946_, v_range_947_, v_b_948_, v_i_949_, v_hs_950_, v_hl_951_);
lean_dec_ref(v_range_947_);
lean_dec_ref(v_expected_946_);
lean_dec(v_a_945_);
lean_dec_ref(v___x_943_);
lean_dec_ref(v___x_942_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(size_t v_sz_954_, size_t v_i_955_, lean_object* v_bs_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_957_ == 0)
{
return v_bs_956_;
}
else
{
lean_object* v_v_958_; lean_object* v___x_959_; lean_object* v_bs_x27_960_; uint8_t v___x_961_; lean_object* v___x_962_; size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v_v_958_ = lean_array_uget(v_bs_956_, v_i_955_);
v___x_959_ = lean_unsigned_to_nat(0u);
v_bs_x27_960_ = lean_array_uset(v_bs_956_, v_i_955_, v___x_959_);
v___x_961_ = 0;
v___x_962_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_962_, 0, v_v_958_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_957_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1 + 1, v___x_957_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1 + 2, v___x_961_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_955_, v___x_963_);
v___x_965_ = lean_array_uset(v_bs_x27_960_, v_i_955_, v___x_962_);
v_i_955_ = v___x_964_;
v_bs_956_ = v___x_965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0___boxed(lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_bs_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_boxed_970_, v_i_boxed_971_, v_bs_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(lean_object* v_as_973_, size_t v_sz_974_, size_t v_i_975_, lean_object* v_b_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_b_976_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_a_980_ = lean_array_uget_borrowed(v_as_973_, v_i_975_);
lean_inc(v_a_980_);
v___x_981_ = l_Lean_Json_parse(v_a_980_);
v___x_982_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__4));
v___x_985_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonSubexprInfo_fromJson_spec__1(v_a_983_, v___x_984_);
v___x_986_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00NNH8__RuntimeScan_loadedScan_spec__3_spec__3___redArg___closed__5));
v___x_989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_Test_Runner_Client_instFromJsonHyp_fromJson_spec__1(v_a_983_, v___x_988_);
v___x_990_ = l_IO_ofExcept___at___00__private_Lean_Elab_Idbg_0__Lean_Idbg_idbgClientLoopImpl_spec__2___redArg(v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; size_t v___x_993_; size_t v___x_994_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_b_976_, v_a_987_, v_a_991_);
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_add(v_i_975_, v___x_993_);
v_i_975_ = v___x_994_;
v_b_976_ = v___x_992_;
goto _start;
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_987_);
lean_dec_ref(v_b_976_);
v_a_996_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_990_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_990_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_983_);
lean_dec_ref(v_b_976_);
v_a_1004_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_986_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_986_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_b_976_);
v_a_1012_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_982_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_982_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(lean_object* v_as_1020_, lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_){
_start:
{
size_t v_sz_boxed_1025_; size_t v_i_boxed_1026_; lean_object* v_res_1027_; 
v_sz_boxed_1025_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1026_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_as_1020_, v_sz_boxed_1025_, v_i_boxed_1026_, v_b_1023_);
lean_dec_ref(v_as_1020_);
return v_res_1027_;
}
}
static lean_object* _init_l_main___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_unsigned_to_nat(16u);
v___x_1031_ = lean_mk_array(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = 1;
v___x_1049_ = lean_box_uint32(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = 2;
v___x_1051_ = lean_box_uint32(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1052_){
_start:
{
uint32_t v___y_1055_; uint8_t v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1081_; size_t v___y_1082_; uint32_t v___y_1083_; lean_object* v___y_1084_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_main___closed__5));
v___x_1128_ = l_Lean_findSysroot(v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Lean_initSearchPath(v_a_1129_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_1132_) == 0)
{
uint8_t v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1170_; 
lean_dec_ref_known(v___x_1132_, 1);
if (lean_obj_tag(v_args_1052_) == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = ((lean_object*)(l_main___closed__12));
v___y_1170_ = v___x_1176_;
goto v___jp_1169_;
}
else
{
lean_object* v_head_1177_; 
v_head_1177_ = lean_ctor_get(v_args_1052_, 0);
lean_inc(v_head_1177_);
v___y_1170_ = v_head_1177_;
goto v___jp_1169_;
}
v___jp_1133_:
{
size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint32_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_sz_1138_ = lean_array_size(v___y_1137_);
v___x_1139_ = ((size_t)0ULL);
lean_inc_ref(v___y_1137_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__0(v_sz_1138_, v___x_1139_, v___y_1137_);
v___x_1141_ = l_Lean_Options_empty;
v___x_1142_ = 0;
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = ((lean_object*)(l_main___closed__6));
v___x_1145_ = 0;
v___x_1146_ = 2;
v___x_1147_ = lean_box(1);
v___x_1148_ = l_Lean_importModules(v___x_1140_, v___x_1141_, v___x_1142_, v___x_1144_, v___x_1145_, v___y_1136_, v___x_1146_, v___x_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
if (v___y_1134_ == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_main___closed__7));
v___x_1154_ = lean_string_dec_eq(v___y_1135_, v___x_1153_);
lean_dec_ref(v___y_1135_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec(v_a_1149_);
lean_dec(v_args_1052_);
v___x_1155_ = l_main___boxed__const__2;
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
lean_del_object(v___x_1151_);
v___y_1081_ = v_a_1149_;
v___y_1082_ = v___x_1139_;
v___y_1083_ = v___x_1142_;
v___y_1084_ = v___x_1143_;
goto v___jp_1080_;
}
}
}
else
{
lean_object* v_a_1160_; 
lean_dec_ref(v___y_1135_);
v_a_1160_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1148_, 1);
v___y_1081_ = v_a_1160_;
v___y_1082_ = v___x_1139_;
v___y_1083_ = v___x_1142_;
v___y_1084_ = v___x_1143_;
goto v___jp_1080_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___y_1135_);
lean_dec(v_args_1052_);
v_a_1161_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1148_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
v___jp_1169_:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = ((lean_object*)(l_main___closed__8));
v___x_1172_ = lean_string_dec_eq(v___y_1170_, v___x_1171_);
v___x_1173_ = 1;
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_NNH8__RuntimeScan_referenceNames___closed__0));
v___y_1134_ = v___x_1172_;
v___y_1135_ = v___y_1170_;
v___y_1136_ = v___x_1173_;
v___y_1137_ = v___x_1174_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l_main___closed__11));
v___y_1134_ = v___x_1172_;
v___y_1135_ = v___y_1170_;
v___y_1136_ = v___x_1173_;
v___y_1137_ = v___x_1175_;
goto v___jp_1133_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_args_1052_);
v_a_1178_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1132_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1132_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_args_1052_);
v_a_1186_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1131_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1131_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_args_1052_);
v_a_1194_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1128_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1128_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
v___jp_1054_:
{
lean_object* v___x_1058_; 
lean_inc_ref(v___y_1057_);
v___x_1058_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___y_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1070_; 
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v___x_1058_, 0);
lean_dec(v_unused_1071_);
v___x_1060_ = v___x_1058_;
v_isShared_1061_ = v_isSharedCheck_1070_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v___x_1058_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1070_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
if (v___y_1056_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box_uint32(v___y_1055_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = l_main___boxed__const__1;
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1066_);
v___x_1068_ = v___x_1060_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1058_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1058_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
v___jp_1080_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_main___closed__0));
v___x_1086_ = l_IO_FS_lines(v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v_sz_1090_; lean_object* v___x_1091_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = lean_obj_once(&l_main___closed__1, &l_main___closed__1_once, _init_l_main___closed__1);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1084_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v_sz_1090_ = lean_array_size(v_a_1087_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_a_1087_, v_sz_1090_, v___y_1082_, v___x_1089_);
lean_dec(v_a_1087_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = ((lean_object*)(l_main___closed__2));
v___x_1095_ = l_List_getD___redArg(v_args_1052_, v___x_1093_, v___x_1094_);
lean_dec(v_args_1052_);
v___x_1096_ = l_NNH8__RuntimeScan_loadedScan(v___y_1081_, v___x_1095_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec(v___x_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; uint8_t v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_unbox(v_a_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_main___closed__3));
v___x_1100_ = lean_unbox(v_a_1097_);
lean_dec(v_a_1097_);
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___x_1100_;
v___y_1057_ = v___x_1099_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_main___closed__4));
v___x_1102_ = lean_unbox(v_a_1097_);
lean_dec(v_a_1097_);
v___y_1055_ = v___y_1083_;
v___y_1056_ = v___x_1102_;
v___y_1057_ = v___x_1101_;
goto v___jp_1054_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1096_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1096_);
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
lean_dec_ref(v___y_1081_);
lean_dec(v_args_1052_);
v_a_1111_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1091_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1091_);
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
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1081_);
lean_dec(v_args_1052_);
v_a_1119_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1086_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1086_);
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
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = _lean_main(v_args_1202_);
return v_res_1204_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NNH8__RuntimeScan(uint8_t builtin) {
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
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
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
  res = initialize_NNH8__RuntimeScan(1 /* builtin */);
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
