// Lean compiler output
// Module: NFJ_WALKER
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
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_lean_runCommand_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isAxiom(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_validateCat_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_addAutoBoundImplicitsInlayHint_spec__3(size_t, size_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "NEP_FAILURE "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__4_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "discovered_constants_before_failure"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "edges_scanned_before_failure"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "complete"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__8_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "missing reachable constant "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "; parent "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__11 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "; visited "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__13 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NEP_audit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_NEP_audit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "raw graph disagrees with collectAxioms"};
static const lean_object* l_NEP_audit___closed__0 = (const lean_object*)&l_NEP_audit___closed__0_value;
static lean_once_cell_t l_NEP_audit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NEP_audit___closed__1;
static const lean_array_object l_NEP_audit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NEP_audit___closed__2 = (const lean_object*)&l_NEP_audit___closed__2_value;
static const lean_ctor_object l_NEP_audit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_NEP_audit___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_NEP_audit___closed__3 = (const lean_object*)&l_NEP_audit___closed__3_value;
static const lean_string_object l_NEP_audit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "NEP_RESULT "};
static const lean_object* l_NEP_audit___closed__4 = (const lean_object*)&l_NEP_audit___closed__4_value;
static lean_once_cell_t l_NEP_audit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NEP_audit___closed__5;
static const lean_string_object l_NEP_audit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "reachable_constants"};
static const lean_object* l_NEP_audit___closed__6 = (const lean_object*)&l_NEP_audit___closed__6_value;
static const lean_string_object l_NEP_audit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "edges_scanned"};
static const lean_object* l_NEP_audit___closed__7 = (const lean_object*)&l_NEP_audit___closed__7_value;
static const lean_string_object l_NEP_audit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "walked_axioms"};
static const lean_object* l_NEP_audit___closed__8 = (const lean_object*)&l_NEP_audit___closed__8_value;
static const lean_string_object l_NEP_audit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "collect_axioms"};
static const lean_object* l_NEP_audit___closed__9 = (const lean_object*)&l_NEP_audit___closed__9_value;
static const lean_string_object l_NEP_audit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "equal"};
static const lean_object* l_NEP_audit___closed__10 = (const lean_object*)&l_NEP_audit___closed__10_value;
static const lean_string_object l_NEP_audit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_REACHABLE.txt"};
static const lean_object* l_NEP_audit___closed__11 = (const lean_object*)&l_NEP_audit___closed__11_value;
static const lean_string_object l_NEP_audit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_NEP_audit___closed__12 = (const lean_object*)&l_NEP_audit___closed__12_value;
LEAN_EXPORT lean_object* l_NEP_audit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NEP_audit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NEP_audit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg(lean_object* v_fst_1_, lean_object* v_as_2_, size_t v_sz_3_, size_t v_i_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_a_8_; uint8_t v___x_12_; 
v___x_12_ = lean_usize_dec_lt(v_i_4_, v_sz_3_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v_fst_1_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_5_);
return v___x_13_;
}
else
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_30_; 
v_fst_14_ = lean_ctor_get(v_b_5_, 0);
v_snd_15_ = lean_ctor_get(v_b_5_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_b_5_);
if (v_isSharedCheck_30_ == 0)
{
v___x_17_ = v_b_5_;
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_snd_15_);
lean_inc(v_fst_14_);
lean_dec(v_b_5_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_30_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_a_19_; uint8_t v___x_20_; 
v_a_19_ = lean_array_uget_borrowed(v_as_2_, v_i_4_);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_19_, v_snd_15_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_23_; 
lean_inc_n(v_a_19_, 2);
v___x_21_ = l_Lean_NameSet_insert(v_snd_15_, v_a_19_);
lean_inc(v_fst_1_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v_fst_1_);
lean_ctor_set(v___x_17_, 0, v_a_19_);
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_19_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_fst_1_);
v___x_23_ = v_reuseFailAlloc_26_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_array_push(v_fst_14_, v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_21_);
v_a_8_ = v___x_25_;
goto v___jp_7_;
}
}
else
{
lean_object* v___x_28_; 
if (v_isShared_18_ == 0)
{
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_fst_14_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_snd_15_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
v_a_8_ = v___x_28_;
goto v___jp_7_;
}
}
}
}
v___jp_7_:
{
size_t v___x_9_; size_t v___x_10_; 
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_4_, v___x_9_);
v_i_4_ = v___x_10_;
v_b_5_ = v_a_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg___boxed(lean_object* v_fst_31_, lean_object* v_as_32_, lean_object* v_sz_33_, lean_object* v_i_34_, lean_object* v_b_35_, lean_object* v___y_36_){
_start:
{
size_t v_sz_boxed_37_; size_t v_i_boxed_38_; lean_object* v_res_39_; 
v_sz_boxed_37_ = lean_unbox_usize(v_sz_33_);
lean_dec(v_sz_33_);
v_i_boxed_38_ = lean_unbox_usize(v_i_34_);
lean_dec(v_i_34_);
v_res_39_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg(v_fst_31_, v_as_32_, v_sz_boxed_37_, v_i_boxed_38_, v_b_35_);
lean_dec_ref(v_as_32_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0(lean_object* v___x_40_, lean_object* v_fst_41_, lean_object* v_fst_42_, lean_object* v_snd_43_, lean_object* v_val_44_, uint8_t v___x_45_, lean_object* v___x_46_, lean_object* v_____r_47_, lean_object* v_axioms_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_refs_53_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___y_91_; lean_object* v___x_97_; 
v___x_88_ = l_Lean_ConstantInfo_type(v_val_44_);
v___x_89_ = l_Lean_Expr_getUsedConstants(v___x_88_);
lean_inc_ref(v_val_44_);
v___x_97_ = l_Lean_ConstantInfo_value_x3f(v_val_44_, v___x_45_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_mk_empty_array_with_capacity(v___x_46_);
v___y_91_ = v___x_98_;
goto v___jp_90_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_100_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
v___x_100_ = l_Lean_Expr_getUsedConstants(v_val_99_);
v___y_91_ = v___x_100_;
goto v___jp_90_;
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; size_t v_sz_56_; size_t v___x_57_; lean_object* v___x_58_; 
v___x_54_ = lean_array_get_size(v_refs_53_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_40_);
lean_ctor_set(v___x_55_, 1, v_fst_41_);
v_sz_56_ = lean_array_size(v_refs_53_);
v___x_57_ = ((size_t)0ULL);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg(v_fst_42_, v_refs_53_, v_sz_56_, v___x_57_, v___x_55_);
lean_dec_ref(v_refs_53_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_79_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_79_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_79_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_79_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_78_; 
v_fst_63_ = lean_ctor_get(v_a_59_, 0);
v_snd_64_ = lean_ctor_get(v_a_59_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_78_ == 0)
{
v___x_66_ = v_a_59_;
v_isShared_67_ = v_isSharedCheck_78_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_snd_64_);
lean_inc(v_fst_63_);
lean_dec(v_a_59_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_78_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_nat_add(v_snd_43_, v___x_54_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_68_);
lean_ctor_set(v___x_66_, 0, v_axioms_48_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_axioms_48_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_77_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_snd_64_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v_fst_63_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_73_);
v___x_75_ = v___x_61_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
lean_dec_ref(v_axioms_48_);
v_a_80_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_58_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_58_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
v___jp_90_:
{
lean_object* v___x_92_; 
v___x_92_ = l_Array_append___redArg(v___x_89_, v___y_91_);
lean_dec_ref(v___y_91_);
if (lean_obj_tag(v_val_44_) == 5)
{
lean_object* v_val_93_; lean_object* v_ctors_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_val_93_ = lean_ctor_get(v_val_44_, 0);
lean_inc_ref(v_val_93_);
lean_dec_ref_known(v_val_44_, 1);
v_ctors_94_ = lean_ctor_get(v_val_93_, 4);
lean_inc(v_ctors_94_);
lean_dec_ref(v_val_93_);
v___x_95_ = lean_array_mk(v_ctors_94_);
v___x_96_ = l_Array_append___redArg(v___x_92_, v___x_95_);
lean_dec_ref(v___x_95_);
v_refs_53_ = v___x_96_;
goto v___jp_52_;
}
else
{
lean_dec_ref(v_val_44_);
v_refs_53_ = v___x_92_;
goto v___jp_52_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0___boxed(lean_object* v___x_101_, lean_object* v_fst_102_, lean_object* v_fst_103_, lean_object* v_snd_104_, lean_object* v_val_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_____r_108_, lean_object* v_axioms_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
uint8_t v___x_7011__boxed_113_; lean_object* v_res_114_; 
v___x_7011__boxed_113_ = lean_unbox(v___x_106_);
v_res_114_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0(v___x_101_, v_fst_102_, v_fst_103_, v_snd_104_, v_val_105_, v___x_7011__boxed_113_, v___x_107_, v_____r_108_, v_axioms_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___x_107_);
lean_dec(v_snd_104_);
return v_res_114_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__1));
v___x_119_ = l_Lean_stringToMessageData(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__9));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__11));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__13));
v___x_134_ = l_Lean_stringToMessageData(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg(lean_object* v___x_135_, lean_object* v_root_136_, lean_object* v_a_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___y_142_; lean_object* v_snd_162_; lean_object* v_snd_163_; lean_object* v_fst_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_297_; 
v_snd_162_ = lean_ctor_get(v_a_137_, 1);
lean_inc(v_snd_162_);
v_snd_163_ = lean_ctor_get(v_snd_162_, 1);
lean_inc(v_snd_163_);
v_fst_164_ = lean_ctor_get(v_a_137_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_a_137_, 1);
lean_dec(v_unused_298_);
v___x_166_ = v_a_137_;
v_isShared_167_ = v_isSharedCheck_297_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_fst_164_);
lean_dec(v_a_137_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_297_;
goto v_resetjp_165_;
}
v___jp_141_:
{
if (lean_obj_tag(v___y_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_a_143_ = lean_ctor_get(v___y_142_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___y_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v___y_142_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___y_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
if (lean_obj_tag(v_a_143_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; 
lean_dec(v_root_136_);
lean_dec_ref(v___x_135_);
v_a_147_ = lean_ctor_get(v_a_143_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v_a_143_, 1);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_a_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v_a_151_; 
lean_del_object(v___x_145_);
v_a_151_ = lean_ctor_get(v_a_143_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v_a_143_, 1);
v_a_137_ = v_a_151_;
goto _start;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_root_136_);
lean_dec_ref(v___x_135_);
v_a_154_ = lean_ctor_get(v___y_142_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___y_142_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___y_142_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___y_142_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
v_resetjp_165_:
{
lean_object* v_fst_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_295_; 
v_fst_168_ = lean_ctor_get(v_snd_162_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_snd_162_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_snd_162_, 1);
lean_dec(v_unused_296_);
v___x_170_ = v_snd_162_;
v_isShared_171_ = v_isSharedCheck_295_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_fst_168_);
lean_dec(v_snd_162_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_295_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_294_; 
v_fst_172_ = lean_ctor_get(v_snd_163_, 0);
v_snd_173_ = lean_ctor_get(v_snd_163_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_snd_163_);
if (v_isSharedCheck_294_ == 0)
{
v___x_175_ = v_snd_163_;
v_isShared_176_ = v_isSharedCheck_294_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v_snd_163_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_294_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_array_get_size(v_fst_164_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_nat_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_283_; 
v___x_180_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__0));
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_sub(v___x_177_, v___x_181_);
v___x_183_ = lean_array_get(v___x_180_, v_fst_164_, v___x_182_);
lean_dec(v___x_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
v_snd_185_ = lean_ctor_get(v___x_183_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_283_ == 0)
{
v___x_187_ = v___x_183_;
v_isShared_188_ = v_isSharedCheck_283_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_snd_185_);
lean_inc(v_fst_184_);
lean_dec(v___x_183_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_283_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_checked_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_checked_189_ = lean_ctor_get(v___x_135_, 2);
v___x_190_ = 1;
v___x_191_ = lean_array_pop(v_fst_164_);
lean_inc_ref(v_checked_189_);
v___x_192_ = lean_task_get_own(v_checked_189_);
lean_inc(v_fst_184_);
v___x_193_ = lean_environment_find(v___x_192_, v_fst_184_);
if (lean_obj_tag(v___x_193_) == 1)
{
lean_object* v_val_194_; uint8_t v___x_195_; 
lean_del_object(v___x_187_);
lean_dec(v_snd_185_);
lean_del_object(v___x_175_);
lean_del_object(v___x_170_);
lean_del_object(v___x_166_);
v_val_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_193_, 1);
v___x_195_ = l_Lean_ConstantInfo_isAxiom(v_val_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_box(0);
v___x_197_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0(v___x_191_, v_fst_168_, v_fst_184_, v_snd_173_, v_val_194_, v___x_190_, v___x_178_, v___x_196_, v_fst_172_, v___y_138_, v___y_139_);
lean_dec(v_snd_173_);
v___y_142_ = v___x_197_;
goto v___jp_141_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v_fst_184_);
v___x_198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_184_, v___x_190_);
v___x_199_ = lean_array_push(v_fst_172_, v___x_198_);
v___x_200_ = lean_box(0);
v___x_201_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___lam__0(v___x_191_, v_fst_168_, v_fst_184_, v_snd_173_, v_val_194_, v___x_190_, v___x_178_, v___x_200_, v___x_199_, v___y_138_, v___y_139_);
lean_dec(v_snd_173_);
v___y_142_ = v___x_201_;
goto v___jp_141_;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec(v___x_193_);
v___x_202_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__2);
v___x_203_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__3));
lean_inc(v_root_136_);
v___x_204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_136_, v___x_190_);
v___x_205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_205_);
lean_ctor_set(v___x_187_, 0, v___x_203_);
v___x_207_ = v___x_187_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_282_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_208_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__4));
lean_inc(v_fst_184_);
v___x_209_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_184_, v___x_190_);
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_210_);
lean_ctor_set(v___x_175_, 0, v___x_208_);
v___x_212_ = v___x_175_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_281_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_213_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__5));
lean_inc(v_snd_185_);
v___x_214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_185_, v___x_190_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_215_);
lean_ctor_set(v___x_170_, 0, v___x_213_);
v___x_217_ = v___x_170_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_280_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___y_220_; 
v___x_218_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__6));
if (lean_obj_tag(v_fst_168_) == 0)
{
lean_object* v_size_279_; 
v_size_279_ = lean_ctor_get(v_fst_168_, 0);
lean_inc(v_size_279_);
v___y_220_ = v_size_279_;
goto v___jp_219_;
}
else
{
v___y_220_ = v___x_178_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v___y_220_);
v___x_221_ = l_Lean_JsonNumber_fromNat(v___y_220_);
v___x_222_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_222_);
lean_ctor_set(v___x_166_, 0, v___x_218_);
v___x_224_ = v___x_166_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_278_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_225_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__7));
lean_inc(v_snd_173_);
v___x_226_ = l_Lean_JsonNumber_fromNat(v_snd_173_);
v___x_227_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__8));
v___x_230_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_230_, 0, v___x_179_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_228_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_224_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_217_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_212_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_207_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_Json_mkObj(v___x_238_);
lean_dec_ref_known(v___x_238_, 2);
v___x_240_ = l_Lean_Json_compress(v___x_239_);
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_202_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Lean_logInfo___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_lean_runCommand_spec__1(v___x_242_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref_known(v___x_243_, 1);
v___x_244_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10, &l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10_once, _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__10);
v___x_245_ = l_Lean_MessageData_ofName(v_fst_184_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12, &l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12_once, _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__12);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_MessageData_ofName(v_snd_185_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14, &l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14_once, _init_l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__14);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Nat_reprFast(v___y_220_);
v___x_254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___x_255_ = l_Lean_MessageData_ofFormat(v___x_254_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_252_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v___x_256_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_257_, 1);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_fst_172_);
lean_ctor_set(v___x_258_, 1, v_snd_173_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_fst_168_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_191_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v_a_137_ = v___x_260_;
goto _start;
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v___x_191_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_dec(v_fst_168_);
lean_dec(v_root_136_);
lean_dec_ref(v___x_135_);
v_a_262_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_257_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_257_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v___y_220_);
lean_dec_ref(v___x_191_);
lean_dec(v_snd_185_);
lean_dec(v_fst_184_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
lean_dec(v_fst_168_);
lean_dec(v_root_136_);
lean_dec_ref(v___x_135_);
v_a_270_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_243_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_243_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
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
}
else
{
lean_object* v___x_285_; 
lean_dec(v_root_136_);
lean_dec_ref(v___x_135_);
if (v_isShared_176_ == 0)
{
v___x_285_ = v___x_175_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_fst_172_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_snd_173_);
v___x_285_ = v_reuseFailAlloc_293_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_285_);
v___x_287_ = v___x_170_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_168_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_292_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_289_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_287_);
v___x_289_ = v___x_166_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_fst_164_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_287_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___boxed(lean_object* v___x_299_, lean_object* v_root_300_, lean_object* v_a_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg(v___x_299_, v_root_300_, v_a_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4(size_t v_sz_306_, size_t v_i_307_, lean_object* v_bs_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = lean_usize_dec_lt(v_i_307_, v_sz_306_);
if (v___x_309_ == 0)
{
return v_bs_308_;
}
else
{
lean_object* v_v_310_; lean_object* v___x_311_; lean_object* v_bs_x27_312_; lean_object* v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_v_310_ = lean_array_uget(v_bs_308_, v_i_307_);
v___x_311_ = lean_unsigned_to_nat(0u);
v_bs_x27_312_ = lean_array_uset(v_bs_308_, v_i_307_, v___x_311_);
v___x_313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_310_, v___x_309_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_307_, v___x_314_);
v___x_316_ = lean_array_uset(v_bs_x27_312_, v_i_307_, v___x_313_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_addAutoBoundImplicitsInlayHint_spec__3(v_sz_306_, v___x_315_, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4___boxed(lean_object* v_sz_318_, lean_object* v_i_319_, lean_object* v_bs_320_){
_start:
{
size_t v_sz_boxed_321_; size_t v_i_boxed_322_; lean_object* v_res_323_; 
v_sz_boxed_321_ = lean_unbox_usize(v_sz_318_);
lean_dec(v_sz_318_);
v_i_boxed_322_ = lean_unbox_usize(v_i_319_);
lean_dec(v_i_319_);
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4(v_sz_boxed_321_, v_i_boxed_322_, v_bs_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NEP_audit_spec__2(lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
if (lean_obj_tag(v_a_324_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_List_reverse___redArg(v_a_325_);
return v___x_326_;
}
else
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_338_; 
v_head_327_ = lean_ctor_get(v_a_324_, 0);
v_tail_328_ = lean_ctor_get(v_a_324_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_338_ == 0)
{
v___x_330_ = v_a_324_;
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_head_327_);
lean_dec(v_a_324_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = 1;
v___x_333_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_327_, v___x_332_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_a_325_);
lean_ctor_set(v___x_330_, 0, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_a_325_);
v___x_335_ = v_reuseFailAlloc_337_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v_a_324_ = v_tail_328_;
v_a_325_ = v___x_335_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(lean_object* v_xs_339_, lean_object* v_ys_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_zero_342_; uint8_t v_isZero_343_; 
v_zero_342_ = lean_unsigned_to_nat(0u);
v_isZero_343_ = lean_nat_dec_eq(v_x_341_, v_zero_342_);
if (v_isZero_343_ == 1)
{
lean_dec(v_x_341_);
return v_isZero_343_;
}
else
{
lean_object* v_one_344_; lean_object* v_n_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_one_344_ = lean_unsigned_to_nat(1u);
v_n_345_ = lean_nat_sub(v_x_341_, v_one_344_);
lean_dec(v_x_341_);
v___x_346_ = lean_array_fget_borrowed(v_xs_339_, v_n_345_);
v___x_347_ = lean_array_fget_borrowed(v_ys_340_, v_n_345_);
v___x_348_ = lean_string_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v_n_345_);
return v___x_348_;
}
else
{
v_x_341_ = v_n_345_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg___boxed(lean_object* v_xs_350_, lean_object* v_ys_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v_xs_350_, v_ys_351_, v_x_352_);
lean_dec_ref(v_ys_351_);
lean_dec_ref(v_xs_350_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l_NEP_audit___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_NEP_audit___closed__0));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_NEP_audit___closed__5(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l_NEP_audit___closed__4));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_NEP_audit(lean_object* v_root_373_, lean_object* v_stem_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; uint8_t v___y_386_; lean_object* v___x_412_; lean_object* v_env_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_412_ = lean_st_ref_get(v_a_376_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_env_413_);
lean_dec(v___x_412_);
v___x_414_ = 0;
v___x_415_ = l_Lean_Environment_setExporting(v_env_413_, v___x_414_);
lean_inc_n(v_root_373_, 4);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_root_373_);
lean_ctor_set(v___x_416_, 1, v_root_373_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_mk_empty_array_with_capacity(v___x_417_);
v___x_419_ = lean_array_push(v___x_418_, v___x_416_);
v___x_420_ = lean_box(1);
v___x_421_ = l_Lean_NameSet_insert(v___x_420_, v_root_373_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = ((lean_object*)(l_NEP_audit___closed__3));
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_419_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg(v___x_415_, v_root_373_, v___x_425_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_569_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v_snd_428_ = lean_ctor_get(v_a_427_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_a_427_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_a_427_, 0);
lean_dec(v_unused_570_);
v___x_430_ = v_a_427_;
v_isShared_431_ = v_isSharedCheck_569_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_dec(v_a_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_569_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_snd_432_; lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_568_; 
v_snd_432_ = lean_ctor_get(v_snd_428_, 1);
v_fst_433_ = lean_ctor_get(v_snd_428_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_snd_428_);
if (v_isSharedCheck_568_ == 0)
{
v___x_435_ = v_snd_428_;
v_isShared_436_ = v_isSharedCheck_568_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_433_);
lean_dec(v_snd_428_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_568_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_567_; 
v_fst_437_ = lean_ctor_get(v_snd_432_, 0);
v_snd_438_ = lean_ctor_get(v_snd_432_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_snd_432_);
if (v_isSharedCheck_567_ == 0)
{
v___x_440_ = v_snd_432_;
v_isShared_441_ = v_isSharedCheck_567_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_inc(v_fst_437_);
lean_dec(v_snd_432_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_567_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_519_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_559_; 
if (lean_obj_tag(v_fst_433_) == 0)
{
lean_object* v_size_566_; 
v_size_566_ = lean_ctor_get(v_fst_433_, 0);
lean_inc(v_size_566_);
v___y_559_ = v_size_566_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_422_;
goto v___jp_558_;
}
v___jp_442_:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_446_ = lean_obj_once(&l_NEP_audit___closed__5, &l_NEP_audit___closed__5_once, _init_l_NEP_audit___closed__5);
v___x_447_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg___closed__3));
v___x_448_ = 1;
v___x_449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_373_, v___x_448_);
v___x_450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_450_);
lean_ctor_set(v___x_440_, 0, v___x_447_);
v___x_452_ = v___x_440_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_477_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_453_ = ((lean_object*)(l_NEP_audit___closed__6));
v___x_454_ = lean_array_get_size(v___y_443_);
lean_dec_ref(v___y_443_);
v___x_455_ = l_Lean_JsonNumber_fromNat(v___x_454_);
v___x_456_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_456_);
lean_ctor_set(v___x_435_, 0, v___x_453_);
v___x_458_ = v___x_435_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_476_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_459_ = ((lean_object*)(l_NEP_audit___closed__7));
v___x_460_ = l_Lean_JsonNumber_fromNat(v_snd_438_);
v___x_461_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_461_);
lean_ctor_set(v___x_430_, 0, v___x_459_);
v___x_463_ = v___x_430_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_475_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_464_ = ((lean_object*)(l_NEP_audit___closed__8));
lean_inc_ref(v___y_444_);
v___x_465_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___y_444_);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = ((lean_object*)(l_NEP_audit___closed__9));
lean_inc_ref(v___y_445_);
v___x_468_ = l_Array_toJson___at___00Lean_Server_Test_Runner_Client_instToJsonHyp_toJson_spec__1(v___y_445_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l_NEP_audit___closed__10));
v___x_471_ = lean_array_get_size(v___y_444_);
v___x_472_ = lean_array_get_size(v___y_445_);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
v___y_379_ = v___x_452_;
v___y_380_ = v___x_469_;
v___y_381_ = v___x_446_;
v___y_382_ = v___x_458_;
v___y_383_ = v___x_466_;
v___y_384_ = v___x_463_;
v___y_385_ = v___x_470_;
v___y_386_ = v___x_414_;
goto v___jp_378_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v___y_444_, v___y_445_, v___x_471_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
v___y_379_ = v___x_452_;
v___y_380_ = v___x_469_;
v___y_381_ = v___x_446_;
v___y_382_ = v___x_458_;
v___y_383_ = v___x_466_;
v___y_384_ = v___x_463_;
v___y_385_ = v___x_470_;
v___y_386_ = v___x_474_;
goto v___jp_378_;
}
}
}
}
}
v___jp_478_:
{
lean_object* v___x_485_; 
v___x_485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_validateCat_spec__3___redArg(v___y_482_, v___y_481_, v___y_479_, v___y_484_);
lean_dec(v___y_484_);
lean_dec(v___y_482_);
v___y_443_ = v___y_480_;
v___y_444_ = v___y_483_;
v___y_445_ = v___x_485_;
goto v___jp_442_;
}
v___jp_486_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_le(v___y_492_, v___y_487_);
if (v___x_493_ == 0)
{
lean_dec(v___y_487_);
lean_inc(v___y_492_);
v___y_479_ = v___y_492_;
v___y_480_ = v___y_488_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_489_;
v___y_483_ = v___y_491_;
v___y_484_ = v___y_492_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___y_492_;
v___y_480_ = v___y_488_;
v___y_481_ = v___y_490_;
v___y_482_ = v___y_489_;
v___y_483_ = v___y_491_;
v___y_484_ = v___y_487_;
goto v___jp_478_;
}
}
v___jp_494_:
{
lean_object* v___x_497_; lean_object* v_a_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
lean_inc(v_root_373_);
v___x_497_ = l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(v_root_373_, v_a_376_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
v_sz_499_ = lean_array_size(v_a_498_);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00NEP_audit_spec__4(v_sz_499_, v___x_500_, v_a_498_);
v___x_502_ = lean_array_get_size(v___x_501_);
v___x_503_ = lean_nat_dec_eq(v___x_502_, v___x_422_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_nat_sub(v___x_502_, v___x_417_);
v___x_505_ = lean_nat_dec_le(v___x_422_, v___x_504_);
if (v___x_505_ == 0)
{
lean_inc(v___x_504_);
v___y_487_ = v___x_504_;
v___y_488_ = v___y_495_;
v___y_489_ = v___x_502_;
v___y_490_ = v___x_501_;
v___y_491_ = v___y_496_;
v___y_492_ = v___x_504_;
goto v___jp_486_;
}
else
{
v___y_487_ = v___x_504_;
v___y_488_ = v___y_495_;
v___y_489_ = v___x_502_;
v___y_490_ = v___x_501_;
v___y_491_ = v___y_496_;
v___y_492_ = v___x_422_;
goto v___jp_486_;
}
}
else
{
v___y_443_ = v___y_495_;
v___y_444_ = v___y_496_;
v___y_445_ = v___x_501_;
goto v___jp_442_;
}
}
v___jp_506_:
{
lean_object* v___x_511_; 
v___x_511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_validateCat_spec__3___redArg(v___y_508_, v_fst_437_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec(v___y_508_);
v___y_495_ = v___y_507_;
v___y_496_ = v___x_511_;
goto v___jp_494_;
}
v___jp_512_:
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_le(v___y_516_, v___y_513_);
if (v___x_517_ == 0)
{
lean_dec(v___y_513_);
lean_inc(v___y_516_);
v___y_507_ = v___y_514_;
v___y_508_ = v___y_515_;
v___y_509_ = v___y_516_;
v___y_510_ = v___y_516_;
goto v___jp_506_;
}
else
{
v___y_507_ = v___y_514_;
v___y_508_ = v___y_515_;
v___y_509_ = v___y_516_;
v___y_510_ = v___y_513_;
goto v___jp_506_;
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_520_ = ((lean_object*)(l_NEP_audit___closed__11));
v___x_521_ = lean_string_append(v_stem_374_, v___x_520_);
v___x_522_ = ((lean_object*)(l_NEP_audit___closed__12));
lean_inc_ref(v___y_519_);
v___x_523_ = lean_array_to_list(v___y_519_);
v___x_524_ = lean_box(0);
v___x_525_ = l_List_mapTR_loop___at___00NEP_audit_spec__2(v___x_523_, v___x_524_);
v___x_526_ = l_String_intercalate(v___x_522_, v___x_525_);
v___x_527_ = lean_string_append(v___x_526_, v___x_522_);
v___x_528_ = l_IO_FS_writeFile(v___x_521_, v___x_527_);
lean_dec_ref(v___x_527_);
lean_dec_ref(v___x_521_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
lean_dec_ref_known(v___x_528_, 1);
v___x_529_ = lean_array_get_size(v_fst_437_);
v___x_530_ = lean_nat_dec_eq(v___x_529_, v___x_422_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_nat_sub(v___x_529_, v___x_417_);
v___x_532_ = lean_nat_dec_le(v___x_422_, v___x_531_);
if (v___x_532_ == 0)
{
lean_inc(v___x_531_);
v___y_513_ = v___x_531_;
v___y_514_ = v___y_519_;
v___y_515_ = v___x_529_;
v___y_516_ = v___x_531_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___x_531_;
v___y_514_ = v___y_519_;
v___y_515_ = v___x_529_;
v___y_516_ = v___x_422_;
goto v___jp_512_;
}
}
else
{
v___y_495_ = v___y_519_;
v___y_496_ = v_fst_437_;
goto v___jp_494_;
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___y_519_);
lean_del_object(v___x_440_);
lean_dec(v_snd_438_);
lean_dec(v_fst_437_);
lean_del_object(v___x_435_);
lean_del_object(v___x_430_);
lean_dec(v_root_373_);
v_a_533_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_545_ == 0)
{
v___x_535_ = v___x_528_;
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_528_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_ref_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v_ref_537_ = lean_ctor_get(v_a_375_, 7);
v___x_538_ = lean_io_error_to_string(v_a_533_);
v___x_539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___x_540_ = l_Lean_MessageData_ofFormat(v___x_539_);
lean_inc(v_ref_537_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_ref_537_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_541_);
v___x_543_ = v___x_535_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
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
v___jp_546_:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(v___y_548_, v___y_547_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec(v___y_548_);
v___y_519_ = v___x_551_;
goto v___jp_518_;
}
v___jp_552_:
{
uint8_t v___x_557_; 
v___x_557_ = lean_nat_dec_le(v___y_556_, v___y_555_);
if (v___x_557_ == 0)
{
lean_dec(v___y_555_);
lean_inc(v___y_556_);
v___y_547_ = v___y_554_;
v___y_548_ = v___y_553_;
v___y_549_ = v___y_556_;
v___y_550_ = v___y_556_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___y_554_;
v___y_548_ = v___y_553_;
v___y_549_ = v___y_556_;
v___y_550_ = v___y_555_;
goto v___jp_546_;
}
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_mk_empty_array_with_capacity(v___y_559_);
lean_dec(v___y_559_);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_560_, v_fst_433_);
v___x_562_ = lean_array_get_size(v___x_561_);
v___x_563_ = lean_nat_dec_eq(v___x_562_, v___x_422_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_nat_sub(v___x_562_, v___x_417_);
v___x_565_ = lean_nat_dec_le(v___x_422_, v___x_564_);
if (v___x_565_ == 0)
{
lean_inc(v___x_564_);
v___y_553_ = v___x_562_;
v___y_554_ = v___x_561_;
v___y_555_ = v___x_564_;
v___y_556_ = v___x_564_;
goto v___jp_552_;
}
else
{
v___y_553_ = v___x_562_;
v___y_554_ = v___x_561_;
v___y_555_ = v___x_564_;
v___y_556_ = v___x_422_;
goto v___jp_552_;
}
}
else
{
v___y_519_ = v___x_561_;
goto v___jp_518_;
}
}
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_stem_374_);
lean_dec(v_root_373_);
v_a_571_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_426_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_426_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
v___jp_378_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_387_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_387_, 0, v___y_386_);
lean_inc_ref(v___y_385_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___y_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v___y_380_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___y_383_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v___y_384_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___y_382_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v___y_379_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_Json_mkObj(v___x_395_);
lean_dec_ref_known(v___x_395_, 2);
v___x_397_ = l_Lean_Json_compress(v___x_396_);
v___x_398_ = l_Lean_stringToMessageData(v___x_397_);
lean_inc_ref(v___y_381_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___y_381_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = l_Lean_logInfo___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_lean_runCommand_spec__1(v___x_399_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_410_; 
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_411_);
v___x_402_ = v___x_400_;
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
else
{
lean_dec(v___x_400_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_410_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
if (v___y_386_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_del_object(v___x_402_);
v___x_404_ = lean_obj_once(&l_NEP_audit___closed__1, &l_NEP_audit___closed__1_once, _init_l_NEP_audit___closed__1);
v___x_405_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v___x_404_, v_a_375_, v_a_376_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_406_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_NEP_audit___boxed(lean_object* v_root_579_, lean_object* v_stem_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_NEP_audit(v_root_579_, v_stem_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0(lean_object* v_fst_585_, lean_object* v_as_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___redArg(v_fst_585_, v_as_586_, v_sz_587_, v_i_588_, v_b_589_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0___boxed(lean_object* v_fst_594_, lean_object* v_as_595_, lean_object* v_sz_596_, lean_object* v_i_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
size_t v_sz_boxed_602_; size_t v_i_boxed_603_; lean_object* v_res_604_; 
v_sz_boxed_602_ = lean_unbox_usize(v_sz_596_);
lean_dec(v_sz_596_);
v_i_boxed_603_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00NEP_audit_spec__0(v_fst_594_, v_as_595_, v_sz_boxed_602_, v_i_boxed_603_, v_b_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v_as_595_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1(lean_object* v___x_605_, lean_object* v_root_606_, lean_object* v_inst_607_, lean_object* v_a_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___redArg(v___x_605_, v_root_606_, v_a_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1___boxed(lean_object* v___x_613_, lean_object* v_root_614_, lean_object* v_inst_615_, lean_object* v_a_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Init_While_0__whileM_erased___at___00NEP_audit_spec__1(v___x_613_, v_root_614_, v_inst_615_, v_a_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_620_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00NEP_audit_spec__3(lean_object* v_xs_621_, lean_object* v_ys_622_, lean_object* v_hsz_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = l_Array_isEqvAux___at___00NEP_audit_spec__3___redArg(v_xs_621_, v_ys_622_, v_x_624_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00NEP_audit_spec__3___boxed(lean_object* v_xs_627_, lean_object* v_ys_628_, lean_object* v_hsz_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Array_isEqvAux___at___00NEP_audit_spec__3(v_xs_627_, v_ys_628_, v_hsz_629_, v_x_630_, v_x_631_);
lean_dec_ref(v_ys_628_);
lean_dec_ref(v_xs_627_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NFJ__WALKER(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
