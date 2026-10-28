import R1Z.PV_RunJoin_OuterABI30
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OuterABILaws30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30

theorem compilation_reverse (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) :
    compilationFromForest (compilationToForest c) = c := by cases c; rfl
#print axioms compilation_reverse

theorem format_roundtrip (e : BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    formatToForest (formatFromForest e) = e := by cases e <;> rfl
#print axioms format_roundtrip

theorem format_reverse (e : pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError) :
    formatFromForest (formatToForest e) = e := by cases e <;> rfl
#print axioms format_reverse

theorem leaf_roundtrip (e : BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1) :
    leafErrorToForest (leafErrorFromForest e) = e := by cases e <;> rfl
#print axioms leaf_roundtrip

theorem leaf_reverse (e : pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1) :
    leafErrorFromForest (leafErrorToForest e) = e := by cases e <;> rfl
#print axioms leaf_reverse

theorem tree_identity (e : BuilderForestAdmissionPort.pool_v1.incremental_merkle.PoolV1TreeError) :
    treeErrorFromForest e = e := by cases e <;> rfl
#print axioms tree_identity

theorem error_roundtrip (e : BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceErrorV1) :
    errorToForest (errorFromForest e) = e := by
  cases e <;> simp only [errorToForest,errorFromForest,format_roundtrip,leaf_roundtrip,tree_identity]
#print axioms error_roundtrip

theorem error_reverse (e : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) :
    errorFromForest (errorToForest e) = e := by
  cases e <;> simp only [errorToForest,errorFromForest,format_reverse,leaf_reverse,tree_identity]
#print axioms error_reverse

theorem error_injective : Function.Injective errorFromForest := by
  intro a b h
  simpa only [error_roundtrip] using congrArg errorToForest h
#print axioms error_injective
end R1Z.PV_RunJoin_OuterABILaws30
