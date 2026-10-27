import R1Z.PV_RunJoin_UniversalTransition22
import R1Z.PV_Src_NativeDirections
import R1Z.PV_RunJoin_ValueBits20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalCompilerFrame22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields

/-- All successful compiler returns preserve the caller's directions and
value-bit computations, and select the public statement's variant. Neither
fixture output nor a concrete compiler execution is reduced here. -/
theorem payload [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    compiled.trace.private_directions = BuilderRecordsPath.bits (PV_Src_NativeDirections.reference input) ∧
      compiled.trace.value_bits = Array.make 3#usize [PV_RunJoin_ValueBits20.bits input.pair.value,
        PV_RunJoin_ValueBits20.bits out,PV_RunJoin_ValueBits20.bits change.value] ∧
      compiled.trace.variant = (if publicInput.recipient_commitment.isSome then
        pair_trace.PoolV1PairTraceVariantV1.PrivateTransfer else .Withdrawal) := by
  rcases publicInput with ⟨pubAnchor,pubNullifier,pubRecipient,pubChange,pubAsset⟩
  cases pubRecipient <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    rw [PV_Src_NativeDirections.run_eq input] at h
    simp only [PV_RunJoin_ValueBits20.source,bind_tc_ok] at h
    repeat' first
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
      | (cases h; exact ⟨rfl,rfl,rfl⟩)
#print axioms payload

theorem native [ExternalLinear] [Records] (i : PV_Src_NativeInput.Input)
    (success : PV_Src_NativeInput.run i = ok (.Ok i.compiled)) :
    i.compiled.trace.private_directions = BuilderRecordsPath.bits (PV_Src_NativeDirections.reference i.witness) ∧
      i.compiled.trace.value_bits = Array.make 3#usize [PV_RunJoin_ValueBits20.bits i.witness.pair.value,
        PV_RunJoin_ValueBits20.bits (PV_Src_NativeInput.outputValue i.request),
        PV_RunJoin_ValueBits20.bits i.change.value] ∧
      i.compiled.trace.variant = (match i.request with
        | .transfer _ _ => pair_trace.PoolV1PairTraceVariantV1.PrivateTransfer
        | .withdrawal _ => .Withdrawal) := by
  have fields := payload i.witness (PV_Src_NativeInput.outputValue i.request)
    (PV_Src_NativeInput.recipient i.request) i.change
    (PV_Src_NativeInput.forestPublic i.request) i.laneAnchor i.snapshot i.compiled success
  refine ⟨fields.1,fields.2.1,?_⟩
  cases hr : i.request <;> simpa [PV_Src_NativeInput.forestPublic,hr] using fields.2.2
#print axioms native
end R1Z.PV_RunJoin_UniversalCompilerFrame22
