import R1Z.PV_Join_CodecCaller
import R1Z.PV_Join_Field
import R1Z.PV_Join_Generic
import R1Z.PV_Join_Merkle
import R1Z.PV_Join_Heap
import R1Z.PV_Join_State
import R1Z.PV_Join_StateChanged
import R1Z.PV_Join_Borrow
import R1Z.PV_Join_Current72
import R1Z.PV_Join_Current80
import R1Z.PV_Join_Current105
import R1Z.PV_Join_CB3
import R1Z.PV_Join_ProofClosure
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_AggregateCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
variable [ExternalTypes]
/-- Preserve all remaining fields and replace these callbacks by the checked
source selections. No property of the supplied raw callback is assumed. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BodyStore.selected ops with
    op3 := @ExternalFuns.op3 _ (PV_CB_Take.selected ops),
    op71 := @ExternalFuns.op71 _ (PV_CB_Codecs.selected ops),
    op72 := @ExternalFuns.op72 _ (PV_CB_Op72Exact.selected ops),
    op77 := @ExternalFuns.op77 _ (PV_CB_PointClone.selected ops),
    op80 := @ExternalFuns.op80 _ (PV_CB_Op80Exact.selected ops),
    op81 := @ExternalFuns.op81 _ (PV_CB_Heap.selected (ProverRwP6BodyStore.selected ops)),
    op82 := @ExternalFuns.op82 _ (PV_CB_Merkle.selected ops),
    op83 := @ExternalFuns.op83 _ (PV_CB_Merkle.selected ops),
    op84 := @ExternalFuns.op84 _ (PV_CB_Merkle.selected ops),
    op86 := @ExternalFuns.op86 _ (PV_CB_Merkle.selected ops),
    op100 := @ExternalFuns.op100 _ (PV_CB_Field.selected ops),
    op101 := @ExternalFuns.op101 _ (PV_CB_Field.selected ops),
    op105 := @ExternalFuns.op105 _ (PV_CB_Op105Exact.selected ops),
    op107 := @ExternalFuns.op107 _ (PV_CB_Field.selected ops),
    op109 := @ExternalFuns.op109 _ (PV_CB_Field.selected ops),
    op111 := @ExternalFuns.op111 _ (PV_CB_State.selected ops),
    op114 := @ExternalFuns.op114 _ (PV_CB_Op114Source.selected ops),
    op118 := @ExternalFuns.op118 _ (PV_CB_State.selected ops),
    op127 := @ExternalFuns.op127 _ (PV_CB_Borrow.selected ops),
    op128 := @ExternalFuns.op128 _ (PV_CB_Borrow.selected ops),
    op130 := @ExternalFuns.op130 _ (PV_CB_Borrow.selected ops),
    op131 := @ExternalFuns.op131 _ (PV_CB_Borrow.selected ops),
    op246 := @PV_CB3_ShippedOp246.multiproof.binary_parent}
theorem dictionary (ops : ExternalFuns) : selected ops = ProverRwP6BodyStore.selected ops := by
  have h3 : @ExternalFuns.op3 _ (PV_CB_Take.selected ops) =
      @ExternalFuns.op3 _ (ProverRwP6BodyStore.selected ops) := by
    funext T inst x
    exact (PV_CB_TakeSource.op3_source ops inst x).trans (PV_Join_Generic.op3_source ops inst x).symm
  have h71 : @ExternalFuns.op71 _ (PV_CB_Codecs.selected ops) =
      @ExternalFuns.op71 _ (ProverRwP6BodyStore.selected ops) := by
    funext s
    exact (PV_CB_Op71Source.op71_source ops s).trans (PV_Join_Codecs.op71_source ops s).symm
  have h72 : @ExternalFuns.op72 _ (PV_CB_Op72Exact.selected ops) =
      @ExternalFuns.op72 _ (ProverRwP6BodyStore.selected ops) := by
    funext x bytes
    exact (PV_CB_Op72Exact.op72_source ops x bytes).trans (PV_Join_Current72.op72_source ops x bytes).symm
  have h77 : @ExternalFuns.op77 _ (PV_CB_PointClone.selected ops) =
      @ExternalFuns.op77 _ (ProverRwP6BodyStore.selected ops) := by
    funext E inst p
    exact (PV_CB_Op77Source.op77_source ops inst p).trans (PV_Join_Generic.op77_source ops inst p).symm
  have h80 : @ExternalFuns.op80 _ (PV_CB_Op80Exact.selected ops) =
      @ExternalFuns.op80 _ (ProverRwP6BodyStore.selected ops) := by
    funext E inst x y h
    exact (PV_CB_Op80Exact.op80_source ops inst x y h).trans (PV_Join_Current80.op80_source ops inst x y h).symm
  have h81 : @ExternalFuns.op81 _ (PV_CB_Heap.selected (ProverRwP6BodyStore.selected ops)) =
      @ExternalFuns.op81 _ (ProverRwP6BodyStore.selected ops) := by
    funext T copy n value
    exact (PV_CB_Op81Source.op81_source (ProverRwP6BodyStore.selected ops) copy n value).trans (PV_Join_Heap.op81_source ops copy n value).symm
  have h82 : @ExternalFuns.op82 _ (PV_CB_Merkle.selected ops) =
      @ExternalFuns.op82 _ (ProverRwP6BodyStore.selected ops) := by
    exact (PV_CB_Op82Source.op82_source ops ).trans (PV_Join_Merkle.op82_source ops ).symm
  have h83 : @ExternalFuns.op83 _ (PV_CB_Merkle.selected ops) =
      @ExternalFuns.op83 _ (ProverRwP6BodyStore.selected ops) := by
    exact (PV_CB_Op83Source.op83_source ops ).trans (PV_Join_Merkle.op83_source ops ).symm
  have h84 : @ExternalFuns.op84 _ (PV_CB_Merkle.selected ops) =
      @ExternalFuns.op84 _ (ProverRwP6BodyStore.selected ops) := by
    funext hash tag values
    exact (PV_CB_Op84Source.op84_source ops hash tag values).trans (PV_Join_Merkle.op84_source ops hash tag values).symm
  have h86 : @ExternalFuns.op86 _ (PV_CB_Merkle.selected ops) =
      @ExternalFuns.op86 _ (ProverRwP6BodyStore.selected ops) := by
    exact (PV_CB_Op86Source.op86_source ops ).trans (PV_Join_Merkle.op86_source ops ).symm
  have h100 : @ExternalFuns.op100 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op100 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op100Source.op100_source ops x).trans (PV_Join_Field.op100_source ops x).symm
  have h101 : @ExternalFuns.op101 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op101 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op101Source.op101_source ops x).trans (PV_Join_Field.op101_source ops x).symm
  have h105 : @ExternalFuns.op105 _ (PV_CB_Op105Exact.selected ops) =
      @ExternalFuns.op105 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_Join_Current105.selected_bridge ops x).symm
  have h107 : @ExternalFuns.op107 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op107 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op107Source.op107_source ops x).trans (PV_Join_Field.op107_source ops x).symm
  have h109 : @ExternalFuns.op109 _ (PV_CB_Field.selected ops) =
      @ExternalFuns.op109 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op109Source.op109_source ops x).trans (PV_Join_Field.op109_source ops x).symm
  have h111 : @ExternalFuns.op111 _ (PV_CB_State.selected ops) =
      @ExternalFuns.op111 _ (ProverRwP6BodyStore.selected ops) := by
    exact (PV_CB_Op111Source.op111_source ops ).trans (PV_Join_State.op111_source ops ).symm
  have h114 : @ExternalFuns.op114 _ (PV_CB_Op114Source.selected ops) =
      @ExternalFuns.op114 _ (ProverRwP6BodyStore.selected ops) := by
    funext a b
    exact (PV_Join_StateChanged.selected_bridge ops a b).symm
  have h118 : @ExternalFuns.op118 _ (PV_CB_State.selected ops) =
      @ExternalFuns.op118 _ (ProverRwP6BodyStore.selected ops) := by
    funext x
    exact (PV_CB_Op118Source.op118_source ops x).trans (PV_Join_State.op118_source ops x).symm
  have h127 : @ExternalFuns.op127 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op127 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op127Source.op127_source ops inst x).trans (PV_Join_Borrow.op127_source ops inst x).symm
  have h128 : @ExternalFuns.op128 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op128 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op128Source.op128_source ops inst x).trans (PV_Join_Borrow.op128_source ops inst x).symm
  have h130 : @ExternalFuns.op130 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op130 _ (ProverRwP6BodyStore.selected ops) := by
    funext Z inst x
    exact (PV_CB_Op130Source.op130_source ops inst x).trans (PV_Join_Borrow.op130_source ops inst x).symm
  have h131 : @ExternalFuns.op131 _ (PV_CB_Borrow.selected ops) =
      @ExternalFuns.op131 _ (ProverRwP6BodyStore.selected ops) := by
    funext T Z view inst x
    exact (PV_CB_Op131Source.op131_source ops view inst x).trans (PV_Join_Borrow.op131_source ops view inst x).symm
  have h246 : @PV_CB3_ShippedOp246.multiproof.binary_parent =
      @ExternalFuns.op246 _ (ProverRwP6BodyStore.selected ops) := by
    funext H inst hash left right
    exact (PV_Join_CB3.op246_source ops inst hash left right).symm
  unfold selected
  rw [h3, h71, h72, h77, h80, h81, h82, h83, h84, h86, h100, h101, h105, h107, h109, h111, h114, h118, h127, h128, h130, h131, h246]
  rfl
theorem refinement_of_data (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)) :
    data (ProverRwBodyNativeWideInstall.execute (selected ops) store pub compiled v hash binding digest attempt s)=model →
      ProverRwBodyNativeWideInstall.execute (selected ops) store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  rw [dictionary]
  exact PV_Join_CodecCaller.refinement_of_data ops store pub compiled v hash
    binding digest attempt s after accepted reservation model
#print axioms dictionary
#print axioms refinement_of_data
end R1Z.PV_Join_AggregateCaller
#join_closure R1Z.PV_Join_AggregateCaller.refinement_of_data
