import R1Z.PV_RunJoin_UniversalCompilerFrame22
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalReturnedLate22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields

theorem result_continue {α ε : Type} {r : core.result.Result α ε} {value : α}
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue value)) : r = .Ok value := by
  cases r with
  | Ok a =>
    have same := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj h)
    exact congrArg core.result.Result.Ok same
  | Err error => cases h
#print axioms result_continue

theorem call_continue {α ε : Type} {call : Result (core.result.Result α ε)}
    {r : core.result.Result α ε} {value : α}
    (hc : call = ok r)
    (hb : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue value)) :
    call = ok (.Ok value) := hc.trans (congrArg Result.ok (result_continue hb))
#print axioms call_continue

theorem exists_success {α β ε : Type} {f : Result α}
    {g : α → Result (core.result.Result β ε)} {value : β}
    {leaf : α} {r : core.result.Result β ε}
    (hf : f = ok leaf) (hg : g leaf = ok r)
    (hb : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue value)) :
    ∃ leaf, f = ok leaf ∧ g leaf = ok (.Ok value) :=
  ⟨leaf,hf,call_continue hg hb⟩
#print axioms exists_success

theorem exists_and_success {α β ε : Type} {p : Prop} {f : Result α}
    {g : α → Result (core.result.Result β ε)} {value : β}
    {leaf : α} {r : core.result.Result β ε}
    (hp : p) (hf : f = ok leaf) (hg : g leaf = ok r)
    (hb : core.result.Result.Insts.CoreOpsTry.branch r = ok (.Continue value)) :
    ∃ leaf, p ∧ f = ok leaf ∧ g leaf = ok (.Ok value) :=
  ⟨leaf,hp,hf,call_continue hg hb⟩
#print axioms exists_and_success

/-- Every successful outer compiler return uses the actual late_append
result on its actual record/output-pair, including both native error layers. -/
theorem returned [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records leaf,
      pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.output_pair records = ok leaf ∧
      pair_forest_trace.late_append records snapshot leaf =
        ok (.Ok compiled.public_statement.candidate_afterstate) := by
  rcases publicInput with ⟨pubAnchor,pubNullifier,pubRecipient,pubChange,pubAsset⟩
  cases pubRecipient <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    pv_peel h with records hr
    refine ⟨records,?_⟩
    repeat' first
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
      | (cases h)
    all_goals
      apply exists_and_success hr <;> assumption
#print axioms returned
end R1Z.PV_RunJoin_UniversalReturnedLate22
