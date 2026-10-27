import RPz7_Hiq_Suffix
import RPz7_Hist_PairExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_Association
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open GExq_AccountExperiment

theorem selected {A : Type} (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (input : FirstInputs A) (next : SecondInputs A) (reply1 : FirstReply A) (reply2 : SecondReply A)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (v : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (cuts : SourceCuts ops input.entry.first (next.entry.second S2W_D189Wrappers.secondSizes) saved f s)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id
      (next.entry.second S2W_D189Wrappers.secondSizes) next.data next.slot = ok (.Ok v))
    (encoding : ops.op22 v.statement = ok (.Ok s.encoded)) :
    Hiq_ByteSelection.select ops id (input,reply1,some (next,reply2)) = Hist_PairExperiment.select ⟨f,s⟩ := by
  obtain ⟨proof1,public1⟩ := Hiq_Suffix.first _ _ _ _ _ _ cuts
  have proof2 := Hiq_Suffix.second _ _ _ _ _ _ cuts
  have public2 := Hiq_ByteSelection.public2_read _ _ _ _ _ _ _ validation encoding
  simp only [Hiq_ByteSelection.select,Hist_PairExperiment.select,proof1,public1,proof2,public2]
  rfl

/-- Factory over actual source successes; selection requires no separately
supplied four-byte output association. The original full cuts remain outputs. -/
theorem source {A : Type} (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (input : FirstInputs A) (next : SecondInputs A) (reply1 : FirstReply A) (reply2 : SecondReply A)
    (saved : alloc.vec.Vec U8)
    (first : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id input.entry.first input.data = ok (.Ok saved))
    (second : AdapterRw.r1_pool_adapter.owned.stage2_owned ops id
      (next.entry.second S2W_D189Wrappers.secondSizes) next.data next.slot = ok (.Ok ())) :
    ∃ f s v, SourceCuts ops input.entry.first (next.entry.second S2W_D189Wrappers.secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id
        (next.entry.second S2W_D189Wrappers.secondSizes) next.data next.slot = ok (.Ok v) ∧
      ops.op22 v.statement = ok (.Ok s.encoded) ∧
      Hiq_ByteSelection.select ops id (input,reply1,some (next,reply2)) = Hist_PairExperiment.select ⟨f,s⟩ := by
  obtain ⟨f,s,v,cuts,get,validate,encode⟩ := Hist_ArgumentCuts.source ops id _ _ _ _ _ saved first second
  exact ⟨f,s,v,cuts,get,validate,encode,selected _ _ _ _ _ _ _ _ _ _ cuts validate encode⟩

#print axioms selected
#print axioms source
end AspisR1.Hiq_Association
end
