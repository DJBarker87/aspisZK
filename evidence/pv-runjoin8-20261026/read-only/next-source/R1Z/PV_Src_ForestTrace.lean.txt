import R1Z.PV_Src_ForestPartsTotal
import R1Z.BuilderFieldNormalization

/-! Successful, exact raw trace from the actual extracted Parts/banks/columns
pipeline. The fallback in `trace` is unreachable, proved here for all records. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_ForestTrace
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
abbrev Columns := Array (alloc.vec.Vec U32) 16#usize

def run (w : RW) (p : RP) : Result Columns := do
  let (_,_,_,merged) ← merged_banks w p
  BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder.columns merged

theorem run_exact (w : RW) (p : RP) :
    ∃ out, run w p = ok out ∧
      (∀ c, c < 16 → (out.val[c]!).val.length = 1024) ∧
      ∀ c r, PV_Src_Forest_Columns.read out c r = copyCellMerged (wordWitness w) (wordPublic p) c r := by
  obtain ⟨pt,hpt⟩ := PV_Src_ForestPartsTotal.parts_total w p
  obtain ⟨merged,out,hb,hc,hl,hr⟩ := PV_Src_Forest_PartsComplete.banks_columns w p pt hpt
  refine ⟨out,?_,hl,hr⟩
  rw [run,hb]
  simp only [bind_tc_ok]
  exact hc

def trace {K : Type} [Field K] (w : RW) (p : RP) : R0P.Trace K :=
  fun c r => liftU (PV_Src_Forest_Columns.read
    (okOr (run w p) (Array.repeat 16#usize ⟨[],by simp⟩)) c r)

theorem trace_eq {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
    (w : RW) (p : RP) : trace (K := K) w p =
      BuilderRefinement.mergedTrace (wordWitness w) (wordPublic p) := by
  obtain ⟨out,ho,_,hr⟩ := run_exact w p
  funext c r
  change liftU (PV_Src_Forest_Columns.read (okOr (run w p) _) c r) = _
  rw [ho,okOr_ok,hr]
  rfl

theorem canonical_trace {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
    (w : RW) (p : RP) (pub : R0P.Public R1J.SpendWitnessMap.F)
    (words : WitnessOk (wordWitness w))
    (publicCorr : PubCorr (wordPublic p) (R1J.SpendWitnessMap.mapPub (K := K) pub)) :
    trace (K := K) w p = BuilderRefinement.mergedTrace
      (BuilderCanonical.rustWitness (BuilderRecordCanonical.witness (wordWitness w)))
      (BuilderCanonical.rustPublic pub) := by
  rw [trace_eq]
  exact BuilderFieldNormalization.trace_normalization _ _ _ words publicCorr

#print axioms run_exact
#print axioms trace_eq
#print axioms canonical_trace
end R1Z.PV_Src_ForestTrace
