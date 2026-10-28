import R1Z.ProverRw21CallerFoundation
import R1Z.PV_RunJoin_SelectedCoordinates32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Foundation34
open Aeneas Aeneas.Std Result PV_RunJoin_HonestIdentification26
open ProverRw21CallerFoundation
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Every original compiled semantic column has the exact decoder length.
The fact is derived from successful compilation, not from a cached payload
shape or from totalising the decoder. -/
theorem lengths (i : Honest (K := K)) :
    ∀ c, c < 16 → (i.val.compiled.semantic_c1.c1.val[c]!).val.length = 1024 := by
  obtain ⟨banks,hb,hc⟩ := PV_RunJoin_UniversalBuild22.returned_bank i.val (success i)
  obtain ⟨out,ho,hl,_⟩ := PV_Src_ForestTrace.run_exact
    (PV_RunJoin_UniversalBuild22.records i.val).w
    (PV_RunJoin_UniversalBuild22.records i.val).p
  have he : out = banks.merged := Result.ok.inj
    (ho.symm.trans (PV_Src_ForestBanks.merged_run _ _ hb))
  rw [he] at hl
  rw [hc]
  exact hl

/-- The actual nominal foundation is in the successful decoder domain. -/
theorem shape (i : Honest (K := K)) :
    Shape (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) := by
  intro lane
  rw [column_length]
  have h := lengths i lane.val lane.isLt
  have inside : lane.val < i.val.compiled.semantic_c1.c1.val.length := by
    rw [i.val.compiled.semantic_c1.c1.property]
    exact lane.isLt
  simpa only [rawColumn,PV_RunJoin_NominalLeafData.foundation,getElem!_pos i.val.compiled.semantic_c1.c1.val lane.val inside] using h

/-- Full decoder success for the ORIGINAL semantic foundation; no new
prepared payload is chosen and no source/model equation is assumed. -/
theorem decoded (i : Honest (K := K)) :
    ∃ values, decode (PV_RunJoin_NominalLeafData.foundation i.val.compiled.semantic_c1) = some values :=
  (success_iff _).mpr (shape i)

#print axioms lengths
#print axioms shape
#print axioms decoded
end R1Z.PV_RunJoin_Foundation34
