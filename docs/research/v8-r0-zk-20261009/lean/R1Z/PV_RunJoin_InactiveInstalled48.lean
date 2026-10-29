import R1Z.PV_RunJoin_InactiveRun48
import R1Z.PV_RunJoin_InactiveValue48
import R1Z.PV_RunJoin_ClaimFields48
import R1Z.ProverCommitGamma48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48
open ProverRwDictionaryTower (fromW)
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_InactiveValueCell48 (input)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j))
    (w : PV_RunJoin_WeightCarrier46.W) (hs : w.variant=.S2) :
    ∃ z : Raw,
      @prover.opening_inactive (types base) (selected base heap box ops) (input q) w=ok (fromW (source z)) ∧
      canonical z ∧ value z=PV_RunJoin_InactiveValue48.total q 1024 0 ∧
      (do let inactive ← @prover.opening_inactive (types base) (selected base heap box ops) (input q) w
          @aspis_core.field.wide_exact.WideExact.to_le_bytes (types base) (selected base heap box ops) inactive)=
        ok (PV_RunJoin_FlatBytes35.wire (fromW (source z))) := by
  obtain ⟨z,hz,hcz,hdz⟩ := PV_RunJoin_InactiveValue48.complete q hq
    (PV_RunJoin_WeightCarrier46.state w) 1024 0#usize (by decide)
    ProverCommitGamma48.zero ProverCommitGamma48.zero_canonical
  have actual := PV_RunJoin_InactiveRun48.complete base heap box ops (input q) w hs
  rw [ProverCommitGamma48.source_zero,hz] at actual
  change @prover.opening_inactive (types base) (selected base heap box ops) (input q) w=ok (fromW (source z)) at actual
  refine ⟨z,actual,hcz,?_,?_⟩
  · simpa only [ProverCommitGamma48.zero_value,zero_add,show (0#usize).val=0 from rfl] using hdz
  · rw [actual]
    simp only [bind_tc_ok]
    exact PV_RunJoin_ClaimFields48.serializer base heap box ops _
#print axioms complete
end R1Z.PV_RunJoin_InactiveInstalled48
