import R1Z.PV_RunJoin_InactiveIndicator48
import R1Z.PV_RunJoin_Vector44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveValueCell48
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48
open ProverRwDictionaryTower (fromW toW native_w_roundtrip)
open PV_RunJoin_WeightMap46 (mapResult)

def input (q : Nat → Raw) : Slice ProverRwFull.aspis_core.field.wide_exact.WideExact :=
  Array.to_slice (ProverCommitArray49.array 1024#usize (fun j => fromW (source (q j))))

theorem read (q : Nat → Raw) (j : Usize) (hj : j.val<1024) :
    mapResult toW (Slice.index_usize (input q) j)=ok (source (q j.val)) := by
  rw [input,PV_RunJoin_Vector44.read 1024#usize _ j hj]
  change ok (toW (fromW (source (q j.val))))=_
  rw [native_w_roundtrip]

attribute [local irreducible] source value

theorem complete (q : Nat → Raw) (hq : ∀ j,j<1024 → canonical (q j))
    (state : ProverCommitWeightsStorage53.State) (s : Raw) (hs : canonical s)
    (row : Usize) (hr : row.val<1024) :
    ∃ z : Raw, PV_RunJoin_InactiveCell48.step (input q) state (source s) row=ok (source z) ∧
      canonical z ∧ value z=value s+value (q row.val)*PV_RunJoin_InactiveIndicator48.mask row.val := by
  obtain ⟨hraw,hcanon,hvalue⟩ := ProverCommitInactiveOutput49.exact_result row hr
  obtain ⟨product,hp,hcp,hdp⟩ := ProverCommitWideQM31Scalar49.value_exact
    (q row.val) (ProverCommitInactiveModel49.raw row) (hq row.val hr)
  obtain ⟨z,hz,hcz,hdz⟩ := add_exact s product hs hcp
  refine ⟨z,?_,hcz,?_⟩
  · simp only [PV_RunJoin_InactiveCell48.step,read q row hr,bind_tc_ok,
      ProverCommitWeightsStorage53.raw_zero,hraw,hp,hz]
  · rw [hdz,hdp,PV_RunJoin_InactiveIndicator48.complete row hr]
#print axioms read
#print axioms complete
end R1Z.PV_RunJoin_InactiveValueCell48
