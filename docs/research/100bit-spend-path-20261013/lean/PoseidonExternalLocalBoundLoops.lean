import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalBoundSource
import RawPoseidonExternalRowReads
import Aeneas.Std.WP

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result WP
namespace AspisR1.PoseidonExternalLocalBoundLoops

open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalBoundSource
open AspisR1.RawPoseidonExternalRowReads

abbrev LocalRows := Array (Array U64 4#usize) 4#usize

private theorem inner_loop_success_fuel (local1 : LocalRows) (bounded : Bool)
    (output limb : Usize) (fuel : Nat)
    (houtput : output.val < 4) (hspan : limb.val + fuel = 4) :
    ∃ result : Bool,
      state_only_poseidon.external_local_packed_raw_loop0_loop0
        local1 bounded output limb = .ok result := by
  induction fuel generalizing limb bounded with
  | zero =>
      have hstop : ¬ limb < 4#usize := by scalar_tac
      refine ⟨bounded, ?_⟩
      rw [state_only_poseidon.external_local_packed_raw_loop0_loop0.eq_def,
        if_neg hstop]
  | succ fuel ih =>
      have hlimb : limb.val < 4 := by omega
      have hrow := array_index_usize_ok local1 output (by simpa using houtput)
      let row : Array U64 4#usize := local1.val[output.val]'(by
        simpa [local1.property] using houtput)
      have hrow' : Array.index_usize local1 output = .ok row := by
        simpa [row] using hrow
      have hcell := array_index_usize_ok row limb (by simpa using hlimb)
      obtain ⟨bound, hbound, _⟩ := external_local_limb_bound_success
      let bounded1 : Bool := bounded && decide
        ((row.val[limb.val]'(by simpa [row.property] using hlimb)).val < bound.val)
      have hincSpec : (limb + 1#usize : Result Usize) ⦃z => z.val = limb.val + 1⦄ := by
        apply UScalar.add_spec
        have hmax := Usize.cMax_bound_concrete.1
        scalar_tac
      obtain ⟨limb1, hinc, hincVal⟩ := WP.spec_imp_exists hincSpec
      have hspan' : limb1.val + fuel = 4 := by rw [hincVal]; omega
      obtain ⟨bounded2, hrec⟩ := ih (bounded := bounded1) (limb := limb1) hspan'
      have hfour : (4#usize).val = 4 := by scalar_tac
      rw [state_only_poseidon.external_local_packed_raw_loop0_loop0.eq_def,
        if_pos (by scalar_tac)]
      simp only [UScalar.lt_equiv, hfour, hlimb, hrow', bind_tc_ok,
        hcell, bind_tc_ok, hbound, bind_tc_ok, bounded1, hinc, bind_tc_ok, hrec]
      exact ⟨bounded2, rfl⟩

theorem ignored_bound_loop_success (local1 : LocalRows) (bounded : Bool)
    (output : Usize) (fuel : Nat)
    (hspan : output.val + fuel = 4) :
    state_only_poseidon.external_local_packed_raw_loop0 local1 bounded output = .ok () := by
  induction fuel generalizing output bounded with
  | zero =>
      have hstop : ¬ output < 4#usize := by scalar_tac
      rw [state_only_poseidon.external_local_packed_raw_loop0.eq_def, if_neg hstop]
  | succ fuel ih =>
      have houtput : output.val < 4 := by omega
      obtain ⟨bounded1, hinner⟩ := inner_loop_success_fuel local1 bounded output 0#usize 4
        houtput (by simp)
      have hincSpec : (output + 1#usize : Result Usize) ⦃z => z.val = output.val + 1⦄ := by
        apply UScalar.add_spec
        have hmax := Usize.cMax_bound_concrete.1
        scalar_tac
      obtain ⟨output1, hinc, hincVal⟩ := WP.spec_imp_exists hincSpec
      have hspan' : output1.val + fuel = 4 := by rw [hincVal]; omega
      have hfour : (4#usize).val = 4 := by scalar_tac
      rw [state_only_poseidon.external_local_packed_raw_loop0.eq_def,
        if_pos (by scalar_tac)]
      simp only [UScalar.lt_equiv, hfour, houtput, hinner, bind_tc_ok,
        hinc, bind_tc_ok]
      exact ih (bounded := bounded1) (output := output1) hspan'

/-- The generated nested bound scan succeeds for every fixed-shape row table.
Its accumulated boolean is deliberately not constrained: the source discards
it and returns Unit. -/
theorem ignored_bound_scan_success (local1 : LocalRows) :
    state_only_poseidon.external_local_packed_raw_loop0 local1 true 0#usize = .ok () :=
  ignored_bound_loop_success local1 true 0#usize 4 (by decide)

#print axioms inner_loop_success_fuel
#print axioms ignored_bound_loop_success
#print axioms ignored_bound_scan_success
end AspisR1.PoseidonExternalLocalBoundLoops
