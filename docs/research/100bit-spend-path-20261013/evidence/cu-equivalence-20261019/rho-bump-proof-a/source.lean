import AspisR1RhoBump.Funs
import CuSavingsRhoAllocationBound
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoBump
open Aeneas Aeneas.Std Result AspisR1RhoBump

theorem source_success (start len pos size : Usize) (future : Nat)
    (hpos : pos ≠ 0#usize)
    (hfree : start.val+8+size.val+7+future ≤ pos.val) :
    ∃ out,source_alloc start len pos size = .ok (some out) ∧
      start.val+8+future ≤ out.val ∧ out.val+size.val ≤ pos.val ∧
      pos.val ≤ out.val+size.val+7 := by
  let sub := UScalar.saturating_sub pos size
  let out := UScalar.and sub (UScalar.not 7#usize)
  have hs : sub.val = pos.val-size.val := by rfl
  have hb := CuSavingsRhoAllocationBound.clear_low_three_bounds sub.bv
  change out.val ≤ sub.val ∧ sub.val ≤ out.val+7 at hb
  have hz : size.val ≤ pos.val := by omega
  have hsub : pos.val-size.val+size.val=pos.val := Nat.sub_add_cancel hz
  have hbound : start.val+8+future ≤ out.val := by omega
  have hsum : start.val+8 ≤ Usize.max := by have h:=pos.hmax;omega
  have hadd : start+8#usize = .ok (UScalar.ofNatCore (start.val+8) hsum) := by scalar_tac
  have hlt : ¬out < UScalar.ofNatCore (start.val+8) hsum := by
    change ¬out.val < start.val+8
    omega
  refine ⟨out,?_,hbound,by omega,by omega⟩
  unfold source_alloc
  simp only [hpos,if_false,bind_tc_ok]
  change (do
    let top ← start+8#usize
    if out < top then .ok none else .ok (some out)) = _
  rw [hadd]
  simp only [bind_tc_ok,hlt,if_false]

#print axioms source_success
end AspisR1.CuSavingsRhoBump
