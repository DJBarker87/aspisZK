import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFuel

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a
abbrev LoopState := (Array QM 7#usize) × Usize

def loopBody (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (state : LoopState) :
    Result (ControlFlow LoopState
      (pool_v1.pair_forest_copy_terminal.Selectors × Array QM 7#usize)) :=
  pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
    self state.1 state.2

private theorem body_done
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (sums : Array QM 7#usize) (block : Usize)
    (hge : 64 ≤ block.val) :
    loopBody self (sums, block) = .ok (.done (self, sums)) := by
  have h64 : (64#usize).val = 64 := rfl
  have hnotVal : ¬ block.val < 64 := by omega
  have hlen : Slice.len (Array.to_slice
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS) = 64#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice,
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS]
  unfold loopBody
  simp [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body,
    lift, hlen, hnotVal]

set_option backward.isDefEq.respectTransparency false in
theorem loop0_success_fuel
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (sums : Array QM 7#usize) (block : Usize) (fuel : Nat)
    (hspan : block.val + fuel = 64)
    (hself : CanonicalArray self.high) (hsums : CanonicalArray sums) :
    ∃ out : Array QM 7#usize,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0
        self sums block = .ok (self, out) ∧ CanonicalArray out := by
  induction fuel generalizing block sums with
  | zero =>
      have hblock : block.val = 64 := by omega
      have hbody := body_done self sums block (by omega)
      change pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
        self sums block = .ok (.done (self, sums)) at hbody
      refine ⟨sums, ?_, hsums⟩
      rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0,
        loop.eq_def]
      dsimp only
      rw [hbody]
  | succ fuel ih =>
      have hblock : block.val < 64 := by omega
      obtain ⟨coordinate, hcoordinate, added, updated, block1,
        hbody, hinc, hadd, haddCanonical, hupdatedCanonical, hset⟩ :=
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep.loop0_body_step
          self sums block hblock hself hsums
      change pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
        self sums block = .ok (.cont (updated, block1)) at hbody
      have hinc' : (block + 1#usize : Result Usize) = .ok block1 := by
        change UScalar.add block 1#usize = .ok block1
        exact hinc
      have haddSpec := UScalar.add_equiv block (1#usize)
      rw [hinc'] at haddSpec
      simp only [Result.ok.injEq] at haddSpec
      have hblock1 : block1.val = block.val + 1 := haddSpec.2.1
      have hspan1 : block1.val + fuel = 64 := by omega
      obtain ⟨out, hrun, hout⟩ := ih
        (sums := updated) (block := block1) (hspan := hspan1)
        (hsums := hupdatedCanonical)
      refine ⟨out, ?_, hout⟩
      rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0,
        loop.eq_def]
      dsimp only
      rw [hbody]
      exact hrun

#print axioms loop0_success_fuel
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFuel
