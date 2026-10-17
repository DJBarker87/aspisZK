import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFuel

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel

abbrev QM := field.QM31
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a

def cell {n : Usize} (a : Array QM n) (j : Fin n.val) : QM :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

private theorem body_done
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (sums : Array QM 7#usize) (block : Usize)
    (hge : 64 ≤ block.val) :
    pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
      self sums block = .ok (.done (self, sums)) := by
  have hnotVal : ¬ block.val < 64 := by omega
  have hlen : Slice.len (Array.to_slice
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS) = 64#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice,
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS]
  simp [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body,
    lift, hlen, hnotVal]

theorem loop0_success_fuel_prefix
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (sums : Array QM 7#usize) (block : Usize) (fuel : Nat)
    (hspan : block.val + fuel = 64)
    (hself : CanonicalArray self.high) (hsums : CanonicalArray sums)
    (hinv : ∀ j : Fin 7,
      AspisR1.ExtractedMaskQM31Exact.decode (cell sums j) =
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue self j block.val) :
    ∃ out : Array QM 7#usize,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0
        self sums block = .ok (self, out) ∧ CanonicalArray out ∧
      (∀ j : Fin 7,
        AspisR1.ExtractedMaskQM31Exact.decode (cell out j) =
          AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue self j 64) := by
  induction fuel generalizing block sums with
  | zero =>
      have hblock : block.val = 64 := by omega
      have hbody := body_done self sums block (by omega)
      change pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
        self sums block = .ok (.done (self, sums)) at hbody
      refine ⟨sums, ?_, hsums, ?_⟩
      · rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0,
          loop.eq_def]
        dsimp only
        rw [hbody]
      · intro j
        simpa [hblock] using hinv j
  | succ fuel ih =>
      have hblock : block.val < 64 := by omega
      obtain ⟨coordinate, hcoordinate, updated, block1, hbody, hinc,
        hupdatedCanonical, hinv1⟩ :=
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.loop0_body_step_prefix
          self sums block hblock hself hsums hinv
      have hinc' : (block + 1#usize : Result Usize) = .ok block1 := by
        change UScalar.add block 1#usize = .ok block1
        exact hinc
      have haddSpec := UScalar.add_equiv block (1#usize)
      rw [hinc'] at haddSpec
      simp only [Result.ok.injEq] at haddSpec
      have hblock1 : block1.val = block.val + 1 := haddSpec.2.1
      have hspan1 : block1.val + fuel = 64 := by omega
      obtain ⟨out, hrun, houtCanonical, houtInv⟩ :=
        ih (sums := updated) (block := block1) (hspan := hspan1)
          (hsums := hupdatedCanonical) (hinv := by
            intro j
            simpa [hblock1, cell,
              AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.cell] using hinv1 j)
      refine ⟨out, ?_, houtCanonical, houtInv⟩
      rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0,
        loop.eq_def]
      dsimp only
      rw [hbody]
      exact hrun

#print axioms loop0_success_fuel_prefix
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel
