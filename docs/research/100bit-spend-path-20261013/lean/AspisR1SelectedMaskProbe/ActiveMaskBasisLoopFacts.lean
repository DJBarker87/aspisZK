import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof
import CopyActiveMaskBasisRegroup

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts

def matchCoordinate (mask : Std.U16) : Result Usize :=
  match mask with
  | 6144#uscalar => ok 0#usize
  | 6145#uscalar => ok 1#usize
  | 4097#uscalar => ok 2#usize
  | 2048#uscalar => ok 3#usize
  | 2049#uscalar => ok 4#usize
  | 26214#uscalar => ok 5#usize
  | 1749#uscalar => ok 6#usize
  | _ => fail Error.arrayOutOfBounds

def modelCoordinate (mask : Nat) : Usize :=
  match mask with
  | 6144 => 0#usize
  | 6145 => 1#usize
  | 4097 => 2#usize
  | 2048 => 3#usize
  | 2049 => 4#usize
  | 26214 => 5#usize
  | 1749 => 6#usize
  | _ => 0#usize

theorem source_mask_member (i : Fin 64) :
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 6144#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 6145#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 4097#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 2048#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 2049#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 26214#u16 ∨
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i = 1749#u16 := by
  have hm := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.source_mask_table i
  have hmem : R0P.copyActiveRowMasks i = 6144 ∨
      R0P.copyActiveRowMasks i = 6145 ∨ R0P.copyActiveRowMasks i = 4097 ∨
      R0P.copyActiveRowMasks i = 2048 ∨ R0P.copyActiveRowMasks i = 2049 ∨
      R0P.copyActiveRowMasks i = 26214 ∨ R0P.copyActiveRowMasks i = 1749 := by
    fin_cases i <;> decide
  rcases hmem with h | h | h | h | h | h | h
  · left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; right; left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; right; right; left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; right; right; right; left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; right; right; right; right; left
    apply UScalar.eq_of_val_eq
    simpa [hm] using h
  · right; right; right; right; right; right
    apply UScalar.eq_of_val_eq
    simpa [hm] using h

theorem source_match_coordinate (i : Fin 64) :
    matchCoordinate (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i) =
      .ok (modelCoordinate (R0P.copyActiveRowMasks i)) := by
  rcases source_mask_member i with h | h | h | h | h | h | h
  all_goals
    have hm := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.source_mask_table i
    have hcopy : R0P.copyActiveRowMasks i =
        (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i).val := hm.symm
    have hnum := congrArg UScalar.val h
    rw [hnum] at hcopy
    rw [h]
    rw [hcopy]
    rfl

theorem model_coordinate_agrees (i : Fin 64) :
    (modelCoordinate (R0P.copyActiveRowMasks i)).val =
      (R0P.activeMaskCoordinate (R0P.copyActiveRowMasks i)).val := by
  rcases source_mask_member i with h | h | h | h | h | h | h
  all_goals
    have hm := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.source_mask_table i
    have hcopy : R0P.copyActiveRowMasks i =
        (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask i).val := hm.symm
    have hnum := congrArg UScalar.val h
    rw [hnum] at hcopy
    rw [hcopy]
    rfl

#print axioms source_mask_member
#print axioms source_match_coordinate
#print axioms model_coordinate_agrees
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts
