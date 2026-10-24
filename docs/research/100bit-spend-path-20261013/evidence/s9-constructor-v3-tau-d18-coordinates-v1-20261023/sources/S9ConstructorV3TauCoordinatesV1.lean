import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import R1D18PointWeights
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3TauCoordinatesV1

/-- Symbolic bounded subtraction, reusing the retained reverse-range
subtraction proof pattern instead of reducing machine-word moduli. -/
theorem wrapping_sub_natural (n m : Usize) (h : m.val ≤ n.val) :
    (Usize.wrapping_sub n m).val = n.val - m.val := by
  rw [Usize.wrapping_sub_val_eq]
  have hn : n.val < UScalar.size .Usize := by simpa only [UScalar.size] using n.hBounds
  have hm : m.val < UScalar.size .Usize := by simpa only [UScalar.size] using m.hBounds
  have he : n.val + (UScalar.size .Usize - m.val) =
      (n.val-m.val) + UScalar.size .Usize := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Symbolic product bound, avoiding reduction of an opaque machine modulus. -/
theorem wrapping_mul_two_natural (tau : Usize) (ht : tau.val≤4) :
    (Usize.wrapping_mul 2#usize tau).val = 2*tau.val := by
  have h8 : (8#usize).val = 8 := rfl
  have hsize : 8 < UScalar.size .Usize := by
    simpa only [UScalar.size,h8] using (8#usize).hBounds
  rw [Usize.wrapping_mul_val_eq]
  change (2*tau.val) % UScalar.size .Usize = 2*tau.val
  exact Nat.mod_eq_of_lt (by omega)

/-- Literal source TAU and both wrapping source coordinates equal the
existing D18 permutation/indices. Only the five table entries are reduced. -/
theorem tau_read_coordinates (d tau : Usize) (hd : d.val < 5)
    (hread : Array.index_usize AspisR1S9ActualWeightsNewBoxNewV3.TAU d = .ok tau) :
    tau.val = (AspisR1.d18Tau ⟨d.val,hd⟩).val ∧
    (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize tau)).val =
      9 - 2*(AspisR1.d18Tau ⟨d.val,hd⟩).val ∧
    (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize tau)).val =
      8 - 2*(AspisR1.d18Tau ⟨d.val,hd⟩).val := by
  have hcases : d.val=0 ∨ d.val=1 ∨ d.val=2 ∨ d.val=3 ∨ d.val=4 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · have he : d = 0#usize := UScalar.eq_of_val_eq h0
    subst d
    unfold AspisR1S9ActualWeightsNewBoxNewV3.TAU Array.index_usize at hread
    change Result.ok (3#usize) = Result.ok tau at hread
    have ht : (3#usize) = tau := Result.ok.inj hread
    subst tau
    have hm := wrapping_mul_two_natural (3#usize) (by decide)
    refine ⟨rfl,?_,?_⟩
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
  · have he : d = 1#usize := UScalar.eq_of_val_eq h1
    subst d
    unfold AspisR1S9ActualWeightsNewBoxNewV3.TAU Array.index_usize at hread
    change Result.ok (4#usize) = Result.ok tau at hread
    have ht : (4#usize) = tau := Result.ok.inj hread
    subst tau
    have hm := wrapping_mul_two_natural (4#usize) (by decide)
    refine ⟨rfl,?_,?_⟩
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
  · have he : d = 2#usize := UScalar.eq_of_val_eq h2
    subst d
    unfold AspisR1S9ActualWeightsNewBoxNewV3.TAU Array.index_usize at hread
    change Result.ok (2#usize) = Result.ok tau at hread
    have ht : (2#usize) = tau := Result.ok.inj hread
    subst tau
    have hm := wrapping_mul_two_natural (2#usize) (by decide)
    refine ⟨rfl,?_,?_⟩
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
  · have he : d = 3#usize := UScalar.eq_of_val_eq h3
    subst d
    unfold AspisR1S9ActualWeightsNewBoxNewV3.TAU Array.index_usize at hread
    change Result.ok (0#usize) = Result.ok tau at hread
    have ht : (0#usize) = tau := Result.ok.inj hread
    subst tau
    have hm := wrapping_mul_two_natural (0#usize) (by decide)
    refine ⟨rfl,?_,?_⟩
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
  · have he : d = 4#usize := UScalar.eq_of_val_eq h4
    subst d
    unfold AspisR1S9ActualWeightsNewBoxNewV3.TAU Array.index_usize at hread
    change Result.ok (1#usize) = Result.ok tau at hread
    have ht : (1#usize) = tau := Result.ok.inj hread
    subst tau
    have hm := wrapping_mul_two_natural (1#usize) (by decide)
    refine ⟨rfl,?_,?_⟩
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl
    · rw [wrapping_sub_natural _ _ (by rw [hm]; decide),hm]
      rfl

#print axioms wrapping_sub_natural
#print axioms wrapping_mul_two_natural
#print axioms tau_read_coordinates
end AspisR1S9ConstructorV3TauCoordinatesV1
