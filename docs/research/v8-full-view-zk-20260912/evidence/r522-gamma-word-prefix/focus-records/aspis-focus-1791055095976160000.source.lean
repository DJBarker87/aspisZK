import AspisR515SharedGamma.SharedGammaDots
import AspisV8R19.R158WordBounds

set_option autoImplicit false
namespace AspisV8R19.R522GammaWordPrefix
open Aeneas Aeneas.Std Result
open AspisV8.AffinePrimal AspisV8.SharedGammaDots

/-- The actual fixed-width primitives agree with the reused natural prefix
arithmetic. The complete selected array loop remains a separate obligation. -/
theorem wrapping_mac_prefix (n : Nat) (s a b : U64) (hn : n < 4)
    (hs : s.val ≤ n*m^2) (ha : a.val ≤ m) (hb : b.val ≤ m) :
    (U64.wrapping_add s (U64.wrapping_mul a b)).val = s.val+a.val*b.val ∧
    (U64.wrapping_add s (U64.wrapping_mul a b)).val ≤ (n+1)*m^2 := by
  obtain ⟨hbound, hexact⟩ := four_product_prefix n s.val a.val b.val hn hs ha hb
  have he : (U64.wrapping_add s (U64.wrapping_mul a b)).val = s.val+a.val*b.val := by
    rw [U64.wrapping_add_val_eq, U64.wrapping_mul_val_eq]
    simpa only [UScalar.size, UScalarTy.numBits, word] using hexact
  exact ⟨he, by rw [he]; exact hbound⟩

theorem checked_mac_prefix (n : Nat) (s a b : U64) (hn : n < 4)
    (hs : s.val ≤ n*m^2) (ha : a.val ≤ m) (hb : b.val ≤ m) :
    (do let product ← (a*b : Result U64); (s+product : Result U64)) =
        .ok (U64.wrapping_add s (U64.wrapping_mul a b)) := by
  have hab : a.val*b.val ≤ m^2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hb
  have hcap : (n+1)*m^2 ≤ 4*m^2 := Nat.mul_le_mul_right _ (by omega)
  have hword : 4*m^2 ≤ U64.max := by norm_num [m,p,U64.max,U64.numBits]
  have hmul : a.val*b.val ≤ U64.max := by omega
  have hsum := (wrapping_mac_prefix n s a b hn hs ha hb).2
  have hprod : (U64.wrapping_mul a b).val = a.val*b.val := by
    rw [U64.wrapping_mul_val_eq]
    apply Nat.mod_eq_of_lt
    simp only [UScalar.size,UScalarTy.numBits]
    norm_num [U64.max,U64.numBits] at hmul
    omega
  have hadd : s.val+(U64.wrapping_mul a b).val ≤ U64.max := by
    rw [hprod]
    have hbnd := (four_product_prefix n s.val a.val b.val hn hs ha hb).1
    omega
  rw [R158WordBounds.checked_mul_u64_eq_wrapping a b hmul]
  simp only [bind_tc_ok]
  exact R158WordBounds.checked_add_u64_eq_wrapping s _ hadd

#print axioms wrapping_mac_prefix
#print axioms checked_mac_prefix
end AspisV8R19.R522GammaWordPrefix
