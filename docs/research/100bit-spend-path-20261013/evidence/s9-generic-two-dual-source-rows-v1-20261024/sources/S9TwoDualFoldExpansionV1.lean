import RoundPairing
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
noncomputable section
namespace AspisR1S9TwoDualFoldExpansionV1
open AspisR1
open scoped BigOperators
variable {K : Type} [Field K]

/-- Same fibre-major source order after two radix-four layers. -/
def blockIndex {n : Nat} (d : Fin n) (s : Fin 16) : Fin (4*(4*n)) :=
  ⟨16*d.val+s.val,by have hd:=d.isLt;have hs:=s.isLt;omega⟩

theorem child_child_block {n : Nat} (d : Fin n) (t1 t0 : Fin 4) :
    childIndex (childIndex d t1) t0=blockIndex d (finProdFinEquiv (t1,t0)) := by
  apply Fin.ext
  change 4*(4*d.val+t1.val)+t0.val=16*d.val+(t0.val+4*t1.val)
  omega

theorem low16_mod (t1 t0 : Fin 4) :
    (finProdFinEquiv (t1,t0)).val%4=t0.val := by
  change (t0.val+4*t1.val)%4=t0.val
  have h0:=t0.isLt
  omega

theorem low16_div (t1 t0 : Fin 4) :
    (finProdFinEquiv (t1,t0)).val/4=t1.val := by
  change (t0.val+4*t1.val)/4=t1.val
  have h0:=t0.isLt
  omega

theorem sum_low16_reindex (term : Fin 16 → K) :
    (∑t1 : Fin 4,∑t0 : Fin 4,term (finProdFinEquiv (t1,t0)))=∑s : Fin 16,term s := by
  symm
  rw [←(finProdFinEquiv (m:=4) (n:=4)).sum_comp,Fintype.sum_prod_type]

/-- Generic opaque-field expansion for ANY raw row. No tensor/product-row
premise and no enumeration of a source vector or field recurrence. -/
theorem two_dual_fold_double_sum {n : Nat} (a0 a1 : K)
    (w : Fin (4*(4*n)) → K) (d : Fin n) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 w) d=
      ∑t1 : Fin 4,∑t0 : Fin 4,
        w (childIndex (childIndex d t1) t0)*RoundPairing.quarter^2*
          a0^((4-t0.val)%4)*a1^((4-t1.val)%4) := by
  simp only [RoundPairing.dualFold,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t1 _
  apply Finset.sum_congr rfl
  intro t0 _
  ring

theorem two_dual_fold_block_sum {n : Nat} (a0 a1 : K)
    (w : Fin (4*(4*n)) → K) (d : Fin n) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 w) d=
      ∑s : Fin 16,w (blockIndex d s)*RoundPairing.quarter^2*
        a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4) := by
  rw [two_dual_fold_double_sum,←sum_low16_reindex]
  apply Finset.sum_congr rfl
  intro t1 _
  apply Finset.sum_congr rfl
  intro t0 _
  rw [child_child_block,low16_mod,low16_div]

/-- Requested1024→64 instance, still on arbitrary uninterpreted row values. -/
theorem two_dual_fold_1024_64 (a0 a1 : K) (w : Fin 1024 → K) (d : Fin 64) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 w) d=
      ∑s : Fin 16,w (blockIndex d s)*RoundPairing.quarter^2*
        a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4) :=
  two_dual_fold_block_sum (n:=64) a0 a1 w d

#print axioms child_child_block
#print axioms low16_mod
#print axioms low16_div
#print axioms sum_low16_reindex
#print axioms two_dual_fold_double_sum
#print axioms two_dual_fold_block_sum
#print axioms two_dual_fold_1024_64
end AspisR1S9TwoDualFoldExpansionV1
end
