import XRz_FinishLoop
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_FillCells
open XRx_FinishStep XRz_FinishBody XRz_FinishLoop
theorem length (f : Nat → Q) (n i : Nat) (t : It) :
 (fill f i n t).iter.slice.length=t.iter.slice.length := by
 induction n generalizing i with
 | zero => rfl
 | succ n ih =>
  change ((fill f (i+1) n t).iter.slice.setAtNat i (f i)).length=_
  rw [Slice.setAtNat_length,ih]

theorem cell (f : Nat → Q) (n i : Nat) (t : It) (j : Nat) (bound : j<t.iter.slice.length) :
 (fill f i n t).iter.slice.val[j]? = 
 if i ≤ j ∧ j < i + n then some (f j) else t.iter.slice.val[j]? := by
 induction n generalizing i with
 | zero => simp only [fill]; rw [if_neg (by omega)]; rfl
 | succ n ih =>
  change ((fill f (i+1) n t).iter.slice.val.set i (f i))[j]? = _
  by_cases same : i=j
  · subst j
    have hb : i < (fill f (i+1) n t).iter.slice.length := by rw [length]; exact bound
    rw [List.getElem?_set_self hb,if_pos (by omega)]
  · rw [List.getElem?_set_ne same,ih]
    have eq : (i+1 ≤ j ∧ j < i+1+n) ↔ (i ≤ j ∧ j < i+(n+1)) := by omega
    by_cases h : i+1 ≤ j ∧ j < i+1+n
    · rw [if_pos h,if_pos (eq.mp h)]
    · rw [if_neg h,if_neg (fun x => h (eq.mpr x))]
#print axioms length
#print axioms cell
end XRz_FillCells
