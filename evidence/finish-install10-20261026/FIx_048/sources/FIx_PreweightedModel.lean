import FIx_PreweightedLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedModel
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)

theorem value {N : Usize} (a : Array NQ N) (start n group : Nat)
    (old : Fin (24#usize).val → K) (j : Fin (24#usize).val) :
    FIx_PreweightedLoop.model a start n group old j=
      old j+(if group≤j.val ∧ j.val<group+n then FIx_PreweightedGroup.increment a start j.val else 0) := by
  induction n generalizing group old with
  | zero =>
    simp only [FIx_PreweightedLoop.model,Nat.add_zero,
      if_neg (show ¬(group≤j.val ∧ j.val<group) by omega),add_zero]
  | succ n ih =>
    rw [FIx_PreweightedLoop.model,ih]
    unfold FIx_PreweightedGroup.step
    by_cases he : j.val=group
    · rw [if_pos he,if_neg (show ¬(group+1≤j.val ∧ j.val<group+1+n) by omega),add_zero,
        if_pos (show group≤j.val ∧ j.val<group+(n+1) by omega)]
      rw [he]
    · rw [if_neg he]
      have h : (group+1≤j.val ∧ j.val<group+1+n) ↔ (group≤j.val ∧ j.val<group+(n+1)) := by omega
      by_cases hi : group≤j.val ∧ j.val<group+(n+1)
      · rw [if_pos hi,if_pos (h.mpr hi)]
      · rw [if_neg hi,if_neg (fun hh=>hi (h.mp hh))]

#print axioms value
end AspisR1.FIx_PreweightedModel
end
