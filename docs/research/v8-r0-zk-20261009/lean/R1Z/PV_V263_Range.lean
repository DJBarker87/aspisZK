import R1Z.PV_RunJoin_WorkCoverage35
/-! Structural range-helper binding side conditions. These are arithmetic
facts, not worker scheduling, allocation, TLS or termination laws. -/
set_option autoImplicit false
namespace R1Z.PV_V263_Range
open Aeneas Aeneas.Std PV_RunJoin_WorkRange35

theorem intermediates (n k : Nat) (hk : k < 16) :
    (n/16)*k ≤ n ∧ start n k ≤ n ∧
    start n k + n/16 ≤ n ∧ start n k + width n k ≤ n := by
  have h := bounded n k hk
  have hw : n/16 ≤ width n k := by unfold width; omega
  have hs : (n/16)*k ≤ start n k := by unfold start; omega
  omega

/-- Every addition/multiplication in range has a non-overflowing natural
value. The only assertion is discharged by the worker-index bound. -/
theorem usize_safe (n : Usize) (k : Nat) (hk : k < 16) :
    (n.val/16)*k ≤ Usize.max ∧ start n.val k ≤ Usize.max ∧
    start n.val k + n.val/16 ≤ Usize.max ∧
    start n.val k + width n.val k ≤ Usize.max := by
  have h := intermediates n.val k hk
  have hn := n.hmax
  omega

/-- ordered_families(16,...) partitions family indices, separately from the
original item-count partition. Its sixteenth-family end is exactly 16. -/
theorem outer (k : Nat) (hk : k < 16) :
    start 16 k = k ∧ width 16 k = 1 := by
  simp only [start,width]
  simp

/-- No numerical evaluation of the reached 14336-cell case is needed. -/
theorem coverage (n : Nat) : PV_RunJoin_WorkCoverage35.indices n 16 = List.range n :=
  PV_RunJoin_WorkCoverage35.complete n

#print axioms intermediates
#print axioms usize_safe
#print axioms outer
#print axioms coverage
end R1Z.PV_V263_Range
