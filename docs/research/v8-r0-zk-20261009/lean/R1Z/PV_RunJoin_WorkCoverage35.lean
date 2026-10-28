import R1Z.PV_RunJoin_WorkRange35
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WorkCoverage35
open PV_RunJoin_WorkRange35

/-- Source-order flattening of the sixteen adjacent callback-index ranges. -/
def indices (n : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => indices n k ++ List.range' (start n k) (width n k)

theorem prefix (n k : Nat) : indices n k=List.range' 0 (start n k) := by
  induction k with
  | zero => rw [indices,PV_RunJoin_WorkRange35.zero];rfl
  | succ k ih =>
    rw [indices,ih,PV_RunJoin_WorkRange35.next]
    simpa only [Nat.zero_add] using
      (List.range'_append 0 (start n k) (width n k)).symm

theorem complete (n : Nat) : indices n 16=List.range n := by
  rw [prefix,end_all]
  rfl

theorem count (n : Nat) : (indices n 16).length=n := by rw [complete,List.length_range]

theorem coverage (n i : Nat) : i∈indices n 16 ↔ i<n := by rw [complete,List.mem_range]

theorem no_duplicates (n : Nat) : (indices n 16).Nodup := by rw [complete];exact List.nodup_range

#print axioms prefix
#print axioms complete
#print axioms count
#print axioms coverage
#print axioms no_duplicates
end R1Z.PV_RunJoin_WorkCoverage35
