import PV_B3Q_LoopGuards
import PV_B3Q_RangeIndexSource
namespace PV_B3Q_CallerLayouts
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
/-- Every deployed unoptimized add_preweighted call: (offset, array length).
The scalars array has TWO entries, so the final call occupies positions 92,93. -/
def layouts : List (Nat × Nat) :=
 [(0,16),(16,16),(32,17),(49,33),(82,2),(0,12),(84,8),(92,2)]
theorem layouts_safe : layouts.all (fun p => decide (0 < p.2 ∧ p.1+p.2 ≤ 96)) = true := by decide

theorem layout_member (start count : Nat) (member : (start,count) ∈ layouts) :
 0 < count ∧ start+count ≤ 96 := by
 have h := List.all_eq_true.mp layouts_safe (start,count) member
 exact of_decide_eq_true h

theorem preweighted_caller (start count group slot : Nat)
    (member : (start,count) ∈ layouts)
    (range : group ≤ (start+count-1)/4) (lane : slot < 4)
    (inside : start ≤ 4*group+slot ∧ 4*group+slot < start+count) :
 group < 24 ∧ slot < 4 ∧ 4*group+slot-start < count :=
 preweighted_source start count group slot (layout_member start count member) range lane inside

def highRanges : List (Nat × Nat) := [(0,57),(4,25),(33,57),(57,63)]
theorem high_ranges_safe : highRanges.all (fun p => decide (p.1 ≤ p.2 ∧ p.2 ≤ 64)) = true := by decide

theorem high_range_read (start finish block : Nat) (member : (start,finish) ∈ highRanges)
    (sourceGuard : start ≤ block ∧ block < finish) : block < 64 := by
 have h := List.all_eq_true.mp high_ranges_safe (start,finish) member
 have bounds : start ≤ finish ∧ finish ≤ 64 := of_decide_eq_true h
 omega

def internalRows : List Nat := [2,3,4,5,6,7,8]
theorem internal_rows_safe : internalRows.all
 (fun row => decide (2 ≤ row ∧ row < 16 ∧ 2*(row-2)+1 < 14)) = true := by decide

theorem internal_row_reads (row : Nat) (member : row ∈ internalRows) :
 row < 16 ∧ 2*(row-2) < 14 ∧ 2*(row-2)+1 < 14 := by
 have h := List.all_eq_true.mp internal_rows_safe row member
 have b : 2 ≤ row ∧ row < 16 ∧ 2*(row-2)+1 < 14 := of_decide_eq_true h
 omega

theorem append_selector_rows (level carry : Nat) (loop : level < 20) (branch : carry < 20) :
 (34+level)*16 < 1024 ∧ (34+level)*16+12 < 1024 ∧
 (33+carry)*16+11 < 1024 := by omega

theorem digest_source_window (start lane : Nat) (caller : start=0 ∨ start=8)
    (loop : lane < 8) : start+lane < 16 := by omega
#print axioms layouts_safe
#print axioms layout_member
#print axioms preweighted_caller
#print axioms high_ranges_safe
#print axioms high_range_read
#print axioms internal_rows_safe
#print axioms internal_row_reads
#print axioms append_selector_rows
#print axioms digest_source_window
end PV_B3Q_CallerLayouts
