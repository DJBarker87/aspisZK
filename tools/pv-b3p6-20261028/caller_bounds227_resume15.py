from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Caller15227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''
s='import PV_B3P_Operations12227\n'+h+'''
/-- The only reachable dot call uses two seven-element arrays. Its original
length assertion therefore holds and its <=4 fast branch is not taken. -/
theorem dot7_source_entry15 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) :
    weights.val.length = values.val.length ∧ ¬ weights.val.length ≤ 4 := by
  rw [weights.property,values.property]
  decide

theorem dot7_block_indices15 (start index : Nat) (block : start = 0 ∨ start = 4)
    (member : start ≤ index ∧ index < min (start+4) 7) :
    index < 7 ∧ index-start < 4 := by omega

/-- The two source chunks preserve term order and do not pad the final block. -/
theorem dot7_ordered_partition15 : List.range' 0 4 ++ List.range' 4 3 = List.range' 0 7 := by
  decide
#print axioms dot7_source_entry15
#print axioms dot7_block_indices15
#print axioms dot7_ordered_partition15
end PV_B3P_Caller15227
''';(L/'PV_B3P_DotCallerBounds15227.lean').write_text(s)
s='import PV_B3P_Operations12227\nimport PV_B3P_ReverseRange14227\n'+h+'''
/-- Both actual selector-expansion calls use a complete point slice. -/
theorem expand_point_slices15 (point : Array aspis_core.field.QM31 10#usize) :
    (point.val.take 6).length = 6 ∧ (point.val.drop 6).length = 4 := by
  simp only [List.length_take,List.length_drop,point.property]
  decide

theorem expand_two_write_bounds15 (index len capacity : Nat)
    (source_bound : index < len) (space : 2*len ≤ capacity) :
    2*index < capacity ∧ 2*index+1 < capacity := by omega

/-- A decreasing source index reads the parent before it overwrites either
child. The two children are distinct; no next smaller parent is overwritten. -/
theorem expand_reverse_frame15 (index smaller : Nat) (next : smaller < index) :
    smaller ≠ 2*index ∧ smaller ≠ 2*index+1 ∧ 2*index ≠ 2*index+1 := by omega
#print axioms expand_point_slices15
#print axioms expand_two_write_bounds15
#print axioms expand_reverse_frame15
end PV_B3P_Caller15227
''';(L/'PV_B3P_ExpandCallerBounds15227.lean').write_text(s)
s='import PV_B3P_NativePreweighted15227\n'+h+'''
def PreweightedCall15 (start count : Nat) : Prop :=
  (start=0 ∧ count=16) ∨ (start=16 ∧ count=16) ∨ (start=32 ∧ count=17) ∨
  (start=49 ∧ count=33) ∨ (start=82 ∧ count=2) ∨ (start=0 ∧ count=12) ∨
  (start=84 ∧ count=8) ∨ (start=92 ∧ count=2)

theorem preweighted_source_call_bounds15 (start count : Nat) (called : PreweightedCall15 start count) :
    0 < count ∧ start+count ≤ 96 ∧ (start+count-1)/4 < 24 := by
  unfold PreweightedCall15 at called
  rcases called with h|h|h|h|h|h|h|h
  all_goals rcases h with ⟨hs,hn⟩; subst start; subst count; decide

theorem preweighted_window_source_index15 (start count group slot : Nat)
    (slot_bound : slot < 4) (selected : start ≤ 4*group+slot ∧ 4*group+slot < start+count) :
    4*group+slot-start < count := by omega

/-- Only the selected arm reads values[source-start]; the ZERO arm performs
no values read. The call bound makes the final inclusive increment safe. -/
theorem preweighted_source_group_successor15 (start count group : Nat)
    (called : PreweightedCall15 start count) (group_bound : group ≤ (start+count-1)/4) :
    group+1 ≤ 24 := by
  have bound := preweighted_source_call_bounds15 start count called
  omega
#print axioms preweighted_source_call_bounds15
#print axioms preweighted_window_source_index15
#print axioms preweighted_source_group_successor15
end PV_B3P_Caller15227
''';(L/'PV_B3P_PreweightedCallerBounds15227.lean').write_text(s)
