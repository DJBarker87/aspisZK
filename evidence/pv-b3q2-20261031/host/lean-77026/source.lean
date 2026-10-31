import PV_B3Q_ExpandGuards
namespace PV_B3Q_LoopGuards
open Aeneas Aeneas.Std
set_option autoImplicit false
/-- The source forward-counter transfer. A state is reachable from its actual
lower bound only by increments taken in the original strict loop guard. -/
inductive Reach (lower upper : Nat) : Nat → Prop where
 | initial (ordered : lower ≤ upper) : Reach lower upper lower
 | increment {index : Nat} : Reach lower upper index → index < upper →
     Reach lower upper (index+1)

theorem reach_invariant {lower upper index : Nat} (reached : Reach lower upper index) :
 lower ≤ index ∧ index ≤ upper := by
 induction reached with
 | initial ordered => exact ⟨Nat.le_refl _,ordered⟩
 | increment reached guard ih => constructor <;> omega

def Emitted (upper index : Nat) : Prop := Reach 0 upper index ∧ index < upper

theorem emitted_bound {upper index : Nat} (emitted : Emitted upper index) : index < upper :=
 emitted.2

theorem emitted_initial (upper : Nat) (nonempty : 0 < upper) : Emitted upper 0 :=
 ⟨.initial (Nat.zero_le _),nonempty⟩

theorem emitted_successor {upper index : Nat} (emitted : Emitted upper index)
    (next : index+1 < upper) : Emitted upper (index+1) :=
 ⟨.increment emitted.1 emitted.2,next⟩

/-- Every source counter used below is at most 1024. The native wrapping
increment agrees with ordinary addition at every visited loop state. -/
theorem machine_increment (index : Usize) (upper : Nat) (guard : index.val < upper)
    (small : upper ≤ 1024) :
 (Usize.wrapping_add index 1#usize).val = index.val+1 := by
 rw [Usize.wrapping_add_val_eq]
 apply Nat.mod_eq_of_lt
 change index.val+1 < UScalar.size .Usize
 have big : 1024 < UScalar.size .Usize := by
   simpa [UScalar.size,Usize.size,Usize.numBits] using (1024#usize).hBounds
 omega

/-- A source chunk-loop visits only elements before its min(start+4,end).
No assumption on field data or witness words occurs in these bounds. -/
theorem chunk_bounds (start index finish : Nat)
    (outer : start < finish) (inner : start ≤ index)
    (guard : index < min (start+4) finish) : index < finish ∧ index-start < 4 := by
 omega

theorem preweighted_source (start count group slot : Nat)
    (shape : 0 < count ∧ start+count ≤ 96)
    (group_bound : group ≤ (start+count-1)/4)
    (slot_bound : slot < 4)
    (inside : start ≤ 4*group+slot ∧ 4*group+slot < start+count) :
 group < 24 ∧ slot < 4 ∧ 4*group+slot-start < count := by omega

/-- Slice source checks are runtime branch guards, not endpoint restrictions. -/
theorem positive_range_length (start finish : Nat) (ordered : start ≤ finish) :
 start+(finish-start)=finish := by omega
#print axioms reach_invariant
#print axioms emitted_bound
#print axioms emitted_initial
#print axioms emitted_successor
#print axioms machine_increment
#print axioms chunk_bounds
#print axioms preweighted_source
#print axioms positive_range_length
end PV_B3Q_LoopGuards
