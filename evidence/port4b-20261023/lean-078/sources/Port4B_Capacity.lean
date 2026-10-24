import Port4B_TailReads

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Capacity
open Aeneas Aeneas.Std Result

/-- The installed physical table read is the P6 capacity on all six slots. -/
theorem read (slot cap : Usize) (b k : Nat) (hb : b<2) (hk : k<3)
    (value : slot.val=3*b+k)
    (returned : Array.index_usize
      (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) slot=ok cap) :
    cap.val=OraclePortSelectedDraft.capacity (3*b+k) := by
  interval_cases b <;> interval_cases k
  all_goals
    simp [Array.index_usize,Array.make,value] at returned
    subst cap
    decide

#print axioms read
end AspisR1.Port4B_Capacity
end
