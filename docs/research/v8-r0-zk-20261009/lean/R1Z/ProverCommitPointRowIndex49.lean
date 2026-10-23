import AspisR1ProducerRelease47.PointRows49
import R1Z.ProverCommitPointWeight49
import R1Z.ProverCommitArray49
import R1Z.ProverCommitInactiveRow49
/-! The literal point-factor permutation table and its source coordinate
arithmetic. Only five scalar entries are inspected. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPointRowIndex49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPointTensor49

def tau (i : Nat) : Usize :=
  if i=0 then 3#usize else if i=1 then 4#usize else if i=2 then 2#usize
  else if i=3 then 0#usize else 1#usize

theorem tau_array : point_rows.TAU=ProverCommitArray49.array 5#usize tau := by
  apply Subtype.ext
  rfl

theorem tau_value (i : Fin 5) : (tau i.val).val=(d18Tau i).val := by
  fin_cases i <;> rfl

theorem tau_index (d : Usize) (hd : d.val<5) :
    Array.index_usize point_rows.TAU d=ok (tau d.val) := by
  rw [tau_array,ProverCommitArray49.index _ _ _ hd]

theorem coordinates (d : Usize) (hd : d.val<5) :
    (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize (tau d.val))).val=
      (ProverCommitPointWeight49.a ⟨d.val,hd⟩).val ∧
    (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize (tau d.val))).val=
      (ProverCommitPointWeight49.b ⟨d.val,hd⟩).val := by
  have ht : (tau d.val).val<5 := by rw [tau_value ⟨d.val,hd⟩];exact (d18Tau ⟨d.val,hd⟩).isLt
  have hm : (Usize.wrapping_mul 2#usize (tau d.val)).val=2*(tau d.val).val :=
    ProverCommitInactiveRow49.mul_val _ _ (by change 2*(tau d.val).val<2048;omega)
  constructor
  · rw [ProverCommitSampleBits49.sub_value _ _ (by rw [hm];change 2*(tau d.val).val≤9;omega),hm,tau_value ⟨d.val,hd⟩]
    rfl
  · rw [ProverCommitSampleBits49.sub_value _ _ (by rw [hm];change 2*(tau d.val).val≤8;omega),hm,tau_value ⟨d.val,hd⟩]
    rfl

#print axioms tau_array
#print axioms tau_value
#print axioms tau_index
#print axioms coordinates
end R1Z.ProverCommitPointRowIndex49
