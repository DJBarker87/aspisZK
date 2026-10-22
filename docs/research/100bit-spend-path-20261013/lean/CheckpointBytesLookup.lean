import CheckpointBytesBlocks
import OraclePortCheckpointSlicesC5

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesLookup
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCheckpointAbiC5 OraclePortCompactDraft

theorem slice_byte (b : Bytes) (start width i : Nat) (bound : i < width) :
    (slice b start width)[i]? = b[start+i]? := by
  simp [slice,List.getElem?_take,bound,Nat.add_comm]

theorem block_offset (j : Fin 18) :
    (widths.take j.val).sum = offsets[j.val]'(by have := j.isLt; simp [offsets] <;> omega) := by
  fin_cases j <;> rfl

/-- Structural block lookup uses only the 18-entry width/offset table. -/
theorem body_byte (p : Prepared) (a : QueryAccumulator.State K E) (hp hu : State)
    (j : Fin 18) (field : Bytes) (entry : (blocks p a hp hu)[j.val]? = some field)
    (i : Nat) (bound : i < field.length) :
    (body p a hp hu)[offsets[j.val]'(by have := j.isLt; simp [offsets] <;> omega)+i]? = field[i]? := by
  have sliced := OraclePortCheckpointSlicesC5.slice_index (blocks p a hp hu) j.val field entry
  rw [List.map_take,block_widths,block_offset j] at sliced
  have byte := congrArg (fun bs : Bytes => bs[i]?) sliced
  rw [slice_byte _ _ _ i bound] at byte
  exact byte

/-- Arbitrary fixed-width vector lookup; induction is on the vector length. -/
theorem vector_byte {n : Nat} (f : Fin n → Bytes) (width : Nat)
    (length : ∀ j, (f j).length = width) (j : Fin n) (i : Nat) (bound : i < width) :
    ((List.ofFn f).flatten)[width*j.val+i]? = (f j)[i]? := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.mul_zero,Nat.zero_add]
      exact List.getElem?_append_left (by rw [length]; exact bound)
    · simp only [List.ofFn_succ,List.flatten_cons,Fin.val_succ]
      rw [List.getElem?_append_right (by rw [length]; simp only [Nat.mul_add,Nat.mul_one]; omega),length]
      have index : width*(k.val+1)+i-width = width*k.val+i := by simp only [Nat.mul_add,Nat.mul_one]; omega
      rw [index]
      exact ih (fun k => f k.succ) (fun k => length k.succ) k

#print axioms slice_byte
#print axioms block_offset
#print axioms body_byte
#print axioms vector_byte
end AspisR1.CheckpointBytesLookup
end
