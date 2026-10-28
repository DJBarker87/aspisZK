import R1Z.PV_RDB1_PointerConstruct
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_Copy

/-- Snapshot range-copy interpretation at the existing intrinsic boundary.
The fresh scalar source array does not alias the mutable destination. -/
def overwrite {T : Type} (out : List T) (offset : Nat) (data : List T) : List T :=
  out.take offset ++ data ++ out.drop (offset+data.length)

theorem overwrite_frame {T : Type} (before suffix data : List T) :
    overwrite (before++suffix) before.length data =
      before++data++suffix.drop data.length := by
  unfold overwrite
  rw [List.take_left,List.drop_append]
  have hz : before.drop (before.length+data.length)=[] :=
    List.drop_eq_nil_iff.mpr (by omega)
  rw [hz,Nat.add_sub_cancel_left,List.nil_append]

def copies {T : Type} (out : List T) (offset : Nat) : List (List T) → List T
  | [] => out
  | chunk::rest => copies (overwrite out offset chunk) (offset+chunk.length) rest

theorem copies_result {T : Type} (chunks : List (List T)) (before suffix : List T) :
    copies (before++suffix) before.length chunks =
      before++chunks.flatten++suffix.drop chunks.flatten.length := by
  induction chunks generalizing before suffix with
  | nil => simp only [copies,List.flatten_nil,List.length_nil,List.drop_zero,List.append_nil]
  | cons c cs ih =>
    simp only [copies,overwrite_frame]
    rw [← List.length_append,ih]
    simp only [List.flatten_cons,List.length_append,List.drop_drop,List.append_assoc]

/-- Replacing a valid range preserves the complete buffer length. -/
theorem overwrite_length {T : Type} (out data : List T) (offset : Nat)
    (fits : offset+data.length ≤ out.length) :
    (overwrite out offset data).length=out.length := by
  simp only [overwrite,List.length_append,List.length_take,List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  omega

/-- Every consecutive chunk has a valid destination range when their entire
extent fits. No runtime copy-length or indexing panic is hidden. -/
theorem chunk_bounds (offset used chunk rest bufferLength : Nat)
    (fits : offset+used+chunk+rest ≤ bufferLength) :
    offset+used ≤ offset+used+chunk ∧ offset+used+chunk ≤ bufferLength := by omega

/-- General memory/frame law, including capacity/allocator/observer state
in an arbitrary W: the copy operation touches only its destination bytes. -/
theorem copy_effect {T W : Type} (out data : List T) (offset : Nat) (w : W) :
    (ok (overwrite out offset data,w) : Result (List T × W)) =
      ok (out.take offset++data++out.drop (offset+data.length),w) := rfl

#print axioms overwrite_frame
#print axioms copies_result
#print axioms overwrite_length
#print axioms chunk_bounds
#print axioms copy_effect
end R1Z.PV_RDB1_Copy
