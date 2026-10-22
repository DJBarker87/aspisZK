import OraclePortStdAllocation
import OraclePortCkptAbi4Std

/-! Actual imported mutable-iterator content operations, with S10's fallible
allocation model. Physical Rust reservation and source loop adoption remain
separate; no allocator availability is asserted. -/
set_option autoImplicit false
namespace AspisR1.OraclePortCkptAbi5Weights
open Aeneas Aeneas.Std Result

def overwrite {T : Type} : List T → core.slice.iter.IterMut T →
    Result (core.slice.iter.IterMut T)
  | [], it => ok it
  | x::xs, it => do
      let (old,rest,back) ← core.slice.iter.IteratorIterMut.next it
      match old with
      | none => .fail .panic
      | some _ => overwrite xs (back rest (some x))

/-- A complete bounded interval is replaced in order through the actual
next/back operation. The arbitrary pre and suffix are retained. -/
theorem overwrite_exact {T : Type} (values old pre suffix : List T)
    (length : values.length = old.length)
    (bound : (pre ++ old ++ suffix).length ≤ Usize.max) :
    overwrite values ⟨⟨pre ++ old ++ suffix,bound⟩,pre.length⟩ =
      ok ⟨⟨pre ++ values ++ suffix,by simpa [List.length_append,length] using bound⟩,
        pre.length + values.length⟩ := by
  induction values generalizing pre old with
  | nil =>
    have empty : old = [] := List.length_eq_zero_iff.mp length.symm
    subst old
    rfl
  | cons x xs ih =>
    cases old with
    | nil => simp only [List.length_cons,List.length_nil] at length; omega
    | cons y ys =>
      have tailLength : xs.length = ys.length := by simpa using length
      have first : pre.length < (pre ++ y::ys ++ suffix).length := by
        simp only [List.length_append,List.length_cons]; omega
      simp only [overwrite,core.slice.iter.IteratorIterMut.next]
      rw [dif_pos (show pre.length < (Slice.len ⟨pre ++ y::ys ++ suffix,bound⟩).val from first)]
      simp only [bind_tc_ok]
      change overwrite xs ⟨Slice.setAtNat (⟨pre ++ y::ys ++ suffix,bound⟩ : Slice T) pre.length x,
        pre.length+1⟩ = _
      have update : Slice.setAtNat (⟨pre ++ y::ys ++ suffix,bound⟩ : Slice T) pre.length x =
          ⟨(pre ++ [x]) ++ ys ++ suffix,by simpa [List.length_append] using bound⟩ := by
        apply Subtype.ext
        simp [Slice.setAtNat,List.set_append_right]
      rw [update]
      have result := ih ys (pre ++ [x]) tailLength
        (by simpa [List.length_append] using bound)
      simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,
        List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm 1] using result

/-- Reservation failure is propagated before any mutable field writes. -/
def allocatedOverwrite {T : Type} (n : Usize) (zero : T) (reserved : Bool)
    (values : List T) : Result (Except OraclePortStdAllocation.AllocationError (Slice T × Nat)) := do
  let allocation ← OraclePortStdAllocation.filled n zero reserved
  match allocation with
  | .error e => ok (.error e)
  | .ok v =>
    let it ← overwrite values ⟨⟨v.val,v.property⟩,0⟩
    ok (.ok (it.slice,it.i))

/-- S10 filled content plus real std mutable writeback gives all decoded
weights and the exact ending index, for both reservation outcomes. It does
not supply source reservation/decoder/loop correspondence. -/
theorem allocated_overwrite_exact {T : Type} (n : Usize) (zero : T) (reserved : Bool)
    (values : List T) (length : values.length = n.val) :
    allocatedOverwrite n zero reserved values =
      if reserved then ok (.ok (⟨values,by rw [length]; scalar_tac⟩,n.val))
      else ok (.error .allocation) := by
  cases reserved with
  | false => rfl
  | true =>
    simp only [allocatedOverwrite,OraclePortStdAllocation.filled_exact,
      OraclePortStdAllocation.filledSpec,↓reduceIte,bind_tc_ok]
    have written := overwrite_exact values (List.replicate n.val zero) [] []
      (by simpa only [List.length_replicate] using length)
      (by simp only [List.nil_append,List.append_nil,List.length_replicate]; scalar_tac)
    simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,length] at written
    rw [written]
    rfl

#print axioms allocated_overwrite_exact
#print axioms overwrite_exact
end AspisR1.OraclePortCkptAbi5Weights
