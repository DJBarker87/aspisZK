import NHI_FilledBridge
set_option autoImplicit false
namespace NHM_FilledFrame
open Aeneas Aeneas.Std Result AspisR1 NP6_StdModel

/-- The resize initialization invariant: a prefix is unchanged when one new
copy is appended, and the new selected cell is exactly the SAME input value. -/
theorem window {T : Type} (prefix : List T) (value : T) (i : Nat) :
 (prefix ++ [value])[i]? =
 if i < prefix.length then prefix[i]? else if i = prefix.length then some value else none := by
 by_cases h : i < prefix.length
 · simp [List.getElem?_append,h]
 · by_cases e : i=prefix.length
   · subst i; simp
   · simp [List.getElem?_append,h]
     have : 0 < i-prefix.length := by omega
     simp [List.getElem?_eq_none (by simpa using this),e]

/-- Induction on allocation initialization, with no successful-allocation premise. -/
theorem prefix {T : Type} (n : Nat) (value : T) :
 List.replicate (n+1) value = List.replicate n value ++ [value] := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [List.replicate_succ,List.cons_append,ih]

/-- Error transport preserves the entire caller frame. This is a model law;
the native reserve/error observation is separately required. -/
theorem allocation_error {T Frame : Type} (frame : Frame) (n : Usize) (value : T)
 (e : NP6_StdModel.ReservationError) :
 (NHI_FilledModel.result (.Err e) n value,frame)=
 (ok (core.result.Result.Err FIo_Native.aspis_core.r0.Error.Allocation),frame) := by rfl

#print axioms window
#print axioms prefix
#print axioms allocation_error
end NHM_FilledFrame
