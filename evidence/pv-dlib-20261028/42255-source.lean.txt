import R1Z.ProverRwFullTypes
open Aeneas Aeneas.Std
namespace R1Z.PV_DL_Truncation
open ProverRwFull
set_option autoImplicit false

def value (side : digest.core_api.TruncSide) (n : Nat) (full : List U8) : List U8 :=
  match side with
  | .Left => full.take n
  | .Right => full.drop (full.length-n)

theorem length (side : digest.core_api.TruncSide) (n : Nat) (full : List U8)
    (h : n≤full.length) : (value side n full).length=n := by
  cases side
  · simp only [value,List.length_take,Nat.min_eq_left h]
  · simp only [value,List.length_drop];omega

theorem full (side : digest.core_api.TruncSide) (bytes : List U8) :
    value side bytes.length bytes=bytes := by cases side <;> simp [value]

theorem left_source (n : Nat) (bytes : List U8) : value .Left n bytes=bytes.take n := rfl

theorem right_source (n : Nat) (bytes : List U8) :
    value .Right n bytes=bytes.drop (bytes.length-n) := rfl

#print axioms value
#print axioms length
#print axioms full
#print axioms left_source
#print axioms right_source
end R1Z.PV_DL_Truncation
