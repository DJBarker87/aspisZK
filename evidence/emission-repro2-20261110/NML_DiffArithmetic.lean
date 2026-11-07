import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

namespace NML_Old0
abbrev field.M31 := Std.U32
def field.P : Std.U32 := 2147483647#u32
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s
end NML_Old0

namespace NML_Old1
abbrev field.M31 := Std.U32
def field.P : Std.U32 := 2147483647#u32
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s
end NML_Old1

namespace NML_Emitted
abbrev field.M31 := Std.U32
def field.P : Std.U32 := 2147483647#u32
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← lift (Std.U32.wrapping_add self rhs)
  if s >= field.P
  then let s1 ← lift (Std.U32.wrapping_sub s field.P)
       ok s1
  else ok s
end NML_Emitted

namespace NML_Diffs
theorem old0_overflow : NML_Old0.field.M31.add (4294967295#u32) (1#u32) = fail .integerOverflow := by rfl
#print axioms old0_overflow
theorem old1_overflow : NML_Old1.field.M31.add (4294967295#u32) (1#u32) = fail .integerOverflow := by rfl
#print axioms old1_overflow
theorem emitted_wrap : NML_Emitted.field.M31.add (4294967295#u32) (1#u32) = ok (0#u32) := by rfl
#print axioms emitted_wrap
theorem body_difference0 : NML_Old0.field.M31.add ≠ NML_Emitted.field.M31.add := by
 intro h
 have point := congrFun (congrFun h (4294967295#u32)) (1#u32)
 rw [old0_overflow, emitted_wrap] at point
 cases point
#print axioms body_difference0
theorem body_difference1 : NML_Old1.field.M31.add ≠ NML_Emitted.field.M31.add := by
 intro h
 have point := congrFun (congrFun h (4294967295#u32)) (1#u32)
 rw [old1_overflow, emitted_wrap] at point
 cases point
#print axioms body_difference1
end NML_Diffs
