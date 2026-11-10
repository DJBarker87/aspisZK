import Aeneas
import NCX_Reference.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
#print core.array.equality.PartialEqArray.eq
#print core.array.equality.PartialEqArray.ne
#print core.cmp.PartialEqU8
#print Aeneas.Std.core.cmp.PartialEqU8
theorem s1 : (1#u8 <<< 0#i32 : Result Std.U8) = ok 1#u8 := by rfl
theorem s2 : (1#u8 <<< 1#i32 : Result Std.U8) = ok 2#u8 := by rfl
theorem s3 : (1#u8 <<< 1#i32 : Result Std.U8) = ok 2#u8 := by decide
#check @NCX_Reference.required_binding_is_zero
