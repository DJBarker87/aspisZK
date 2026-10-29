import PV_B3P_P227_01
namespace PV_B3Q_MatrixRawFixture0
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def matrix0 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 131#u32, b := 16768#u32 }, c1 := { a := 1073152#u32, b := 1098907648#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 262#u32, b := 33536#u32 }, c1 := { a := 2146304#u32, b := 2197815296#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 173#u32, b := 22144#u32 }, c1 := { a := 1417216#u32, b := 1451229184#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 346#u32, b := 44288#u32 }, c1 := { a := 2834432#u32, b := 2902458368#u32 } }) left2
 .ok sums3
#eval "raw_matrix:0=" ++ (match matrix0 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix1 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 1#u32, b := 128#u32 }, c1 := { a := 8192#u32, b := 8388608#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 132#u32, b := 16896#u32 }, c1 := { a := 1081344#u32, b := 1107296256#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 263#u32, b := 33664#u32 }, c1 := { a := 2154496#u32, b := 2206203904#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 1#u32, b := 128#u32 }, c1 := { a := 8192#u32, b := 8388608#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 174#u32, b := 22272#u32 }, c1 := { a := 1425408#u32, b := 1459617792#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 347#u32, b := 44416#u32 }, c1 := { a := 2842624#u32, b := 2910846976#u32 } }) left2
 .ok sums3
#eval "raw_matrix:1=" ++ (match matrix1 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix2 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 7#u32, b := 896#u32 }, c1 := { a := 57344#u32, b := 58720256#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 138#u32, b := 17664#u32 }, c1 := { a := 1130496#u32, b := 1157627904#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 269#u32, b := 34432#u32 }, c1 := { a := 2203648#u32, b := 2256535552#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 7#u32, b := 896#u32 }, c1 := { a := 57344#u32, b := 58720256#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 180#u32, b := 23040#u32 }, c1 := { a := 1474560#u32, b := 1509949440#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 353#u32, b := 45184#u32 }, c1 := { a := 2891776#u32, b := 2961178624#u32 } }) left2
 .ok sums3
#eval "raw_matrix:2=" ++ (match matrix2 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix3 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 19#u32, b := 2432#u32 }, c1 := { a := 155648#u32, b := 159383552#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 150#u32, b := 19200#u32 }, c1 := { a := 1228800#u32, b := 1258291200#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 281#u32, b := 35968#u32 }, c1 := { a := 2301952#u32, b := 2357198848#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 19#u32, b := 2432#u32 }, c1 := { a := 155648#u32, b := 159383552#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 192#u32, b := 24576#u32 }, c1 := { a := 1572864#u32, b := 1610612736#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 365#u32, b := 46720#u32 }, c1 := { a := 2990080#u32, b := 3061841920#u32 } }) left2
 .ok sums3
#eval "raw_matrix:3=" ++ (match matrix3 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix4 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483646#u32, b := 4294967103#u32 }, c1 := { a := 4294955007#u32, b := 4282384383#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483777#u32, b := 16576#u32 }, c1 := { a := 1060864#u32, b := 1086324736#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483908#u32, b := 33344#u32 }, c1 := { a := 2134016#u32, b := 2185232384#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 2147483646#u32, b := 4294967103#u32 }, c1 := { a := 4294955007#u32, b := 4282384383#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 2147483819#u32, b := 21952#u32 }, c1 := { a := 1404928#u32, b := 1438646272#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 2147483992#u32, b := 44096#u32 }, c1 := { a := 2822144#u32, b := 2889875456#u32 } }) left2
 .ok sums3
#eval "raw_matrix:4=" ++ (match matrix4 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
end PV_B3Q_MatrixRawFixture0
