import PV_B3P_P227_01
namespace PV_B3Q_MatrixFixture
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def matrix0 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 31#u32, b := 527#u32 }, c1 := { a := 961#u32, b := 1457#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 32#u32, b := 544#u32 }, c1 := { a := 992#u32, b := 1504#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 33#u32, b := 561#u32 }, c1 := { a := 1023#u32, b := 1551#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 43#u32, b := 731#u32 }, c1 := { a := 1333#u32, b := 2021#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 44#u32, b := 748#u32 }, c1 := { a := 1364#u32, b := 2068#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 45#u32, b := 765#u32 }, c1 := { a := 1395#u32, b := 2115#u32 } }) left2
 .ok sums3
#eval "prepared_matrix:0=" ++ (match matrix0 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix1 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 62#u32, b := 1054#u32 }, c1 := { a := 1922#u32, b := 2914#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 63#u32, b := 1071#u32 }, c1 := { a := 1953#u32, b := 2961#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 64#u32, b := 1088#u32 }, c1 := { a := 1984#u32, b := 3008#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 86#u32, b := 1462#u32 }, c1 := { a := 2666#u32, b := 4042#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 87#u32, b := 1479#u32 }, c1 := { a := 2697#u32, b := 4089#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 88#u32, b := 1496#u32 }, c1 := { a := 2728#u32, b := 4136#u32 } }) left2
 .ok sums3
#eval "prepared_matrix:1=" ++ (match matrix1 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix7 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 248#u32, b := 4216#u32 }, c1 := { a := 7688#u32, b := 11656#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 249#u32, b := 4233#u32 }, c1 := { a := 7719#u32, b := 11703#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 250#u32, b := 4250#u32 }, c1 := { a := 7750#u32, b := 11750#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 344#u32, b := 5848#u32 }, c1 := { a := 10664#u32, b := 16168#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 345#u32, b := 5865#u32 }, c1 := { a := 10695#u32, b := 16215#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 346#u32, b := 5882#u32 }, c1 := { a := 10726#u32, b := 16262#u32 } }) left2
 .ok sums3
#eval "prepared_matrix:7=" ++ (match matrix7 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix19 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 620#u32, b := 10540#u32 }, c1 := { a := 19220#u32, b := 29140#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 621#u32, b := 10557#u32 }, c1 := { a := 19251#u32, b := 29187#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 622#u32, b := 10574#u32 }, c1 := { a := 19282#u32, b := 29234#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 860#u32, b := 14620#u32 }, c1 := { a := 26660#u32, b := 40420#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 861#u32, b := 14637#u32 }, c1 := { a := 26691#u32, b := 40467#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 862#u32, b := 14654#u32 }, c1 := { a := 26722#u32, b := 40514#u32 } }) left2
 .ok sums3
#eval "prepared_matrix:19=" ++ (match matrix19 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
end PV_B3Q_MatrixFixture
