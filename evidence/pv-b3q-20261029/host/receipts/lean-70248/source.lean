import PV_B3P_P227_01
namespace PV_B3Q_MatrixRawFixture1
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def matrix5 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483647#u32, b := 4294967231#u32 }, c1 := { a := 4294963199#u32, b := 4290772991#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483778#u32, b := 16704#u32 }, c1 := { a := 1069056#u32, b := 1094713344#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483909#u32, b := 33472#u32 }, c1 := { a := 2142208#u32, b := 2193620992#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 2147483647#u32, b := 4294967231#u32 }, c1 := { a := 4294963199#u32, b := 4290772991#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 2147483820#u32, b := 22080#u32 }, c1 := { a := 1413120#u32, b := 1447034880#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 2147483993#u32, b := 44224#u32 }, c1 := { a := 2830336#u32, b := 2898264064#u32 } }) left2
 .ok sums3
#eval "raw_matrix:5=" ++ (match matrix5 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix6 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483648#u32, b := 64#u32 }, c1 := { a := 4096#u32, b := 4194304#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483779#u32, b := 16832#u32 }, c1 := { a := 1077248#u32, b := 1103101952#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483910#u32, b := 33600#u32 }, c1 := { a := 2150400#u32, b := 2202009600#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 2147483648#u32, b := 64#u32 }, c1 := { a := 4096#u32, b := 4194304#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 2147483821#u32, b := 22208#u32 }, c1 := { a := 1421312#u32, b := 1455423488#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 2147483994#u32, b := 44352#u32 }, c1 := { a := 2838528#u32, b := 2906652672#u32 } }) left2
 .ok sums3
#eval "raw_matrix:6=" ++ (match matrix6 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix7 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 4294967295#u32, b := 4294967295#u32 }, c1 := { a := 4294967295#u32, b := 4294967295#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 130#u32, b := 16640#u32 }, c1 := { a := 1064960#u32, b := 1090519040#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 261#u32, b := 33408#u32 }, c1 := { a := 2138112#u32, b := 2189426688#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 4294967295#u32, b := 4294967295#u32 }, c1 := { a := 4294967295#u32, b := 4294967295#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 172#u32, b := 22016#u32 }, c1 := { a := 1409024#u32, b := 1442840576#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 345#u32, b := 44160#u32 }, c1 := { a := 2826240#u32, b := 2894069760#u32 } }) left2
 .ok sums3
#eval "raw_matrix:7=" ++ (match matrix7 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix8 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483648#u32, b := 64#u32 }, c1 := { a := 4096#u32, b := 4194304#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483779#u32, b := 16832#u32 }, c1 := { a := 1077248#u32, b := 1103101952#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2147483910#u32, b := 33600#u32 }, c1 := { a := 2150400#u32, b := 2202009600#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 2147483648#u32, b := 64#u32 }, c1 := { a := 4096#u32, b := 4194304#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 2147483821#u32, b := 22208#u32 }, c1 := { a := 1421312#u32, b := 1455423488#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 2147483994#u32, b := 44352#u32 }, c1 := { a := 2838528#u32, b := 2906652672#u32 } }) left2
 .ok sums3
#eval "raw_matrix:8=" ++ (match matrix8 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
def matrix9 : Result (Array (Array U64 3#usize) 3#usize) := do
 let sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
 let left0 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2882400001#u32, b := 3874980053#u32 }, c1 := { a := 3185587577#u32, b := 2161501943#u32 } })
 let left1 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2882400132#u32, b := 3874996821#u32 }, c1 := { a := 3186660729#u32, b := 3260409591#u32 } })
 let left2 ← reference_field.PreparedQm31Multiplier.new ({ c0 := { a := 2882400263#u32, b := 3875013589#u32 }, c1 := { a := 3187733881#u32, b := 64349944#u32 } })
 let sums1 ← reference_field.accumulate_prepared227 sums ({ c0 := { a := 2882400001#u32, b := 3874980053#u32 }, c1 := { a := 3185587577#u32, b := 2161501943#u32 } }) left0
 let sums2 ← reference_field.accumulate_prepared227 sums1 ({ c0 := { a := 2882400174#u32, b := 3875002197#u32 }, c1 := { a := 3187004793#u32, b := 3612731127#u32 } }) left1
 let sums3 ← reference_field.accumulate_prepared227 sums2 ({ c0 := { a := 2882400347#u32, b := 3875024341#u32 }, c1 := { a := 3188422009#u32, b := 768993016#u32 } }) left2
 .ok sums3
#eval "raw_matrix:9=" ++ (match matrix9 with | .ok xs => reprStr (xs.val.flatMap (fun row => row.val.map (fun x => x.val))) | .fail _ => "FAIL" | .div => "DIV")
end PV_B3Q_MatrixRawFixture1
