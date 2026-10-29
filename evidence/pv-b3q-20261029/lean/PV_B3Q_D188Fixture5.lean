import PV_B3P_P227_14
namespace PV_B3Q_D188Fixture5
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def report {n : Usize} (r : Result (Array aspis_core.field.QM31 n)) : String :=
 match r with
 | .ok xs => reprStr (xs.val.flatMap (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))
 | .fail _ => "FAIL"
 | .div => "DIV"
def sum0 := reference_poseidon.internal_sum227 (Array.make 4#usize [17#u64, 18#u64, 19#u64, 20#u64] (by rfl)) ({ c0 := { a := 53#u32, b := 901#u32 }, c1 := { a := 1643#u32, b := 2491#u32 } })
#eval "internal_sum227:0=" ++ (match sum0 with | .ok xs => reprStr (xs.val.map (fun x => x.val)) | .fail _ => "FAIL" | .div => "DIV")
def sum1 := reference_poseidon.internal_sum227 (Array.make 4#usize [18#u64, 19#u64, 20#u64, 21#u64] (by rfl)) ({ c0 := { a := 54#u32, b := 918#u32 }, c1 := { a := 1674#u32, b := 2538#u32 } })
#eval "internal_sum227:1=" ++ (match sum1 with | .ok xs => reprStr (xs.val.map (fun x => x.val)) | .fail _ => "FAIL" | .div => "DIV")
def sum7 := reference_poseidon.internal_sum227 (Array.make 4#usize [24#u64, 25#u64, 26#u64, 27#u64] (by rfl)) ({ c0 := { a := 60#u32, b := 1020#u32 }, c1 := { a := 1860#u32, b := 2820#u32 } })
#eval "internal_sum227:7=" ++ (match sum7 with | .ok xs => reprStr (xs.val.map (fun x => x.val)) | .fail _ => "FAIL" | .div => "DIV")
def sum19 := reference_poseidon.internal_sum227 (Array.make 4#usize [36#u64, 37#u64, 38#u64, 39#u64] (by rfl)) ({ c0 := { a := 72#u32, b := 1224#u32 }, c1 := { a := 2232#u32, b := 3384#u32 } })
#eval "internal_sum227:19=" ++ (match sum19 with | .ok xs => reprStr (xs.val.map (fun x => x.val)) | .fail _ => "FAIL" | .div => "DIV")
end PV_B3Q_D188Fixture5
