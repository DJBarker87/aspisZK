import R1Z.PV_CB_Op118Funs
open Aeneas Aeneas.Std Result PV_CB_ShippedOp118
#eval (do
 let v ← aspis_core.state_only_prefix.state_only_statement_points
   (Array.repeat 10#usize ({c0 := {a := 2#u32,b := 0#u32},c1 := {a := 0#u32,b := 0#u32}} : aspis_core.field.QM31))
 ok (v.val.map (fun a => a.val.map (fun q => [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]))) : Result (List (List (List Nat))))
