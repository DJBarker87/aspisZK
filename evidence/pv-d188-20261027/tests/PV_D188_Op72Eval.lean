import R1Z.PV_CB_Op72Funs
open Aeneas Aeneas.Std Result PV_CB_ShippedOp72
-- Testing commands only; no theorem, no proof credit.
#eval (do
  let buf ← lift (Array.to_slice (Array.repeat 20#usize 255#u8))
  let out ← aspis_core.field.QM31.write_le_bytes
    { c0 := { a := 1#u32, b := 2#u32 }, c1 := { a := 3#u32, b := 4#u32 } }
    buf
  ok (out.val.map (fun x => x.val)) : Result (List Nat))
