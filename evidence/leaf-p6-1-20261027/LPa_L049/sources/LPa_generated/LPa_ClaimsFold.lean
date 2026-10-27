import LPa_Claims
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Claims

def finish (state : State) : Result (core.result.Result (Array Row 3#usize) r1_wire.Error) :=
  match state with
  | .Err e => ok (.Err e)
  | .Ok rows =>
    if h : rows.length = 3 then ok (.Ok ⟨rows,h⟩) else fail .panic

def fromRecord (record : r1_wire.ValidatedRecord) := do
  let state ← loop record
  finish state

theorem fromRecord_spec (record : r1_wire.ValidatedRecord) :
    fromRecord record = (do
      let a ← r1_wire.ValidatedRecord.decode_k 29#usize record 0#usize
      match a with
      | .Err e => ok (.Err e)
      | .Ok a =>
        let b ← r1_wire.ValidatedRecord.decode_k 29#usize record 29#usize
        match b with
        | .Err e => ok (.Err e)
        | .Ok b =>
          let c ← r1_wire.ValidatedRecord.decode_k 29#usize record 58#usize
          match c with
          | .Err e => ok (.Err e)
          | .Ok c => ok (.Ok (Array.make 3#usize [a,b,c]))) := by
  have h0 : XRk_usize (0*29) = 0#usize := by rfl
  have h1 : XRk_usize (1*29) = 29#usize := by rfl
  have h2 : XRk_usize (2*29) = 58#usize := by rfl
  simp only [fromRecord, loop, LPa.stagesM, step, h0, h1, h2, bind_tc_ok,
    List.nil_append]
  cases ha : r1_wire.ValidatedRecord.decode_k 29#usize record 0#usize with
  | fail e => rfl
  | div => rfl
  | ok a =>
    cases a with
    | Err e => rfl
    | Ok a =>
      simp only [bind_tc_ok]
      cases hb : r1_wire.ValidatedRecord.decode_k 29#usize record 29#usize with
      | fail e => rfl
      | div => rfl
      | ok b =>
        cases b with
        | Err e => rfl
        | Ok b =>
          simp only [bind_tc_ok]
          cases hc : r1_wire.ValidatedRecord.decode_k 29#usize record 58#usize with
          | fail e => rfl
          | div => rfl
          | ok c => cases c <;> rfl

theorem leaf_eq_loop (p : r1_wire.Prefix) :
    r1_semantic.claims p = (do
      let framed ← Array.index_usize p.records 25#usize
      fromRecord ⟨25#u8,framed⟩) := by
  simp only [fromRecord_spec]
  rfl
#print axioms fromRecord_spec
#print axioms leaf_eq_loop
end LPa.Claims
