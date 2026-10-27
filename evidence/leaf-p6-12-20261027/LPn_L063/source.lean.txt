import LPn_Kit_DotModel
import LPn_MonadicFold
open Aeneas Aeneas.Std Result
open LPl_Kit_Release
set_option autoImplicit false
namespace LPn.ClaimsModel
abbrev Row := Array aspis_core.field.QM31 29#usize
abbrev State := core.result.Result (List Row) r1_wire.Error
-- Native sparse reached-storage checks: LPl_A_claim_point0 / LPl_A_claim_point2.
-- They do not close arbitrary rows or allocation failure; no axiom is introduced.
def step (record : r1_wire.ValidatedRecord) (state : State) (point : Nat) : Result State :=
  match state with
  | .Err e => ok (.Err e)
  | .Ok rows => do
    let row ← r1_wire.ValidatedRecord.decode_k 29#usize record (LPn_Kit_usize (point*29))
    match row with
    | .Err e => ok (.Err e)
    | .Ok row => ok (.Ok (rows ++ [row]))

def loop (record : r1_wire.ValidatedRecord) : Result State :=
  LPn.stagesM (step record) (.Ok []) 3

theorem loop_eq_fold (record : r1_wire.ValidatedRecord) :
    loop record = (List.range 3).foldlM (step record) (.Ok []) :=
  LPn.stagesM_fold _ _ _

-- Exact leaf call order in the actual supplied model. This is a projection,
-- not a new success hypothesis or a proof of the native allocator boundary.
theorem leaf_call_order (p : r1_wire.Prefix) :
    r1_semantic.claims p = (do
      let framed ← Array.index_usize p.records 25#usize
      let a ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 0#usize
      match a with
      | .Err e => ok (.Err e)
      | .Ok a =>
        let b ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 29#usize
        match b with
        | .Err e => ok (.Err e)
        | .Ok b =>
          let c ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 58#usize
          match c with
          | .Err e => ok (.Err e)
          | .Ok c => ok (.Ok (Array.make 3#usize [a,b,c]))) := by
  rfl
#print axioms loop_eq_fold
#print axioms leaf_call_order
end LPn.ClaimsModel
