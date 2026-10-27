import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ControlFlow Error
namespace R1Z.PV_CB3_WeightsPickSource
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
/-- [pv_cb3_source::resume6_tensor_reference::pick4]:
    Source: 'resume6_tensor_reference.rs', lines 4:0-7:1
    Visibility: public -/
def resume6_tensor_reference.pick4
  (xs : Array aspis_core.field.QM31 4#usize) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let a ← Array.index_usize xs 0#usize
  let b ← Array.index_usize xs 1#usize
  let c ← Array.index_usize xs 2#usize
  let d ← Array.index_usize xs 3#usize
  match i.val with
  | 0 => ok a
  | 1 => ok b
  | 2 => ok c
  | 3 => ok d
  | _ => fail panic

end R1Z.PV_CB3_WeightsPickSource
