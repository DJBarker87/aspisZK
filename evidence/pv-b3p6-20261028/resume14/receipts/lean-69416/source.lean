import PV_B3P_Frontier14Port
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier
set_option autoImplicit false
abbrev FF14 := alloc.vec.Vec U8 → Slice U32 → Result ((core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × alloc.vec.Vec U8)
abbrev FV14 := Array (Array U32 8#usize) 20#usize
abbrev FS14 := (core.result.Result Unit aspis_core.state_only_prefix.r0.Error) × alloc.vec.Vec U8

def frontier_step14 (fields : FF14) (next : alloc.vec.Vec U8 → FV14 → Result FS14)
    (index : Usize) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do
  let row ← Array.index_usize values index
  let slice ← lift (Array.to_slice row)
  let (r,out1) ← fields out slice
  let branch ← core.result.Result.Insts.CoreOpsTry.branch r
  match branch with
  | .Continue _ => next out1 values
  | .Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual
    .ok (error,out1)
def suffix20_14 (_fields : FF14) (out : alloc.vec.Vec U8) (_values : FV14) : Result FS14 := .ok (.Ok (),out)
#print axioms suffix20_14
end PV_B3P_FrontierStages14227
