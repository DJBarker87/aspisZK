import AspisR1CuGammaCall.Funs
import CuSavingsRhoCallerClosure
set_option autoImplicit false
namespace AspisR1RhoPowerTail
open Aeneas Aeneas.Std Result
abbrev pool_v1.pair_forest_semantic_terminal.r0.Public := AspisR1CuGamma.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev r1_wire.Error := AspisR1CuGamma.r1_wire.Error
abbrev verifier.Error.Parse := AspisR1CuRho.verifier.Error.Parse
abbrev verifier.Error.Semantic := AspisR1CuRho.verifier.Error.Semantic
abbrev verifier.Error.Transcript := AspisR1CuRho.verifier.Error.Transcript
abbrev verifier.Error.Relation := AspisR1CuRho.verifier.Error.Relation
abbrev verifier.Error.Merkle := AspisR1CuRho.verifier.Error.Merkle
abbrev verifier.Error.Query := AspisR1CuRho.verifier.Error.Query
abbrev verifier.Error.Checkpoint := AspisR1CuRho.verifier.Error.Checkpoint
abbrev verifier.Phase := AspisR1RhoQuery.verifier.Phase
abbrev verifier.Phase.Parsed := AspisR1RhoQuery.verifier.Phase.Parsed
abbrev verifier.Phase.Semantic := AspisR1RhoQuery.verifier.Phase.Semantic
abbrev verifier.Phase.Prepare := AspisR1RhoQuery.verifier.Phase.Prepare
abbrev retained.tx1_prepare.closure (H : Type) := Unit
class RetainedPrefix where
  verifyObserved : {H : Type} → aspis_core.Digest32 H → pool_v1.pair_forest_semantic_terminal.r0.Public → Slice U8 → H → Option (verifier.Phase → Result Unit) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  parse : Slice U8 → Result (core.result.Result verifier.View verifier.Error)
abbrev r1_semantic.verify_observed [RetainedPrefix] := @RetainedPrefix.verifyObserved _
abbrev verifier.View.parse [RetainedPrefix] := RetainedPrefix.parse
abbrev Finish := {H : Type} → aspis_core.Digest32 H → verifier.View → verifier.Prepared → verifier.Accumulator → Array aspis_core.field.WideExact 29#usize → Slice U8 → Slice U8 → Usize → H → Option (verifier.Phase → Result Unit) → Result (core.result.Result (alloc.vec.Vec U8) verifier.Error)
def verifier.mark (obs : Option (verifier.Phase → Result Unit)) (phase : verifier.Phase) : Result Unit :=
  match obs with
  | none => .ok ()
  | some callback => callback phase
variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks] [AspisR1CuRho.HeapReserve] [RetainedPrefix]

def
  retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (c : retained.tx1_prepare.closure H) (tupled_args : r1_wire.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Semantic

/-- Trait implementation: [aspis_r1_cu_gamma::gamma_new::tx1_prepare::{impl core::ops::function::FnOnce<(aspis_r1_cu_gamma::r1_wire::Error,), aspis_r1_cu_gamma::verifier::Error> for aspis_r1_cu_gamma::gamma_new::tx1_prepare::closure<H>}]
    Source: 'lib.rs', lines 968:84-968:102 -/
@[reducible]
def retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError {H
  : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H) :
  core.ops.function.FnOnce (retained.tx1_prepare.closure H) r1_wire.Error
  verifier.Error := {
  call_once :=
    retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
    aspis_coreDigest32Inst
}

/-- [aspis_r1_cu_gamma::gamma_new::tx1_prepare]:
    Source: 'lib.rs', lines 967:0-971:1 -/
def retained.tx1_prepare
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (v : verifier.View) (hash : H)
  (obs : Option (verifier.Phase → Result Unit))
  (g : Array aspis_core.field.WideExact 29#usize) :
  Result ((core.result.Result ((Array (Array aspis_core.field.QM31 29#usize)
    3#usize) × verifier.Prepared) verifier.Error) × (Array
    aspis_core.field.WideExact 29#usize))
  := do
  let r ←
    r1_semantic.verify_observed aspis_coreDigest32Inst public1 v.semantic hash
      obs
  let r1 ←
    core.result.Result.map_err
      (retained.tx1_prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      aspis_coreDigest32Inst) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    verifier.mark obs verifier.Phase.Semantic
    let (r2, g1) ←
      gamma_new.Prepared.gamma_new_new aspis_coreDigest32Inst val v hash g
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      ok (core.result.Result.Ok (val.claims, val1), g1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
          verifier.Prepared) (core.convert.FromSame verifier.Error) residual
      ok (r3, g1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array (Array aspis_core.field.QM31 29#usize) 3#usize) ×
        verifier.Prepared) (core.convert.FromSame verifier.Error) residual
    ok (r2, g)

/-- [aspis_r1_cu_gamma::gamma_new::tx1]:
    Source: 'lib.rs', lines 973:0-979:1
    Visibility: public -/
def retained.tx1
  (finish : Finish) {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H) (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error)
  := do
  if k > 22#usize
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← verifier.View.parse proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue v =>
      verifier.mark obs verifier.Phase.Parsed
      let g := Array.repeat 29#usize aspis_core.field.WideExact.ZERO
      let (r1, g1) ←
        retained.tx1_prepare aspis_coreDigest32Inst public1 v hash obs g
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (_, p) := val
        let r2 ← verifier.Accumulator.new v.variant
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          verifier.mark obs verifier.Phase.Prepare
          finish aspis_coreDigest32Inst v p val1 g1 public_bytes
            proof k hash obs
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

#print axioms retained.tx1
end AspisR1RhoPowerTail
