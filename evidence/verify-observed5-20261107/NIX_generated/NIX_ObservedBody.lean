import NIX_EmittedTypes
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIX_ObservedBody
open NIX_EmittedTypes
/-- The four external functions are dictionary fields, never template axioms.
Types and native body come from the sole retained E001 LLBC / L008 emission. -/
structure Boundaries (H : Type) where
 parse : Slice U8 → Result (core.result.Result r1_wire.Prefix r1_wire.Error)
 publicTranscript : aspis_core.digest.Digest32 H →
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → H →
  Array U8 32#usize → Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error)
 begin : aspis_core.digest.Digest32 H → r1_wire.Prefix → r1_wire.SemanticTranscript H →
  Result (core.result.Result aspis_core.state_only_prefix.r0.Challenges r1_wire.Error × r1_wire.SemanticTranscript H)
 finish : aspis_core.digest.Digest32 H →
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
  r1_wire.SemanticTranscript H → aspis_core.state_only_prefix.r0.Challenges →
  Option (verifier.Phase → Result Unit) → Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)

/-- [aspis_r1_cost_probe::r1_semantic::mark]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 75:0-80:1 -/
def mark
  (obs : Option (verifier.Phase → Result Unit)) (i : Std.U8) :
  Result Unit
  := do
  ok ()

/-- [aspis_r1_cost_probe::r1_semantic::verify_observed]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_semantic.rs', lines 311:0-318:1
    Visibility: public -/
def emitted
  {H : Type} (B : Boundaries H) (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (verifier.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ← B.parse bytes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    mark obs 0#u8
    let r1 ←
      B.publicTranscript aspis_coredigestDigest32Inst public1 hash
        p.c1_root
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, val1) ← B.begin aspis_coredigestDigest32Inst p val
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        mark obs 1#u8
        B.finish aspis_coredigestDigest32Inst public1 p val1
          val2 obs
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual


/-- The emitted deployed mark is effect-free for every callback value. -/
theorem mark_value (obs : Option (verifier.Phase → Result Unit)) (i : U8) : mark obs i=ok () := rfl
#print axioms mark_value
end AspisR1.NIX_ObservedBody
end
