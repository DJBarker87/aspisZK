import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_044
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (row : Std.U8) (payload : Slice Std.U8)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8)
  :
  Logged ((core.result.Result aspis_core.field.QM31 r1_wire.Error) ×
    (host_wire.SemanticTranscript H) × (alloc.vec.Vec Std.U8))
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let r ← PV_L1D_Logged.lift (host_wire.record row payload)
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val
    let (r1, transcript1) ← PV_L1D_Logged.lift (host_wire.SemanticTranscript.semantic aspis_coredigestDigest32Inst
        transcript row s)
    let cf1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r1)
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let s1 := alloc.vec.Vec.deref val
      let bytes1 ← PV_L1D_Logged.lift (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes s1)
      Pure.pure (core.result.Result.Ok val1, transcript1, bytes1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual)
      Pure.pure (r2, transcript1, bytes)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame r1_wire.Error) residual)
    Pure.pure (r1, transcript, bytes)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (row : Std.U8) (payload : Slice Std.U8)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  erase (produce (H := H) aspis_coredigestDigest32Inst row payload transcript bytes) = host_semantic.semantic_row (H := H) aspis_coredigestDigest32Inst row payload transcript bytes := by
  unfold produce
  conv_rhs => unfold host_semantic.semantic_row
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_044
