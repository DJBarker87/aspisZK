import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_056
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8)
  :
  Logged ((core.result.Result (Array aspis_core.field.QM31 10#usize)
    r1_wire.Error) × (host_wire.SemanticTranscript H) × (alloc.vec.Vec
    Std.U8))
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  let zc := Array.repeat 10#usize q
  let (transcript1, bytes1, zc1, pending_return) ← PV_L1D_Logged.lift (host_semantic.zc_rows_loop aspis_coredigestDigest32Inst transcript bytes zc
      0#usize)
  match pending_return with
  | none => Pure.pure (core.result.Result.Ok zc1, transcript1, bytes1)
  | some r => Pure.pure (r, transcript1, bytes1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  erase (produce (H := H) aspis_coredigestDigest32Inst transcript bytes) = host_semantic.zc_rows (H := H) aspis_coredigestDigest32Inst transcript bytes := by
  unfold produce
  conv_rhs => unfold host_semantic.zc_rows
  simp only [erase_bind,erase_observe,erase_lift,Aeneas.Std.bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero hz
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨tr1,bs1,zc1,pending⟩ hr
  cases pending <;> rfl
#print axioms complete_result
end PV_L1D_Source_056
