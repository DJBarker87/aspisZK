import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
import PV_L1_Source_042
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_043
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (initial_claim : aspis_core.field.QM31) (oracle : T1) :
  Logged ((core.result.Result ((Array aspis_core.field.QM31 10#usize) ×
    aspis_core.field.QM31) r1_wire.Error) × (host_wire.SemanticTranscript H)
    × (alloc.vec.Vec Std.U8))
  := do
  let _ ← observe (.boundary 0) 0 (ok ())
  let q ← PV_L1_Logged.lift (aspis_core.field.QM31.ZERO)
  let a := Array.repeat 10#usize q
  PV_L1_Source_042.produce aspis_coredigestDigest32Inst OracleInst
    transcript output a initial_claim 0#usize oracle

theorem complete_result
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (initial_claim : aspis_core.field.QM31) (oracle : T1) :
  erase (produce (H := H) (T1 := T1) aspis_coredigestDigest32Inst OracleInst transcript output initial_claim oracle) = host_sumcheck.prove_sumcheck (H := H) (T1 := T1) aspis_coredigestDigest32Inst OracleInst transcript output initial_claim oracle := by
  unfold produce
  conv_rhs => unfold host_sumcheck.prove_sumcheck
  simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_042.complete_result]
  repeat' first
    | with_reducible rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_042.complete_result]
#print axioms complete_result
end PV_L1_Source_043
