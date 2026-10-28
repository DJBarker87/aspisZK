import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_017
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_018
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged (aspis_core.field.QM31 × (host_transcript.Transcript H))
  := do
  let _ ← observe .opening 0 (ok ())
  let (a, self1) ←
    PV_L1_Source_017.produce aspis_coredigestDigest32Inst self row
      payload
  let out ← PV_L1_Logged.lift (sampler.qm31_sample a)
  let i ← PV_L1_Logged.lift (Aeneas.Std.lift (UScalar.cast .Usize row))
  let we ← PV_L1_Logged.lift (aspis_core.field.wide_exact.WideExact.from_qm31 out)
  trace.value 4#u16 i we
  Pure.pure (out, self1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.scalar_k (H := H) aspis_coredigestDigest32Inst self row payload := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.scalar_k
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_017.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_017.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_017.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_018
