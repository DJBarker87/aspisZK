import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_017
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_019
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  Logged (aspis_core.field.wide_exact.WideExact × (host_transcript.Transcript
    H))
  := do
  let _ ← observe .opening 0 (ok ())
  let (block, self1) ←
    PV_L1D_Source_017.produce aspis_coredigestDigest32Inst self row
      payload
  let out ← PV_L1D_Logged.lift (if nonzero
    then ProverRwFull.sampler.gamma_sample block
    else ProverRwFull.sampler.ordinary_sample block)
  let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (UScalar.cast .Usize row))
  trace.value 4#u16 i out
  Pure.pure (out, self1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload nonzero) = host_transcript.Transcript.scalar (H := H) aspis_coredigestDigest32Inst self row payload nonzero := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.scalar
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_017.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_017.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_017.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_019
