import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
import PV_L1_Source_017
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_019
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
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
    PV_L1_Source_017.produce aspis_coredigestDigest32Inst self row
      payload
  let out ←
    if nonzero
    then sampler.gamma_sample block
    else sampler.ordinary_sample block
  let i ← Aeneas.Std.lift (UScalar.cast .Usize row)
  trace.value 4#u16 i out
  ok (out, self1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) : :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload nonzero) = host_transcript.Transcript.scalar (H := H) aspis_coredigestDigest32Inst self row payload nonzero := by
  unfold produce host_transcript.Transcript.scalar
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_017.complete_result]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_017.complete_result]
#print axioms complete_result
end PV_L1_Source_019
