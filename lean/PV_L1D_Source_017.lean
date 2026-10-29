import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_015
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_017
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged ((Array Std.U8 32#usize) × (host_transcript.Transcript H))
  := do
  let _ ← observe .opening 0 (ok ())
  let self1 ←
    PV_L1D_Source_015.produce aspis_coredigestDigest32Inst self row
      payload
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s, s1 ])))
  let block ← PV_L1D_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s2)
  let s3 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s4 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
  let a ← PV_L1D_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s5)
  Pure.pure (block, { self1 with state := a })

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.block (H := H) aspis_coredigestDigest32Inst self row payload := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.block
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_015.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_015.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_015.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_017
