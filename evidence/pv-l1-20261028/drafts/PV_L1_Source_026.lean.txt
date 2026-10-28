import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_026
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant) :
  Logged (host_transcript.Transcript H)
  := do
  let _ ← observe .opening 0 (ok ())
  let domain ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice
      (Array.make 29#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8, 84#u8, 69#u8, 45#u8,
        83#u8, 65#u8, 76#u8, 84#u8, 69#u8, 68#u8, 58#u8, 80#u8, 51#u8
        ])))
  let i ← PV_L1_Logged.lift (transport.Variant.tag variant)
  let s ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ])))
  let s1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice semantic_state))
  let s2 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 3#usize [ domain, s, s1 ])))
  let a ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest hash s2)
  Pure.pure { state := a, hash }

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant) :
  erase (produce (H := H) aspis_coredigestDigest32Inst hash semantic_state variant) = host_transcript.Transcript.new (H := H) aspis_coredigestDigest32Inst hash semantic_state variant := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.new
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_026
