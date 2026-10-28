import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_015
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged (host_transcript.Transcript H)
  := do
  let _ ← observe .opening 0 (ok ())
  let s ← Aeneas.Std.lift (Array.to_slice self.state)
  let i ← Aeneas.Std.lift (Std.U8.wrapping_add 160#u8 row)
  let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ]))
  let i1 := Slice.len payload
  let i2 ← Aeneas.Std.lift (UScalar.cast .U32 i1)
  let a ← Aeneas.Std.lift (core.num.U32.to_le_bytes i2)
  let s2 ← Aeneas.Std.lift (Array.to_slice a)
  let s3 ← Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, payload ]))
  let a1 ← aspis_coredigestDigest32Inst.digest self.hash s3
  ok { self with state := a1 }

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  : :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.absorb (H := H) aspis_coredigestDigest32Inst self row payload := by
  unfold produce host_transcript.Transcript.absorb
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_015
