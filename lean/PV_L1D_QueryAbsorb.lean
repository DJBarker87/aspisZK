import PV_L1D_ResultCoercion
import PV_L1D_FixedEvents
import PV_L1D_Projection
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_QueryAbsorb
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged PV_L1D_FixedEvents
variable [ExternalTypes] [ExternalFuns]
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged (host_transcript.Transcript H)
  := do
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice self.state))
  let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.U8.wrapping_add 160#u8 row))
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ 0#u8, i ])))
  let i1 := Slice.len payload
  let i2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (UScalar.cast .U32 i1))
  let a ← PV_L1D_Logged.lift (Aeneas.Std.lift (core.num.U32.to_le_bytes i2))
  let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice a))
  let s3 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s, s1, s2, payload ])))
  let a1 ← observe .queryScan 0 (aspis_coredigestDigest32Inst.digest self.hash s3)
  Pure.pure { self with state := a1 }

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  erase (produce aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.absorb aspis_coredigestDigest32Inst self row payload := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.absorb
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,Aeneas.Std.bind_tc_ok,PV_L1D_Projection.prod_case]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,Aeneas.Std.bind_tc_ok,PV_L1D_Projection.prod_case]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
#print axioms complete_result

def readOrder : List R1Z.SideChannelL1AttemptRecord.Event := [R1Z.SideChannelL1AttemptRecord.Event.call .queryScan 0]

theorem completed_order
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Fixed readOrder (produce aspis_coredigestDigest32Inst self row payload) := by
  unfold produce readOrder
  repeat' first
    | apply bind_lift
      intro value
    | apply bind_observe
      intro value
    | exact fixed_lift _
    | exact fixed_pure _
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms completed_order
end PV_L1D_QueryAbsorb
