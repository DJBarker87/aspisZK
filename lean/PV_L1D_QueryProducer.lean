import PV_L1D_QueryAbsorb
import PV_L1D_FixedBind
import PV_L1D_ResultCoercion
import PV_L1D_FixedEvents
import PV_L1D_Projection
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_QueryProducer
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged PV_L1D_FixedEvents
variable [ExternalTypes] [ExternalFuns]
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged ((core.result.Result (Array Std.U32 22#usize) verifier.Error) ×
    (host_transcript.Transcript H))
  := do
  let self1 ← PV_L1D_QueryAbsorb.produce aspis_coredigestDigest32Inst self row
      payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s1 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s, s1 ])))
  let a1 ← observe .queryScan 1 (aspis_coredigestDigest32Inst.digest self1.hash s2)
  let (_, index_mut_back) ← PV_L1D_Logged.lift (Array.index_mut_usize blocks 0#usize)
  let s3 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s4 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s5 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
  let a2 ← observe .queryScan 2 (aspis_coredigestDigest32Inst.digest self1.hash s5)
  let blocks1 := index_mut_back a2
  let state ← PV_L1D_Logged.lift (Array.index_usize blocks1 0#usize)
  let s6 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state))
  let s7 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s8 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s6, s7 ])))
  let a3 ← observe .queryScan 3 (aspis_coredigestDigest32Inst.digest self1.hash s8)
  let blocks2 := index_mut_back a1
  let blocks3 ← PV_L1D_Logged.lift (Array.update blocks2 1#usize a3)
  let s9 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state))
  let s10 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s11 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s9, s10 ])))
  let a4 ← observe .queryScan 4 (aspis_coredigestDigest32Inst.digest self1.hash s11)
  let blocks4 ← PV_L1D_Logged.lift (Array.update blocks1 1#usize a4)
  let state1 ← PV_L1D_Logged.lift (Array.index_usize blocks4 1#usize)
  let s12 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state1))
  let s13 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s14 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s12, s13 ])))
  let a5 ← observe .queryScan 5 (aspis_coredigestDigest32Inst.digest self1.hash s14)
  let blocks5 ← PV_L1D_Logged.lift (Array.update blocks3 2#usize a5)
  let s15 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state1))
  let s16 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s17 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s15, s16 ])))
  let a6 ← observe .queryScan 6 (aspis_coredigestDigest32Inst.digest self1.hash s17)
  let blocks6 ← PV_L1D_Logged.lift (Array.update blocks4 2#usize a6)
  let state2 ← PV_L1D_Logged.lift (Array.index_usize blocks6 2#usize)
  let s18 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state2))
  let s19 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s20 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s18, s19 ])))
  let a7 ← observe .queryScan 7 (aspis_coredigestDigest32Inst.digest self1.hash s20)
  let blocks7 ← PV_L1D_Logged.lift (Array.update blocks5 3#usize a7)
  let s21 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state2))
  let s22 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s23 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s21, s22 ])))
  let a8 ← observe .queryScan 8 (aspis_coredigestDigest32Inst.digest self1.hash s23)
  let blocks8 ← PV_L1D_Logged.lift (Array.update blocks6 3#usize a8)
  let state3 ← PV_L1D_Logged.lift (Array.index_usize blocks8 3#usize)
  let s24 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state3))
  let s25 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s26 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s24, s25 ])))
  let a9 ← observe .queryScan 9 (aspis_coredigestDigest32Inst.digest self1.hash s26)
  let blocks9 ← PV_L1D_Logged.lift (Array.update blocks7 4#usize a9)
  let s27 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state3))
  let s28 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s29 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s27, s28 ])))
  let a10 ← observe .queryScan 10 (aspis_coredigestDigest32Inst.digest self1.hash s29)
  let blocks10 ← PV_L1D_Logged.lift (Array.update blocks8 4#usize a10)
  let state4 ← PV_L1D_Logged.lift (Array.index_usize blocks10 4#usize)
  let s30 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state4))
  let s31 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s32 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s30, s31 ])))
  let a11 ← observe .queryScan 11 (aspis_coredigestDigest32Inst.digest self1.hash s32)
  let blocks11 ← PV_L1D_Logged.lift (Array.update blocks9 5#usize a11)
  let s33 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state4))
  let s34 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s35 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s33, s34 ])))
  let a12 ← observe .queryScan 12 (aspis_coredigestDigest32Inst.digest self1.hash s35)
  let blocks12 ← PV_L1D_Logged.lift (Array.update blocks10 5#usize a12)
  let state5 ← PV_L1D_Logged.lift (Array.index_usize blocks12 5#usize)
  let s36 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state5))
  let s37 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s38 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s36, s37 ])))
  let a13 ← observe .queryScan 13 (aspis_coredigestDigest32Inst.digest self1.hash s38)
  let blocks13 ← PV_L1D_Logged.lift (Array.update blocks11 6#usize a13)
  let s39 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state5))
  let s40 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s41 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s39, s40 ])))
  let a14 ← observe .queryScan 14 (aspis_coredigestDigest32Inst.digest self1.hash s41)
  let blocks14 ← PV_L1D_Logged.lift (Array.update blocks12 6#usize a14)
  let state6 ← PV_L1D_Logged.lift (Array.index_usize blocks14 6#usize)
  let s42 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state6))
  let s43 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s44 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s42, s43 ])))
  let a15 ← observe .queryScan 15 (aspis_coredigestDigest32Inst.digest self1.hash s44)
  let blocks15 ← PV_L1D_Logged.lift (Array.update blocks13 7#usize a15)
  let s45 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice state6))
  let s46 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s47 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s45, s46 ])))
  let a16 ← observe .queryScan 16 (aspis_coredigestDigest32Inst.digest self1.hash s47)
  let blocks16 ← PV_L1D_Logged.lift (Array.update blocks14 7#usize a16)
  let _ ← PV_L1D_Logged.lift (Array.index_usize blocks16 7#usize)
  let r ← PV_L1D_Logged.lift (host_transcript.queries_from_pairs blocks15 blocks16)
  let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (q, state7) := val
    host_transcript.trace_queries q
    Pure.pure (core.result.Result.Ok q, { self1 with state := state7 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U32 22#usize) (core.convert.FromSame verifier.Error)
        residual)
    Pure.pure (r1, self1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  erase (produce aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.queries aspis_coredigestDigest32Inst self row payload := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.queries
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,Aeneas.Std.bind_tc_ok,PV_L1D_Projection.prod_case,PV_L1D_QueryAbsorb.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,Aeneas.Std.bind_tc_ok,PV_L1D_Projection.prod_case,PV_L1D_QueryAbsorb.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
#print axioms complete_result

def readOrder : List R1Z.SideChannelL1AttemptRecord.Event := (R1Z.SideChannelL1AttemptRecord.Event.call .queryScan 0 :: (List.range 16).map (fun n => .call .queryScan (n+1)))

theorem completed_order
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Fixed readOrder (produce aspis_coredigestDigest32Inst self row payload) := by
  unfold produce readOrder
  apply PV_L1D_FixedBind.bind_fixed _ _ [.call .queryScan 0] ((List.range 16).map (fun n => .call .queryScan (n+1)))
  · exact PV_L1D_QueryAbsorb.completed_order _ _ _ _
  · intro firstState
    simp only [PV_L1D_Projection.prod_case]
    repeat' first
      | apply bind_lift
        intro value
      | apply bind_observe
        intro value
      | exact fixed_lift _
      | exact fixed_pure _
      | split <;> simp only [PV_L1D_Projection.prod_case]
    all_goals
      cases value <;> simp only [List.map_nil,PV_L1D_Projection.prod_case]
      all_goals
        apply bind_lift
        intro outcome
        exact fixed_pure _
#print axioms completed_order
end PV_L1D_QueryProducer
