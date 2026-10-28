import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1_Source_015
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_016
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  :
  Logged ((core.result.Result (Array Std.U32 22#usize) verifier.Error) ×
    (host_transcript.Transcript H))
  := do
  let _ ← observe .queryScan 0 (ok ())
  let self1 ←
    PV_L1_Source_015.produce aspis_coredigestDigest32Inst self row
      payload
  let a := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize a
  let s ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s2 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s, s1 ])))
  let a1 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s2)
  let (_, index_mut_back) ← PV_L1_Logged.lift (Array.index_mut_usize blocks 0#usize)
  let s3 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice self1.state))
  let s4 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s5 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s3, s4 ])))
  let a2 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s5)
  let blocks1 := index_mut_back a2
  let state ← PV_L1_Logged.lift (Array.index_usize blocks1 0#usize)
  let s6 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state))
  let s7 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s8 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s6, s7 ])))
  let a3 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s8)
  let blocks2 := index_mut_back a1
  let blocks3 ← PV_L1_Logged.lift (Array.update blocks2 1#usize a3)
  let s9 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state))
  let s10 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s11 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s9, s10 ])))
  let a4 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s11)
  let blocks4 ← PV_L1_Logged.lift (Array.update blocks1 1#usize a4)
  let state1 ← PV_L1_Logged.lift (Array.index_usize blocks4 1#usize)
  let s12 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state1))
  let s13 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s14 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s12, s13 ])))
  let a5 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s14)
  let blocks5 ← PV_L1_Logged.lift (Array.update blocks3 2#usize a5)
  let s15 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state1))
  let s16 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s17 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s15, s16 ])))
  let a6 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s17)
  let blocks6 ← PV_L1_Logged.lift (Array.update blocks4 2#usize a6)
  let state2 ← PV_L1_Logged.lift (Array.index_usize blocks6 2#usize)
  let s18 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state2))
  let s19 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s20 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s18, s19 ])))
  let a7 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s20)
  let blocks7 ← PV_L1_Logged.lift (Array.update blocks5 3#usize a7)
  let s21 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state2))
  let s22 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s23 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s21, s22 ])))
  let a8 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s23)
  let blocks8 ← PV_L1_Logged.lift (Array.update blocks6 3#usize a8)
  let state3 ← PV_L1_Logged.lift (Array.index_usize blocks8 3#usize)
  let s24 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state3))
  let s25 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s26 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s24, s25 ])))
  let a9 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s26)
  let blocks9 ← PV_L1_Logged.lift (Array.update blocks7 4#usize a9)
  let s27 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state3))
  let s28 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s29 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s27, s28 ])))
  let a10 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s29)
  let blocks10 ← PV_L1_Logged.lift (Array.update blocks8 4#usize a10)
  let state4 ← PV_L1_Logged.lift (Array.index_usize blocks10 4#usize)
  let s30 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state4))
  let s31 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s32 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s30, s31 ])))
  let a11 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s32)
  let blocks11 ← PV_L1_Logged.lift (Array.update blocks9 5#usize a11)
  let s33 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state4))
  let s34 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s35 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s33, s34 ])))
  let a12 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s35)
  let blocks12 ← PV_L1_Logged.lift (Array.update blocks10 5#usize a12)
  let state5 ← PV_L1_Logged.lift (Array.index_usize blocks12 5#usize)
  let s36 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state5))
  let s37 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s38 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s36, s37 ])))
  let a13 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s38)
  let blocks13 ← PV_L1_Logged.lift (Array.update blocks11 6#usize a13)
  let s39 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state5))
  let s40 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s41 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s39, s40 ])))
  let a14 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s41)
  let blocks14 ← PV_L1_Logged.lift (Array.update blocks12 6#usize a14)
  let state6 ← PV_L1_Logged.lift (Array.index_usize blocks14 6#usize)
  let s42 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state6))
  let s43 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 1#u8 ])))
  let s44 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s42, s43 ])))
  let a15 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s44)
  let blocks15 ← PV_L1_Logged.lift (Array.update blocks13 7#usize a15)
  let s45 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice state6))
  let s46 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ 2#u8 ])))
  let s47 ← PV_L1_Logged.lift (Aeneas.Std.lift (Array.to_slice (Array.make 2#usize [ s45, s46 ])))
  let a16 ← PV_L1_Logged.lift (aspis_coredigestDigest32Inst.digest self1.hash s47)
  let blocks16 ← PV_L1_Logged.lift (Array.update blocks14 7#usize a16)
  let _ ← PV_L1_Logged.lift (Array.index_usize blocks16 7#usize)
  let r ← PV_L1_Logged.lift (host_transcript.queries_from_pairs blocks15 blocks16)
  let cf ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (q, state7) := val
    host_transcript.trace_queries q
    Pure.pure (core.result.Result.Ok q, { self1 with state := state7 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ← PV_L1_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array Std.U32 22#usize) (core.convert.FromSame verifier.Error)
        residual)
    Pure.pure (r1, self1)

theorem complete_result
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  erase (produce (H := H) aspis_coredigestDigest32Inst self row payload) = host_transcript.Transcript.queries (H := H) aspis_coredigestDigest32Inst self row payload := by
  unfold produce
  conv_rhs => unfold host_transcript.Transcript.queries
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_015.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_015.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_015.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_016
