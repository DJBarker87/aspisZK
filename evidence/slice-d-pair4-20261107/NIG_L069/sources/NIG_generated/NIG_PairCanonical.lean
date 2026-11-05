import NIG_PairS2Body
import NIG_PairSuffix
import NIG_PairValues
set_option autoImplicit false
noncomputable section
namespace NIG_PairCanonical
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_PairFrames

theorem source (r:NP6_StdModel.Reservation) (w:W) (p:AspisR1Stage2.verifier.Prepared)
 (f:Slice U8) (kappa out:NE) (width:f.val.length=2048)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (hf:NHI_TensorOuterStep.Factors w)
 (he:NHI_CellCanon.array w.extra) (hk:canonE kappa)
 (halpha:∀ x∈(FIo_Install.toSlice p.alpha.to_slice).val,canonE x):
 letI:=FIo_Install.allocation r
 FIo_Native.weights.Weights.pair w (FIo_Install.toSlice p.alpha.to_slice) f kappa=ok (.Ok out)→canonE out:=by
 letI:=FIo_Install.allocation r
 intro run
 rw [NIG_PairS2Body.source w p f width kappa] at run
 unfold NIG_PairS2Body.reference at run
 obtain ⟨we,hwe,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have cwe:=NIG_PairValues.slice_read canonE _ _ we halpha hwe
 obtain ⟨ap0,hap0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have ca0:=NIG_PairValues.powers4 we cwe ap0 hap0
 obtain ⟨ap1,hap1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨we1,hwe1,hap1⟩:=Port3_PushFrame.bind_success _ _ _ hap1
 have cwe1:=NIG_PairValues.slice_read canonE _ _ we1 halpha hwe1
 have ca1:=NIG_PairValues.powers4 we1 cwe1 ap1 hap1
 obtain ⟨allocated,hallocated,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases allocated with
 | Err e=>cases run
 | Ok scratch=>
  have init:=NIG_PairFrames.filled r scratch hallocated
  obtain ⟨shared,hshared,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨reply,after,parts⟩,hregular,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have post:=NIG_PairFrames.regular w shared _ f ap0 ap1 s2 hf ca0 ca1 scratch after _ parts reply init hregular
  cases reply with
  | Err e=>cases e <;> cases run
  | Ok u=>
   cases u
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   cases shared with
   | false=>
    change NIG_PairSuffix.dispatch w f ap0 ap1 kappa parts=ok (.Ok out) at run
    rw [NIG_PairSuffix.source w f ap0 ap1 kappa parts s2] at run
    exact NIG_TailControl.canonical w f ap0 ap1 kappa parts s2 width ca0 ca1 he hk post.2.2 out run
   | true=>
    change (do
     let (w1,common)←NIG_CommonLoop.common_reference w (Array.repeat 16#usize NHX_FilledZero.zeroQ)
     let partReply←FIo_Native.weights.shared_partials f common
     let cf←core.result.Result.Insts.CoreOpsTry.branch partReply
     match cf with
     | core.ops.control_flow.ControlFlow.Continue values=>do
      let (rr,pp)←FIo_Native.weights.shared_high values w1 ap0 ap1 parts
      let cf1←core.result.Result.Insts.CoreOpsTry.branch rr
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _=>NIG_PairSuffix.dispatch w1 f ap0 ap1 kappa pp
      | core.ops.control_flow.ControlFlow.Break residual=>core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual NE (core.convert.FromSame FIo_Native.verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break residual=>core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual NE (core.convert.FromSame FIo_Native.verifier.Error) residual)=ok (.Ok out) at run
    obtain ⟨⟨w1,common⟩,hc,run⟩:=Port3_PushFrame.bind_success _ _ _ run
    have emitted:FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w (Array.repeat 16#usize NHX_FilledZero.zeroQ)=ok (w1,common):=by
     rwa [NIG_CommonLoop.common_source]
    obtain ⟨same,commonCanon⟩:=NIG_PairFrames.common w hf w1 common emitted
    subst w1
    obtain ⟨partReply,hpartial,run⟩:=Port3_PushFrame.bind_success _ _ _ run
    cases partReply with
    | Err e=>cases e <;> cases run
    | Ok values=>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨⟨rr,pp⟩,hh,run⟩:=Port3_PushFrame.bind_success _ _ _ run
     have ch:=(NIG_PairFrames.high values w ap0 ap1 parts pp hf ca0 ca1 post.2.2 rr hh).1
     cases rr with
     | Err e=>cases e <;> cases run
     | Ok unit=>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      rw [NIG_PairSuffix.source w f ap0 ap1 kappa pp s2] at run
      exact NIG_TailControl.canonical w f ap0 ap1 kappa pp s2 width ca0 ca1 he hk ch out run
#print axioms source
end NIG_PairCanonical
