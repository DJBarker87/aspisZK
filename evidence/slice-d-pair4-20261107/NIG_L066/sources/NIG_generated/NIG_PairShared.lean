import NIG_PairSuffix
set_option autoImplicit false
noncomputable section
namespace NIG_PairShared
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_PairFrames
variable [FIo_Native.Allocation]

def reference (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts):Result NIG_TailControl.R:=do
 let (w1,common)←NIG_CommonLoop.common_reference w (Array.repeat 16#usize NHX_FilledZero.zeroQ)
 let partials←FIo_Native.weights.shared_partials f common
 match partials with
 | .Err e=>ok (.Err e)
 | .Ok values=>
  let (reply,after)←FIo_Native.weights.shared_high values w1 ap0 ap1 parts
  match reply with
  | .Err e=>ok (.Err e)
  | .Ok _=>NIG_PairSuffix.dispatch w1 f ap0 ap1 kappa after

theorem canonical (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (width:f.val.length=2048)
 (hf:NHI_TensorOuterStep.Factors w) (ha:canon ap0) (hb:canon ap1)
 (he:NHI_CellCanon.array w.extra) (hk:canonE kappa) (hp:canon parts) (out:NE)
 (run:reference w f ap0 ap1 kappa parts=ok (.Ok out)):canonE out:=by
 unfold reference at run
 obtain ⟨⟨w1,common⟩,hc,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have emitted:FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
  w (Array.repeat 16#usize NHX_FilledZero.zeroQ)=ok (w1,common):=by
  rwa [NIG_CommonLoop.common_source]
 obtain ⟨same,canonicalCommon⟩:=NIG_PairFrames.common w hf w1 common emitted
 subst w1
 obtain ⟨partReply,hp0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases partReply with
 | Err e=>cases run
 | Ok values=>
  have cp:=NIG_PairFrames.partials f common values hp0
  obtain ⟨⟨reply,after⟩,hh,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have ch:=(NIG_PairFrames.high values w ap0 ap1 parts after hf ha hb hp reply hh).1
  cases reply with
  | Err e=>cases run
  | Ok u=>
   rw [NIG_PairSuffix.source w f ap0 ap1 kappa after s2] at run
   exact NIG_TailControl.canonical w f ap0 ap1 kappa after s2 width ha hb he hk ch out run
#print axioms canonical
end NIG_PairShared
