import NIG_PairTail
import NIG_PairModel
set_option autoImplicit false
noncomputable section
namespace NIG_TailControl
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_PairFrames
variable [FIo_Native.Allocation]
abbrev R:=core.result.Result NE FIo_Native.verifier.Error

def reference (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts):Result R:=do
 let low←NIG_LowLoop.low_reference ap0 ap1 (Array.repeat 16#usize NHI_Scalar.zero)
 let value←FIo_Native.weights.grouped_inactive_pair w f low
 let parts0←Array.update parts 0#usize value
 let libra←FIo_Native.weights.factored_s2_libra_weights ap0 ap1 w.extra
 let parts4←NIG_LibraLoop.reference f libra parts0
 let powers←FIo_Native.weights.powers 7#usize kappa
 let sum←NHX_FinalLoop.reference parts4 powers
 ok (.Ok sum)

theorem canonical (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (width:f.val.length=2048)
 (ha:canon ap0) (hb:canon ap1) (he:NHI_CellCanon.array w.extra)
 (hk:canonE kappa) (hp:canon parts) (out:NE)
 (run:reference w f ap0 ap1 kappa parts=ok (.Ok out)):canonE out:=by
 unfold reference at run
 obtain ⟨low,hl,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have lowSource:FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize}
  ap0 ap1 (Array.repeat 16#usize NHI_Scalar.zero)=ok low:=by
  rwa [NIG_LowLoop.low_source]
 have cl:=NIG_PairFrames.low ap0 ap1 ha hb low lowSource
 obtain ⟨value,hv,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have cv:=NIG_PairTail.grouped w f low s2 width cl value hv
 obtain ⟨parts0,h0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have cp0:=(NIG_PairTail.put_zero parts parts0 value hp cv h0).1
 obtain ⟨libra,hlibra,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have cb:=NIG_PairFrames.factored w ap0 ap1 ha hb he libra hlibra
 obtain ⟨parts4,h4,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 have lsource:FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f parts0 libra=ok parts4:=by
  rwa [NIG_LibraLoop.source]
 have cp4:=NIG_PairTail.libra f libra parts0 parts4 cb cp0 lsource
 obtain ⟨powers,hpowers,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨expected,expectedSource,ce⟩:=NHX_Powers7Edge.source kappa hk
 cases Result.ok.inj (expectedSource.symm.trans hpowers)
 obtain ⟨sum,hsum,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨expectedSum,es,cs⟩:=NHX_FinalTotal.source parts4 powers cp4 ce
 rw [NHX_FinalLoop.source] at es
 cases Result.ok.inj (es.symm.trans hsum)
 cases core.result.Result.Ok.inj (Result.ok.inj run)
 exact cs

#print axioms canonical
end NIG_TailControl
