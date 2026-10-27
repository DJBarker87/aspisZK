import FJm_LibraPairTrace
import FJm_LibraCanonical
import FJm_ExtraCanon
import FJg_SharedProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_PairLibraCanonical
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ)

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut : NE) (ap0 ap1 libra : Array NE 4#usize) (lowParts parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧ FIo_ArrayCanon.Holds libra ∧
      FIo_Native.weights.factored_s2_libra_weights ap0 ap1 (FIo_Install.toWeights w).extra=ok libra ∧
      FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f lowParts libra=ok parts ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,guard,rest⟩ := FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨n,scratch,scratchOut,a0,a1,ap0,ap1,nativeSelf,common,partials,
    before,highParts,lowParts,parts,k,low,inactive,libra,status,b,
    hregular,hnsize,hfilled,h0,hp0,h1,hp1,hcom,same,hpartial,hhigh,hstatus,hl,hi,hu,hvariant,hlibra,hlib,hk,hsum⟩ :=
    FJm_LibraPairTrace.reached (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f
      (FIo_Install.toE kappa) nativeOut folds guard hn
  subst nativeSelf
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  have eb : b=true := by
    rw [variantS2] at hvariant
    have normal : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true := rfl
    rw [normal] at hvariant
    exact (Result.ok.inj hvariant).symm
  have actual : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 (FIo_Install.toWeights w).extra=ok libra := by
    simpa only [eb,ite_true] using hlibra
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  have cp0 := (FIp_PowersValue.powers 4#usize a0 ap0 ca0 hp0).1
  have cp1 := (FIp_PowersValue.powers 4#usize a1 ap1 ca1 hp1).1
  have extra := FJm_ExtraCanon.value semAlpha z w hc hw
  have canon := FJm_LibraCanonical.value ap0 ap1 (FIo_Install.toWeights w).extra libra cp0 cp1 extra actual
  exact ⟨nativeOut,ap0,ap1,libra,lowParts,parts,k,hn,he,canon,actual,hlib,hk,hsum⟩
#print axioms value
end AspisR1.FJm_PairLibraCanonical
end
