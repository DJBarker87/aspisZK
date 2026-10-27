import FJm_PairLibraInitial
import FJr_ExtraValue
import FJr_LibraMeaning
import FJm_LibraInitialSlot
import FJc_SliceCanonical
import FIp_PowersValue
import FJm_LibraPairTrace
import FJm_LibraCanonical
import FJm_ExtraCanon
import FJg_SharedProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_Part4Meaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
open FJr_LibraFactors (FK FE)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut a0 a1 : NE) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 4=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (FJm_LibraModel.folded (algebraMap FK FE (FJc_WeightArray.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) 8))
          (algebraMap FK FE (FJc_WeightArray.value (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) 9))
          (decodeWide (wide a0)) (decodeWide (wide a1))) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,guard,rest⟩ := FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨n,scratch,scratchOut,a0,a1,ap0,ap1,nativeSelf,common,partials,
    before,highParts,lowParts,parts,k,low,inactive,libra,status,b,
    hregular,hnsize,hfilled,h0,hp0,h1,hp1,hcom,same,hpartial,hhigh,hstatus,hl,hi,hu,hvariant,hlibra,hlib,hk,hsum⟩ :=
    FJm_LibraPairTrace.reached (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f
      (FIo_Install.toE kappa) nativeOut folds guard hn
  subst nativeSelf
  subst status
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  have eb : b=true := by
    rw [variantS2] at hvariant
    have normal : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true := by
      unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
        FIo_Native.transport.Variant.read_discriminant
      simp only [eq_self,decide_true]
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
  have initial := FJm_LibraInitialSlot.value (FIo_Install.toWeights w) (FIo_Install.toSlice alpha)
    f 2#usize n ap0 ap1 partials scratch scratchOut before highParts lowParts inactive hregular hhigh hu
  have meaning := FJr_LibraMeaning.value a0 a1 ap0 ap1 libra (FIo_Install.toWeights w).extra
    ca0 ca1 hp0 hp1 extra actual f lowParts parts initial hlib
  have extraValue := FJr_ExtraValue.value semAlpha z w hw
  rw [extraValue.1,extraValue.2] at meaning
  exact ⟨nativeOut,a0,a1,parts,k,hn,he,h0,h1,hk,hsum,meaning⟩
#print axioms value
end AspisR1.FJr_Part4Meaning
end
