import RPu_FJm_AbsorptionMeaning
import RPu_FJf_CommonValue
import RPu_FJg_PartialsValue
import RPu_FJm_PairTrace
import RPu_FJm_Filled
import RPu_FJm_Continuation
import RPu_FJm_RegularContinuation
import RPu_FJg_SharedProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_Part3Meaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

/-- Actual installed pair's final part3, with allocation and all frames derived
from that pair call. No independently selected parts array is admitted. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8) (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
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
      FIp_ArrayValue.value parts 3=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun j=>algebraMap FK FE (tensorPoint (R0P.SemSource.xor12Point
              (FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))) j)))) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,guard,rest⟩ := FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨n,scratch,scratchOut,a0,a1,ap0,ap1,nativeSelf,common,partials,
    before,highParts,lowParts,parts,k,low,inactive,libra,status,
    hregular,hnsize,hfilled,h0,hp0,h1,hp1,hcom,same,hpartial,hhigh,hstatus,hl,hi,hu,hlib,hk,hsum⟩ :=
    FJm_PairTrace.reached (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)
      nativeOut folds guard hn
  subst nativeSelf
  subst status
  have cv := FJf_CommonValue.sixteen semAlpha z w hc hw (_,common) hcom
  have pv := FJg_PartialsValue.four f common cv.2.1 partials hpartial
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  have v3 := FJm_AbsorptionMeaning.value semAlpha z w hc hw f common partials cv.2.2 pv.2 pv.1
    a0 a1 ap0 ap1 ca0 ca1 hp0 hp1 before highParts hhigh
  have tail := FJm_Continuation.tail f libra highParts lowParts parts inactive hu hlib 3 (by decide) (by decide)
  exact ⟨nativeOut,a0,a1,parts,k,hn,he,h0,h1,hk,hsum,tail.trans v3⟩
#print axioms value
end AspisR1.FJm_Part3Meaning
end
