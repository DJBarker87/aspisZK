import FJg_Part1Trace
import FJg_SharedPart1
import FJg_SharedProvenance
import FJg_PartialsValue
import FJg_FinalContinuation
import FJc_InstalledFinalPart0
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_Part1Final
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
/-- Joint final part0 and source-arithmetic part1 on the actual final sum's
array. No equality of output sums is used to identify intermediate arrays. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (common : Array NQ 16#usize)
      (partials : Array NE 4#usize) (row : Array (Array NQ 4#usize) 5#usize)
      (coeff low0 low1 : Array NQ 4#usize) (low : Array NE 16#usize) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧ FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FJf_QMArray.canon common ∧
      (∀ j,j<16 → FJf_QMArray.value common j=
        FJf_CommonCell.model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) j) ∧
      FJg_PartialsValue.Values f common partials 4 ∧
      Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok row ∧
      Array.index_usize row 4#usize=ok coeff ∧ Array.index_usize row 0#usize=ok low0 ∧
      Array.index_usize row 1#usize=ok low1 ∧ FIo_ArrayCanon.Holds low ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 0=FJc_InactiveValue.sumPrefix f low 12 ∧
      FIp_ArrayValue.value parts 1=
        (AspisR1CurrentWide.Proof.decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix ap0 low0 4)*
        (AspisR1CurrentWide.Proof.decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix ap1 low1 4)*
        FJg_HighCell.sumPrefix partials coeff 4 := by
  obtain ⟨_,_,_,_,_,_,guard,rest⟩ := FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨a0,a1,ap0,ap1,nativeSelf,common,partials,before,highParts,lowParts,parts,k,
    low,inactive,libra,status,h0,hp0,h1,hp1,hcom,same,hpart,hhigh,hstatus,hl,hi,hu,hlib,hk,hsum⟩ :=
    @FJg_Part1Trace.reached (FIo_Install.allocation r) (FIo_Install.toWeights w)
      (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut folds guard hn
  subst nativeSelf
  subst status
  have cv := FJf_CommonValue.sixteen semAlpha z w hc hw (_,common) hcom
  have pv := FJg_PartialsValue.four f common cv.2.1 partials hpart
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  have cp0 := FIp_PowersValue.powers 4#usize a0 ap0 ca0 hp0
  have cp1 := FIp_PowersValue.powers 4#usize a1 ap1 ca1 hp1
  obtain ⟨row,coeff,low0,low1,hr,hd4,hd0,hd1,part1⟩ :=
    FJg_SharedPart1.value semAlpha z w hc hw partials ap0 ap1 pv.1 cp0.1 cp1.1 before highParts hhigh
  have continuation := FJg_FinalContinuation.value f libra highParts lowParts parts inactive hu hlib
  have lc := FJc_LowValue.sixteen ap0 ap1 cp0.1 cp1.1 low hl
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have iv := hi
  rw [FGm_GroupDispatch.same (FIo_Install.toWeights w) f low variant len] at iv
  have inactiveValue := FJc_InactiveValue.value f low inactive lc.1 iv
  exact ⟨nativeOut,a0,a1,ap0,ap1,common,partials,row,coeff,low0,low1,low,parts,k,
    hn,he,h0,h1,hp0,hp1,cv.2.1,cv.2.2,pv.2,hr,hd4,hd0,hd1,lc.1,hk,hsum,
    continuation.2.trans inactiveValue.2,continuation.1.trans part1⟩
#print axioms value
end AspisR1.FJg_Part1Final
end
