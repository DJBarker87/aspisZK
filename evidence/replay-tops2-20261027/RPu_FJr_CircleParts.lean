import RPu_FJr_RegularKindMeaning
import RPu_FJr_NativeRow
import RPu_FJr_ConstructorCircleRows
import RPu_FJr_KindTwoScratch
import RPu_FJr_CircleLiteral
import RPu_FJr_KindIndices
import RPu_FJm_PairTrace
import RPu_FJm_Filled
import RPu_FJm_Continuation
import RPu_FJm_RegularContinuation
import RPu_FJg_SharedProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleParts
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

/-- Actual installed pair's final part2, with allocation and all frames derived
from that pair call. No independently selected parts array is admitted. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8) (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut a0 a1 : NE) (p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize=ok p1 ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 5=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
              (FJc_WeightValues.decode p0.x) (FJc_WeightValues.decode p0.y) j.val)))) ∧
      FIp_ArrayValue.value parts 6=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
              (FJc_WeightValues.decode p1.x) (FJc_WeightValues.decode p1.y) j.val)))) := by
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
  have n64 : n=64#usize := by
    apply UScalar.eq_of_val_eq
    rw [hnsize,len]
    rfl
  subst n
  have cs := FJm_Filled.canonical r 64#usize scratch hfilled
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := FJj_RegularTrace.reached (FIo_Install.toWeights w)
    (FIo_Install.toSlice alpha) f 2#usize 64#usize ap0 ap1 scratch scratchOut _ before hregular
  have cs1 := FJr_KindTwoScratch.value r semAlpha z w hc hw (FIo_Install.toSlice alpha) f ap0 ap1 scratch s1 _ p1 cs h2
  obtain ⟨point0,point1,hz0,hz1,cf,vf0,vf1⟩ := FJr_ConstructorCircleRows.value semAlpha z w hc cz hw
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  obtain ⟨row0,hr0⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 3#usize (by decide)
  obtain ⟨row1,hr1⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 4#usize (by decide)
  have nr0 := FJr_NativeRow.value w cf 3#usize row0 hr0
  have nr1 := FJr_NativeRow.value w cf 4#usize row1 hr1
  let factors0 : Fin 5 → Fin 4 → FK := fun d s=>FJr_CircleOuterCell.digit
    (FJc_WeightValues.decode point0.x) (FJc_WeightValues.decode point0.y) d.val s
  let factors1 : Fin 5 → Fin 4 → FK := fun d s=>FJr_CircleOuterCell.digit
    (FJc_WeightValues.decode point1.x) (FJc_WeightValues.decode point1.y) d.val s
  have rv0 : ∀ d s,FJj_TensorPrefix.rowValue row0 d.val s.val=factors0 d s := by
    intro d s
    exact (nr0.2 d.val s.val).trans (vf0 d s)
  have rv1 : ∀ d s,FJj_TensorPrefix.rowValue row1 d.val s.val=factors1 d s := by
    intro d s
    exact (nr1.2 d.val s.val).trans (vf1 d s)
  have v5 := FJr_RegularKindMeaning.value (FIo_Install.toWeights w) variant 5#usize 3#usize
    (by decide) FJr_KindIndices.five row0 hr0 nr0.1 factors0 rv0 (FIo_Install.toSlice alpha) f
    a0 a1 ap0 ap1 ca0 ca1 hp0 hp1 s1 s2 p1 p2 cs1 h5
  have v6 := FJr_RegularKindMeaning.value (FIo_Install.toWeights w) variant 6#usize 4#usize
    (by decide) FJr_KindIndices.six row1 hr1 nr1.1 factors1 rv1 (FIo_Install.toSlice alpha) f
    a0 a1 ap0 ap1 ca0 ca1 hp0 hp1 s2 scratchOut p2 before v5.1 h6
  have tensor0 : FJd_PointReference.tensor (fun d s=>algebraMap FK FE (factors0 d s))=
      fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
        (FJc_WeightValues.decode point0.x) (FJc_WeightValues.decode point0.y) j.val) := by
    funext j
    exact FJr_CircleLiteral.mapped_tensor _ _ j
  have tensor1 : FJd_PointReference.tensor (fun d s=>algebraMap FK FE (factors1 d s))=
      fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
        (FJc_WeightValues.decode point1.x) (FJc_WeightValues.decode point1.y) j.val) := by
    funext j
    exact FJr_CircleLiteral.mapped_tensor _ _ j
  rw [tensor0] at v5
  rw [tensor1] at v6
  have carry5 := FJj_RegularFrame.value (FIo_Install.toWeights w) 6#usize (FIo_Install.toSlice alpha) f
    2#usize 64#usize ap0 ap1 s2 scratchOut p2 before h6 5 (by decide)
  have shared5 := FJm_Continuation.shared (FIo_Install.toWeights w) partials ap0 ap1 before highParts hhigh 5 (by decide) (by decide)
  have shared6 := FJm_Continuation.shared (FIo_Install.toWeights w) partials ap0 ap1 before highParts hhigh 6 (by decide) (by decide)
  have tail5 := FJm_Continuation.tail f libra highParts lowParts parts inactive hu hlib 5 (by decide) (by decide)
  have tail6 := FJm_Continuation.tail f libra highParts lowParts parts inactive hu hlib 6 (by decide) (by decide)
  exact ⟨nativeOut,a0,a1,point0,point1,parts,k,hn,he,h0,h1,hz0,hz1,hk,hsum,
    tail5.trans (shared5.trans (carry5.trans v5.2)),tail6.trans (shared6.trans v6.2)⟩

#print axioms value
end AspisR1.FJr_CircleParts
end
