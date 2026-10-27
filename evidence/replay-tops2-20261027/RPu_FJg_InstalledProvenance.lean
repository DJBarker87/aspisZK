import RPu_FJg_PairProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_InstalledProvenance
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
/-- Installed Pair's own common operands, with the existing constructor and
shared16 VALUES. The fallback alternative is explicit and not assumed away. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    FIo_Native.weights.shared_two_point_guard (FIo_Install.toWeights w) 2#usize=ok false ∨
    ∃ (ap0 ap1 : Array NE 4#usize) (common : Array NQ 16#usize)
      (partials : Array NE 4#usize) (before after : Array NE 7#usize),
      FIo_Native.weights.shared_two_point_guard (FIo_Install.toWeights w) 2#usize=ok true ∧
      FJf_QMArray.canon common ∧
      (∀ j,j<16 → FJf_QMArray.value common j=
        FJf_CommonCell.model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) j) ∧
      FIo_Native.weights.shared_partials f common=ok (.Ok partials) ∧
      FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after) := by
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  rcases @FJg_PairProvenance.reached (FIo_Install.allocation r) (FIo_Install.toWeights w)
      (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut folds hn with hfalse|hshared
  · exact Or.inl hfalse
  · right
    obtain ⟨a0,a1,ap0,ap1,common,nativeSelf,status,partials,before,after,
      hg,h0,hp0,h1,hp1,hcom,same,hpart,hhigh,hs⟩ := hshared
    have cv := FJf_CommonValue.sixteen semAlpha z w hc hw (nativeSelf,common) hcom
    subst nativeSelf
    subst status
    exact ⟨ap0,ap1,common,partials,before,after,hg,cv.2.1,cv.2.2,hpart,hhigh⟩
#print axioms value
end AspisR1.FJg_InstalledProvenance
end
