import RPu_FJg_InstalledProvenance
import RPu_FJg_SharedGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_SharedProvenance
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
/-- The SAME installed two-fold Pair selects the shared path. All common and
partial call operands are derived from this run; fallback is impossible. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (ap0 ap1 : Array NE 4#usize) (common : Array NQ 16#usize)
      (partials : Array NE 4#usize) (before after : Array NE 7#usize),
      FIo_Native.weights.shared_two_point_guard (FIo_Install.toWeights w) 2#usize=ok true ∧
      FJf_QMArray.canon common ∧
      (∀ j,j<16 → FJf_QMArray.value common j=
        FJf_CommonCell.model (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha) j) ∧
      FIo_Native.weights.shared_partials f common=ok (.Ok partials) ∧
      FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after) := by
  rcases FJg_InstalledProvenance.value r semAlpha z w alpha f kappa out hc hw folds run with hfalse|hshared
  · have bad := FJg_SharedGuard.result semAlpha z w hw false hfalse
    cases bad
  · exact hshared
#print axioms value
end AspisR1.FJg_SharedProvenance
end
