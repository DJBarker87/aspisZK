import FJc_InstalledFinalPart0
import FJc_ExpandedInactive
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InstalledExpandedPart0
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE)
open scoped BigOperators
/-- Arithmetic row formula for actual installed final part0. The native row-
permutation/literal model and global parse joins remain explicit future work. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut : NE) (low : Array NE 16#usize) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧ FIo_ArrayCanon.Holds low ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 0=
        ∑ j : Fin 64,∑ s : Fin 16, if FJc_S2Rows.inactive j.val s.val then
          FJc_InactiveCoefficientsModel.field f j.val*FIp_ArrayValue.value low s.val else 0 := by
  obtain ⟨nativeOut,low,parts,k,hn,he,hc,hk,hsum,hvalue⟩ :=
    FJc_InstalledFinalPart0.value r semAlpha z w alpha f kappa out hw folds len halpha run
  exact ⟨nativeOut,low,parts,k,hn,he,hc,hk,hsum,hvalue.trans (FJc_ExpandedInactive.arithmetic_row f low)⟩
#print axioms value
end AspisR1.FJc_InstalledExpandedPart0
end
