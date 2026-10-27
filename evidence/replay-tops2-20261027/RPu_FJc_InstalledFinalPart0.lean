import RPu_FJc_InactiveFinalValue
import RPt_FJc_InstalledParts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InstalledFinalPart0
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE)
/-- Value of part0 in the SAME final array consumed by the installed Pair's
actual final sum. Local parse-shape/alpha canonicality still require global joins. -/
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
      FIp_ArrayValue.value parts 0=FJc_InactiveValue.sumPrefix f low 12 := by
  obtain ⟨points,a8,a9,f1,f2,hp,h8,h9,hf1,hf2,hvariant,rest⟩ :=
    FJc_InstalledParts.value .S2 semAlpha z w hw
  have variant : (FIo_Install.toWeights w).variant=.S2 := hvariant
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨low,parts,k,hc,hk,hsum,hvalue⟩ :=
    @FJc_InactiveFinalValue.value (FIo_Install.allocation r) (FIo_Install.toWeights w)
      (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut folds variant len halpha hn
  exact ⟨nativeOut,low,parts,k,hn,he,hc,hk,hsum,hvalue⟩
#print axioms value
end AspisR1.FJc_InstalledFinalPart0
end
