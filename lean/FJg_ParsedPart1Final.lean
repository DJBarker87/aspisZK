import FJg_Part1Final
import FJg_ReadSemanticCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ParsedPart1Final
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE)
/-- The SAME strict native semantic-array result supplies constructor-alpha
canonicality. Every original source operand/call observation is retained in
the conclusion. The enclosing reader cut is still explicit. -/
theorem value (bytes : Slice U8) (start stop : Usize) (semAlpha : Array K 10#usize)
    (read : (T2Nat_ReaderOps.ops true).readSemanticAlpha bytes start=ok (.Ok (semAlpha,stop)))
    (r : NP6_StdModel.Reservation)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
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
  exact FJg_Part1Final.value r semAlpha z w alpha f kappa out
    (FJg_ReadSemanticCanon.native true bytes start stop semAlpha read) hw folds len halpha run
#print axioms value
end AspisR1.FJg_ParsedPart1Final
end
