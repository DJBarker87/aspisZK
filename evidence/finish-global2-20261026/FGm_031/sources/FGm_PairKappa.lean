import FGm_PowersValue
import FGm_PairSumVariants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PairKappa
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode value)
open scoped BigOperators

/-- Actual powers then actual final sum; no model weights assumption is hidden
in this local source-value result. The seven source parts remain explicit. -/
theorem value (parts : Array NE 7#usize) (kappa : NE) (out : NE)
    (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_WideValues.Canon kappa)
    (run : (do
      let k ← FIo_Native.weights.powers 7#usize kappa
      FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok out) :
    FIo_WideValues.Canon out ∧ decode out=
      ∑ i ∈ Finset.range 7, decode kappa^i * value parts i := by
  obtain ⟨k,hkRun,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have kp := FGm_PowersValue.value 7#usize kappa k hk hkRun
  have sum := FGm_PairSum.value parts k out hp kp.1 run
  refine ⟨sum.1,?_⟩
  rw [sum.2]
  unfold FGm_PairSumStep.prefixSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [kp.2 i (Finset.mem_range.mp hi)]

#print axioms value
end AspisR1.FGm_PairKappa
end
