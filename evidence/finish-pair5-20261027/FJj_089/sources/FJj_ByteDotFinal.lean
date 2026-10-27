import FJj_ByteDotLoop
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_ByteDotFinal
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators

theorem sumPrefix (f : Slice U8) (scratch : Slice NQ) (n : Nat) :
    FJj_ByteDotCell.sumPrefix f scratch n=∑ j∈Finset.range n,FJj_ByteDotCell.term f scratch j := by
  induction n with
  | zero => simp only [FJj_ByteDotCell.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJj_ByteDotCell.sumPrefix,Finset.sum_range_succ,ih]

theorem value (f : Slice U8) (scratch : Slice NQ) (hc : FJj_QMSlice.canon scratch)
    (dot out : FIo_Native.fast_pairing.EbyKDot) (result : NE)
    (new : FIo_Native.fast_pairing.EbyKDot.new=ok dot)
    (run : FIo_Native.weights.push_byte_products dot f scratch 64#usize=ok (.Ok (),out))
    (finish : FIo_Native.fast_pairing.EbyKDot.finish out=ok result) :
    FIo_WideValues.Canon result ∧ decodeWide (wide result)=
      ∑ j : Fin 64,FJc_InactiveCoefficientsModel.field f j.val*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJj_QMSlice.value scratch j.val) := by
  have loopValue := FJj_ByteDotLoop.value f scratch hc dot out new run
  have finalValue := FJf_EbyKFinish.value out result finish
  refine ⟨finalValue.1,?_⟩
  rw [finalValue.2,loopValue.2.2,sumPrefix,←Fin.sum_univ_eq_sum_range]
  rfl
#print axioms sumPrefix
#print axioms value
end AspisR1.FJj_ByteDotFinal
end
