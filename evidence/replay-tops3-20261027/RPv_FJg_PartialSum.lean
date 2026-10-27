import RPv_FJg_PartialsValue
import RPv_FJf_PartialReference
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_PartialSum
open Aeneas Aeneas.Std
open FIo_FieldBridge (NQ NE)
open scoped BigOperators

theorem value (f : Slice U8) (common : Array NQ 16#usize) (p : Array NE 4#usize)
    (hv : FJg_PartialsValue.Values f common p 4) (i : Fin 4) :
    FIp_ArrayValue.value p i.val=∑ j : Fin 16,
      FJc_InactiveCoefficientsModel.field f (16*i.val+j.val)*
        algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (FJf_QMArray.value common j.val) := by
  let s : Usize := Usize.ofNat i.val (by have := i.isLt;scalar_tac)
  have hs : s.val=i.val := by dsimp only [s];rfl
  have src := hv s (by rw [hs];exact i.isLt)
  rw [hs] at src
  have sums : FJf_PartialCell.sumPrefix f common s 16=
      ∑ j : Fin 16,FJf_PartialCell.term f common s j.val := by
    rw [FJf_PartialReference.sumPrefix,Fin.sum_univ_eq_sum_range]
  rw [src,sums]
  apply Finset.sum_congr rfl
  intro j hj
  unfold FJf_PartialCell.term
  rw [hs]
  rfl
#print axioms value
end AspisR1.FJg_PartialSum
end
