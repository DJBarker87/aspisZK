import FJr_LibraWeightsValue
import FJr_LibraContraction
import FJr_SparseDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide)
open FJr_LibraFactors (FK FE)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (a0 a1 : NE) (ap0 ap1 libra : Array NE 4#usize) (extra : Array NQ 2#usize)
    (ca0 : FIo_WideValues.Canon a0) (ca1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q)
    (hl : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra=ok libra)
    (f : Slice U8) (before out : Array NE 7#usize)
    (zero : before.val[4]?=some FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)
    (run : FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f before libra=ok out) :
    FIp_ArrayValue.value out 4=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (FJm_LibraModel.folded (algebraMap FK FE (FJf_QMArray.value extra 0))
        (algebraMap FK FE (FJf_QMArray.value extra 1)) (decodeWide (wide a0)) (decodeWide (wide a1))) := by
  have weights := FJr_LibraWeightsValue.value a0 a1 ap0 ap1 extra ca0 ca1 hp0 hp1 ce libra hl
  have contraction := FJr_LibraContraction.value f libra weights.1 before out zero run
  rw [contraction,FJr_LibraContraction.sumPrefix_sum,←Fin.sum_univ_eq_sum_range,FJr_SparseDot.value]
  apply Finset.sum_congr rfl
  intro j _
  unfold FJr_LibraContraction.term
  rw [weights.2 j]

#print axioms value
end AspisR1.FJr_LibraMeaning
end
