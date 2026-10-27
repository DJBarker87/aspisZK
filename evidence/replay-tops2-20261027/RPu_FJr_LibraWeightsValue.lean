import RPu_FJr_LibraZero
import RPu_FJr_LibraOne
import RPu_FJr_LibraLoopCuts
import RPu_FIo_GroupCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraWeightsValue
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide)
open FJr_LibraFactors (FK FE)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (extra : Array NQ 2#usize)
    (ca0 : FIo_WideValues.Canon a0) (ca1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (ce : ∀ q∈extra.val,FIo_QMValues.Canon q) (out : Array NE 4#usize)
    (run : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 extra=ok out) :
    FIo_ArrayCanon.Holds out ∧ ∀ j : Fin 4,FIp_ArrayValue.value out j.val=
      FJm_LibraModel.part (algebraMap FK FE (FJf_QMArray.value extra 0))
        (algebraMap FK FE (FJf_QMArray.value extra 1)) (decodeWide (wide a0)) (decodeWide (wide a1)) j := by
  unfold FIo_Native.weights.factored_s2_libra_weights at run
  obtain ⟨it1,w1,b0,r1⟩ := FJr_LibraLoopCuts.head ap0 ap1 extra _ _ out (by change (0:Nat)<2;decide) run
  have v0 := FJr_LibraZero.value a0 a1 ap0 ap1 extra ca0 ca1 hp0 hp1 ce _ it1 _ w1
    (FIo_GroupCanonical.zeros _) rfl b0
  have s1 : it1.start=1#usize := UScalar.eq_of_val_eq v0.2.1
  have e1 : it1.end.val=2 := congrArg UScalar.val v0.1
  obtain ⟨it2,w2,b1,r2⟩ := FJr_LibraLoopCuts.head ap0 ap1 extra it1 w1 out (by omega) r1
  have v1 := FJr_LibraOne.value a0 a1 ap0 ap1 extra ca0 ca1 hp0 hp1 ce it1 it2 w1 w2 v0.2.2.1 s1 b1
  have same := FJr_LibraLoopCuts.stopped ap0 ap1 extra it2 w2 out (by rw [v1.1];omega) r2
  subst out
  refine ⟨v1.2.2.1,?_⟩
  intro j
  fin_cases j <;>
    simp [v1.2.2.2,v0.2.2.2,FJm_LibraModel.part]

#print axioms value
end AspisR1.FJr_LibraWeightsValue
end
