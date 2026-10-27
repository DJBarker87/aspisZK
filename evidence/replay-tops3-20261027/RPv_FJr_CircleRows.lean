import RPu_FJr_CircleOuterCell
import RPv_FJr_CircleOuterCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleRows
open Aeneas Aeneas.Std Result
open FJc_WeightValues (decode)
open FJf_PointBody (Factors)
open FJf_CircleOuterBody (Z)
open FJf_FactorArray (canon value)

theorem value (z : Z) (cz : FJr_CircleOuterCell.CanonZ z)
    (p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint)
    (hp0 : Array.index_usize z 0#usize=ok p0) (hp1 : Array.index_usize z 1#usize=ok p1)
    (factors out : Factors) (hf : canon factors)
    (run : FIn_WeightsExtract.weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors=ok out) :
    canon out ∧
      (∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value out 3 d.val s.val=
        FJr_CircleOuterCell.digit (decode p0.x) (decode p0.y) d.val s) ∧
      (∀ (d : Fin 5) (s : Fin 4),FJf_FactorArray.value out 4 d.val s.val=
        FJr_CircleOuterCell.digit (decode p1.x) (decode p1.y) d.val s) := by
  obtain ⟨it1,f1,hb0,hr1⟩ := FJr_CircleOuterCuts.head z _ factors out (by change (0:Nat)<2;decide) run
  obtain ⟨k0,q0,hk0,he0,hs0,more0,hq0,cf1,v0⟩ := FJr_CircleOuterCell.value z cz _ it1 factors f1 hf rfl hb0
  have ek0 : k0=0#usize := hk0
  rw [ek0] at hq0 v0
  have ep0 : q0=p0 := Result.ok.inj (hq0.symm.trans hp0)
  subst q0
  have s1 : it1.start.val=1 := hs0
  have e1 : it1.end.val=2 := congrArg UScalar.val he0
  obtain ⟨it2,f2,hb1,hr2⟩ := FJr_CircleOuterCuts.head z it1 f1 out (by omega) hr1
  obtain ⟨k1,q1,hk1,he1,hs1,more1,hq1,cf2,v1⟩ := FJr_CircleOuterCell.value z cz it1 it2 f1 f2 cf1 e1 hb1
  have ek1 : k1=1#usize := by apply UScalar.eq_of_val_eq;rw [hk1];exact s1
  rw [ek1] at hq1 v1
  have ep1 : q1=p1 := Result.ok.inj (hq1.symm.trans hp1)
  subst q1
  have same := FJr_CircleOuterCuts.stopped z it2 f2 out (by rw [he1];omega) hr2
  subst out
  refine ⟨cf2,?_,?_⟩
  · intro d s
    rw [v1 3 d.val s,v0 3 d.val s]
    simp only [show (1#usize).val=1 from by decide,show (0#usize).val=0 from by decide,
      show ¬(3+1:Nat)=3 from by decide,show (3+0:Nat)=3 from by decide,
      false_and,true_and,if_false,if_pos d.isLt]
  · intro d s
    rw [v1 4 d.val s]
    simp only [show (1#usize).val=1 from by decide,show (3+1:Nat)=4 from by decide,
      true_and,if_pos d.isLt]

#print axioms value
end AspisR1.FJr_CircleRows
end
