import NDO_JHm_HornerStep
import CurrentClaimSourceAggregation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Polynomial
open Aeneas Aeneas.Std
open JHm_Arithmetic

/-- Ordered source trace converted to a finite sum, without evaluating its source. -/
theorem ordered_sum {T : Type} (xs : List T) (index : T → Nat) (f : T → FE)
    (n : Nat) (hlen : xs.length=n) (order : ∀ j (hj : j<xs.length),index xs[j]=j)
    (term : Nat → FE) (value : ∀ t∈xs,f t=term (index t)) :
    (xs.map f).sum=∑ j : Fin n,term j.val := by
  have same : xs.map f=List.ofFn (fun j : Fin n => term j.val) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_ofFn,hlen]
    · intro j hj hk
      simp only [List.getElem_map,List.getElem_ofFn]
      rw [value _ (List.getElem_mem _),order]
  rw [same,List.sum_ofFn]
#print axioms ordered_sum

/-- Horner evaluation equals the original increasing-power dot. -/
theorem horner_sum (g : FE) (xs : List FE) :
    horner g xs=∑ j : Fin xs.length,g^j.val*xs[j.val] := by
  induction xs with
  | nil => simp [horner]
  | cons x xs ih =>
    rw [horner,ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,List.getElem_cons_zero,Fin.val_succ,
      List.getElem_cons_succ,pow_succ]
    rw [Finset.mul_sum]
    apply congrArg (fun z : FE => x+z)
    apply Finset.sum_congr rfl
    intro j hj
    exact (mul_assoc g (g^j.val) xs[j.val]).symm.trans
      (congrArg (fun z : FE => z*xs[j.val]) (mul_comm g (g^j.val)))
#print axioms horner_sum
end AspisR1.JHm_Polynomial
end
