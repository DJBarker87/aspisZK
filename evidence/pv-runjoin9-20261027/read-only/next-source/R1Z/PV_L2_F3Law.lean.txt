import R1Z.PV_L2_F3CountedFibres
import R0Z.LawTransport

/-! Joint value/history law from conditional successful fibres. No marginal
uniformity inference is used, and decode failures are fixed, not resampled. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Law
open R0Z
attribute [local instance] Classical.propDecidable
variable {Input A H : Type} [Fintype Input]

theorem law_card (f : Input → A) (a : A) :
    law f a = ((Finset.univ.filter (fun i => f i = a)).card : ℚ) / Fintype.card Input := by
  simp only [law,mean,Finset.sum_boole]

/-- An arbitrary value permutation may depend on the retained history. This
includes a full-tape bijection, not merely coordinatewise scalar changes. -/
theorem conditional_relabel (decode : Input → Option (A × H))
    (fibres : ∀ h a b,
      (Finset.univ.filter (fun i => decode i = some (a,h))).card =
        (Finset.univ.filter (fun i => decode i = some (b,h))).card)
    (e : H → A ≃ A) :
    EqualLaws (fun i => (decode i).map (fun p => (e p.2 p.1,p.2))) decode := by
  intro out
  cases out with
  | none =>
    unfold law mean
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    cases hd : decode i <;> simp only [hd,Option.map_none,Option.map_some,reduceCtorEq,ite_true,ite_false]
  | some out =>
    rcases out with ⟨a,h⟩
    have heq : (Finset.univ.filter (fun i =>
      (decode i).map (fun p => (e p.2 p.1,p.2)) = some (a,h))) =
        Finset.univ.filter (fun i => decode i = some ((e h).symm a,h)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      cases hd : decode i with
      | none => simp only [Option.map_none,reduceCtorEq]
      | some p =>
        rcases p with ⟨b,j⟩
        by_cases hj : j=h
        · subst j
          simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,and_true]
          exact (e h).apply_eq_iff_eq_symm_apply
        · simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,hj,and_false]
    rw [law_card,law_card]
    apply congrArg (fun n : Nat => (n : ℚ) / Fintype.card Input)
    calc
      _ = (Finset.univ.filter (fun i => decode i = some ((e h).symm a,h))).card := by
        convert congrArg Finset.card heq using 1 <;> apply congrArg Finset.card <;>
          ext i <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      _ = _ := by
        convert fibres h ((e h).symm a) a using 1 <;> apply congrArg Finset.card <;>
          ext i <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem conditional_test (decode : Input → Option (A × H))
    (fibres : ∀ h a b,
      (Finset.univ.filter (fun i => decode i = some (a,h))).card =
        (Finset.univ.filter (fun i => decode i = some (b,h))).card)
    (e : H → A ≃ A) (test : Option (A × H) → ℚ) :
    mean (fun i => test ((decode i).map (fun p => (e p.2 p.1,p.2)))) =
      mean (fun i => test (decode i)) :=
  LawTransport.mean_eq_of_equalLaws _ _ test (conditional_relabel decode fibres e)

#print axioms law_card
#print axioms conditional_relabel
#print axioms conditional_test
end R1Z.PV_L2_F3Law
