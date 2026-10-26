import FIq_S_RawGenericPolynomialSumcheckChain
set_option autoImplicit false
namespace AspisR1.FIr_Chain
open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain

theorem adjacent {K : Type} [CommSemiring K] {start target : K}
    {xs : List (Polynomial K × K)} (chain : Chain start target xs)
    (i : Nat) (bound : i+1<xs.length) :
    xs[i+1].1.eval 0+xs[i+1].1.eval 1=xs[i].1.eval xs[i].2 := by
  induction chain generalizing i with
  | nil => simp only [List.length_nil] at bound;omega
  | @cons p q rest start mid target degree boundary next tail ih =>
    cases i with
    | zero =>
      cases tail with
      | nil => simp only [List.length_cons,List.length_nil] at bound;omega
      | @cons p' q' rest' mid next' target degree' boundary' nextEq' tail' =>
        simpa only [List.getElem_cons_zero,List.getElem_cons_succ] using boundary'.trans next
    | succ i =>
      have h : i+1<rest.length := by simpa only [List.length_cons,Nat.succ_add,Nat.succ_lt_succ_iff] using bound
      simpa only [List.getElem_cons_succ,Nat.succ_eq_add_one] using ih i h

theorem last_value {K : Type} [CommSemiring K] {start target : K}
    {xs : List (Polynomial K × K)} (chain : Chain start target xs)
    (i : Nat) (last : i+1=xs.length) :
    (xs[i]'(by omega)).1.eval (xs[i]'(by omega)).2 = target := by
  induction chain generalizing i with
  | nil => simp only [List.length_nil] at last;omega
  | @cons p q rest start mid target degree boundary next tail ih =>
    cases i with
    | zero =>
      have len : rest.length=0 := by simp only [List.length_cons] at last;omega
      have empty := List.eq_nil_of_length_eq_zero len
      subst rest
      cases tail
      exact next.symm
    | succ i =>
      have h : i+1=rest.length := by simp only [List.length_cons] at last;omega
      simpa only [List.getElem_cons_succ] using ih i h

#print axioms adjacent
#print axioms last_value
end AspisR1.FIr_Chain
