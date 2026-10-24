import S9ActualKappaFinalSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9KappaFinSevenV1
open AspisR1S9ActualKappaFinalSumV1
open AspisR1S9ActualFinalSumV1 (A)
abbrev W := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)

/-- A Fin7 source read uses the actual parts array length witness directly;
there is no machine-index construction or hidden Usize bound parameter. -/
def partAt (parts : A) (i : Fin 7) : W :=
  parts.val[i.val]'(by rw [parts.property];exact i.isLt)

/-- Source Nat-range polynomial and Fin7 polynomial use the SAME terms. -/
theorem kappaPolynomial_eq_fin_terms (parts : A) (kappa : W) :
    kappaPolynomial parts kappa=∑ i : Fin 7,kappaTerm parts kappa i.val := by
  exact (Fin.sum_univ_eq_sum_range (kappaTerm parts kappa) 7).symm

/-- The bounded source term is its own exact native array read. -/
theorem kappaTerm_fin (parts : A) (kappa : W) (i : Fin 7) :
    kappaTerm parts kappa i.val=decode kappa^i.val*decode (partAt parts i) := by
  simp only [kappaTerm,dif_pos i.isLt,partAt]

/-- Exact ordinary Fin7 polynomial of the SAME source parts; arbitrary
native carriers are allowed and no canonicality or desired meaning is assumed. -/
theorem kappaPolynomial_eq_fin_parts (parts : A) (kappa : W) :
    kappaPolynomial parts kappa=∑ i : Fin 7,decode kappa^i.val*decode (partAt parts i) := by
  rw [kappaPolynomial_eq_fin_terms]
  exact Finset.sum_congr rfl (fun i _ => kappaTerm_fin parts kappa i)

#print axioms kappaPolynomial_eq_fin_terms
#print axioms kappaTerm_fin
#print axioms kappaPolynomial_eq_fin_parts
end AspisR1S9KappaFinSevenV1
