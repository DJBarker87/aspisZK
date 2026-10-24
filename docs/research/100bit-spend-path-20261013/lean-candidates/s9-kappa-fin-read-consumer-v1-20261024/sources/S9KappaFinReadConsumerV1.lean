import S9KappaFinSevenV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9KappaFinReadConsumerV1
open AspisR1S9KappaFinSevenV1
open AspisR1S9ActualFinalSumV1 (A)
open AspisR1S9ActualKappaFinalSumV1 (kappaPolynomial)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)
abbrev E := AspisWideTower.WideExact

/-- Same actual array/list read, independent of the proof of its bound. -/
theorem partAt_eq_atN (parts : A) (i : Fin 7) (j : Usize)
    (hj : j.val<7) (hji : j.val=i.val) :
    partAt parts i=AspisR1S9FactorArrayEntryV1.atN parts j hj := by
  simp only [partAt,AspisR1S9FactorArrayEntryV1.atN,hji]

/-- Symbolic value substitution in the SAME source-part polynomial. All
part meanings remain explicit; no concrete seven-cell sum is unfolded. -/
theorem kappaPolynomial_eq_fin_values (parts : A) (kappa : W)
    (v : Fin 7 → E) (hvalues : ∀ i,decode (partAt parts i)=v i) :
    kappaPolynomial parts kappa=∑ i : Fin 7,decode kappa^i.val*v i := by
  rw [kappaPolynomial_eq_fin_parts]
  exact Finset.sum_congr rfl (fun i _ =>
    congrArg (fun t : E => decode kappa^i.val*t) (hvalues i))

#print axioms partAt_eq_atN
#print axioms kappaPolynomial_eq_fin_values
end AspisR1S9KappaFinReadConsumerV1
