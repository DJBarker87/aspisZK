import S9ConstructorV3VectorMeaningV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3DecodedInputV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1

/-- Total semantic lookup, with a harmless zero outside the ten source words. -/
def decodedInput (z : Vector) (i : Nat) : ExactQM :=
  match z.val[i]? with | none => 0 | some q => decode q

/-- The input-value interface is derived from actual Array.index_usize,
not supplied as a separate premise about the point producer. -/
theorem decoded_input_meaning (z : Vector) : Meaning z (decodedInput z) := by
  intro i q hread
  unfold Array.index_usize at hread
  cases hget : z[i]? with
  | none => simp [hget] at hread
  | some value =>
    have heq : value=q := by
      simpa only [hget,Result.ok.injEq] using hread
    have hlist : z.val[i.val]?=some value := by simpa using hget
    subst q
    simp only [decodedInput,hlist]

#print axioms decoded_input_meaning
end AspisR1S9ConstructorV3DecodedInputV1
