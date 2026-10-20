import Aeneas
import QueryValidatorLoopInvariant
import QueryValidateQueriesSuccessNoTotality
open Aeneas Aeneas.Std AspisR1Stage2AdoptedResume
namespace AspisR1.QueryValidatorFinalFacts
abbrev QueryArray := Array Std.U32 22#usize
open AspisR1.QueryValidatorLoopInvariant

def queryValueList (queries : QueryArray) : List Nat :=
  List.ofFn (fun i : Fin 22 => (queries.val[i.val]!).val)

theorem all_validAt_range_pairwise
    (queries : QueryArray)
    (hvalid : ∀ i : Usize, i.val < 22 → validAt queries i) :
    (∀ i : Nat, i < 22 → queryValue queries i < 2 ^ 18) ∧
      List.Pairwise (fun x y : Nat => x ≠ y) (queryValueList queries) := by
  constructor
  · intro i hi
    let ui : Usize := UScalar.ofNatCore .Usize i (by omega)
    have huv : ui.val = i := by simp [ui, UScalar.ofNatCore_val_eq]
    have h := hvalid ui (by rw [huv]; exact hi)
    exact h.2.1
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [queryValueList, List.getElem_ofFn]
    let uj : Usize := UScalar.ofNatCore .Usize j (by omega)
    have huv : uj.val = j := by simp [uj, UScalar.ofNatCore_val_eq]
    have h := hvalid uj (by rw [huv]; exact hj)
    exact h.2.2 i (by omega)

/-- The actual verifier success exposes the all-slot range and pairwise-distinct query values. -/
theorem validate_queries_success_range_pairwise
    (queries : QueryArray)
    (hvalidate : verifier.validate_queries queries = ok (core.result.Result.Ok ())) :
    (∀ i : Nat, i < 22 → queryValue queries i < 2 ^ 18) ∧
      List.Pairwise (fun x y : Nat => x ≠ y) (queryValueList queries) := by
  have hall := AspisR1.QueryValidateQueriesSuccessNoTotality.validate_queries_success_sound
    queries hvalidate
  exact all_validAt_range_pairwise queries hall

#print axioms validate_queries_success_range_pairwise
end AspisR1.QueryValidatorFinalFacts
