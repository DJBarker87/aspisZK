import Aeneas
import QueryValidatorLoopInvariant
import QueryValidateQueriesSuccessNoTotality
open Aeneas Aeneas.Std Result AspisR1Stage2AdoptedResume
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
  have hwidth : 22 < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  constructor
  · intro i hi
    let ui : Usize := @UScalar.ofNatCore .Usize i (Nat.lt_trans hi hwidth)
    have huv : ui.val = i := by simp only [ui, UScalar.ofNatCore_val_eq]
    have h := hvalid ui (by rw [huv]; exact hi)
    simpa [queryValue, huv] using h.2.1
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hlen : (queryValueList queries).length = 22 := by simp [queryValueList]
    have hi22 : i < 22 := by simpa [hlen] using hi
    have hj22 : j < 22 := by simpa [hlen] using hj
    simp only [queryValueList, List.getElem_ofFn]
    let uj : Usize := @UScalar.ofNatCore .Usize j (Nat.lt_trans hj22 hwidth)
    have huv : uj.val = j := by simp only [uj, UScalar.ofNatCore_val_eq]
    have h := hvalid uj (by rw [huv]; exact hj22)
    simpa [queryValue, huv] using h.2.2 i (by omega)

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
