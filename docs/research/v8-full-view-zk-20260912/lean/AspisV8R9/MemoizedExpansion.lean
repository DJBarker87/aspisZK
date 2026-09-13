import AspisV8PairedCommitment.ShadowTable

/-! A new tape value belongs to an address, not a call. This is a cache
identity, not a real-seed pseudorandomness theorem. -/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem query_result_is_cached (t : Table I A) (i : I) (fresh : A) :
    (queryStep t i fresh).2 i = some (queryStep t i fresh).1 := by
  cases old : t i with
  | none => simp [queryStep, old, put]
  | some a => simp [queryStep, old]

theorem repeated_derivation_same_answer (t : Table I A) (i : I) (a b : A) :
    queryStep (queryStep t i a).2 i b =
      ((queryStep t i a).1, (queryStep t i a).2) := by
  cases old : t i with
  | none => simp [queryStep, old, put]
  | some prior => simp [queryStep, old]

theorem distinct_derivation_address_preserves_old (t : Table I A)
    (i j : I) (fresh old : A) (different : i ≠ j) (cached : t i = some old) :
    (queryStep t j fresh).2 i = some old := by
  cases found : t j with
  | none => simp [queryStep, found, put, different, cached]
  | some a => simp [queryStep, found, cached]

#print axioms query_result_is_cached
#print axioms repeated_derivation_same_answer
#print axioms distinct_derivation_address_preserves_old
end AspisV8R9
