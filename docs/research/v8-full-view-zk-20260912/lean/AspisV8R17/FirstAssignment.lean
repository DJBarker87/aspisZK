import AspisV8R9.MemoizedExpansion

/-! Pathwise provenance of cached oracle answers. A realized call list may
come from an adaptive execution; no distribution on that list is assumed.
First-assignment probability and source refinement remain separate gates. -/
set_option autoImplicit false
namespace AspisV8R17
open AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

def runQueries (t : Table I A) : List (I × A) → Table I A
  | [] => t
  | (i,a)::rest => runQueries (queryStep t i a).2 rest

def firstAssignments (t : Table I A) : List (I × A) → List (I × A)
  | [] => []
  | (i,a)::rest =>
      let tail := firstAssignments (queryStep t i a).2 rest
      match t i with
      | none => (i,a)::tail
      | some _ => tail

theorem query_lookup_origin (t : Table I A) (input : I) (fresh : A)
    (i : I) (a : A) (h : (queryStep t input fresh).2 i = some a) :
    t i = some a ∨ (t input = none ∧ i=input ∧ a=fresh) := by
  cases found : t input with
  | some old => exact Or.inl (by simpa [queryStep,found] using h)
  | none =>
      by_cases hi : i=input
      · subst i
        have ha : fresh=a := by simpa [queryStep,found,put] using h
        exact Or.inr ⟨rfl,rfl,ha.symm⟩
      · exact Or.inl (by simpa [queryStep,found,put,hi] using h)

theorem runQueries_lookup_origin (calls : List (I × A)) (t : Table I A)
    (i : I) (a : A) (h : runQueries t calls i = some a) :
    t i = some a ∨ (i,a) ∈ firstAssignments t calls := by
  induction calls generalizing t with
  | nil => exact Or.inl h
  | cons call rest ih =>
      rcases call with ⟨input,fresh⟩
      obtain hold | hnew := ih (queryStep t input fresh).2 h
      · obtain original | ⟨missing,rfl,rfl⟩ := query_lookup_origin t input fresh i a hold
        · exact Or.inl original
        · exact Or.inr (by simp [firstAssignments,missing])
      · apply Or.inr
        cases found : t input <;> simp [firstAssignments,found,hnew]

theorem firstAssignments_length (calls : List (I × A)) (t : Table I A) :
    (firstAssignments t calls).length ≤ calls.length := by
  induction calls generalizing t with
  | nil => exact Nat.le_refl _
  | cons call rest ih =>
      rcases call with ⟨input,fresh⟩
      have ht := ih (queryStep t input fresh).2
      cases found : t input <;> simp only [firstAssignments,found,List.length_cons] <;> omega

theorem empty_run_answer_assigned (calls : List (I × A)) (i : I) (a : A)
    (h : runQueries (fun _ => none) calls i = some a) :
    (i,a) ∈ firstAssignments (fun _ => none) calls := by
  obtain old | assigned := runQueries_lookup_origin calls (fun _ => none) i a h
  · cases old
  · exact assigned

theorem selected_bad_answer_origin (Bad : I → A → Prop)
    (calls : List (I × A)) (t : Table I A) (i : I) (a : A)
    (selected : runQueries t calls i = some a) (bad : Bad i a) :
    (∃ j b, t j = some b ∧ Bad j b) ∨
      ∃ pair ∈ firstAssignments t calls, Bad pair.1 pair.2 := by
  obtain old | assigned := runQueries_lookup_origin calls t i a selected
  · exact Or.inl ⟨i,a,old,bad⟩
  · exact Or.inr ⟨(i,a),assigned,bad⟩

theorem public_prequery_charged_once (i : I) (a ignored : A) :
    firstAssignments (fun _ => none) [(i,a),(i,ignored)] = [(i,a)] := by
  simp [firstAssignments,queryStep,put]

def queryAnswers (t : Table I A) : List (I × A) → List (I × A)
  | [] => []
  | (i,a)::rest =>
      (i,(queryStep t i a).1)::queryAnswers (queryStep t i a).2 rest

theorem query_preserves_cache (t : Table I A) (input : I) (fresh : A)
    (i : I) (a : A) (cached : t i = some a) :
    (queryStep t input fresh).2 i = some a := by
  by_cases hi : i=input
  · subst i
    simpa [queryStep,cached] using cached
  · exact AspisV8R9.distinct_derivation_address_preserves_old t i input fresh a hi cached

theorem runQueries_preserves_cache (calls : List (I × A)) (t : Table I A)
    (i : I) (a : A) (cached : t i = some a) : runQueries t calls i = some a := by
  induction calls generalizing t with
  | nil => exact cached
  | cons call rest ih =>
      exact ih (queryStep t call.1 call.2).2
        (query_preserves_cache t call.1 call.2 i a cached)

theorem returned_answer_persists (calls : List (I × A)) (t : Table I A)
    (pair : I × A) (returned : pair ∈ queryAnswers t calls) :
    runQueries t calls pair.1 = some pair.2 := by
  induction calls generalizing t with
  | nil => simp [queryAnswers] at returned
  | cons call rest ih =>
      rcases call with ⟨input,fresh⟩
      obtain head | tail := List.mem_cons.mp returned
      · subst pair
        exact runQueries_preserves_cache rest (queryStep t input fresh).2 input _
          (AspisV8R9.query_result_is_cached t input fresh)
      · exact ih (queryStep t input fresh).2 tail

theorem returned_bad_answer_origin (Bad : I → A → Prop)
    (calls : List (I × A)) (t : Table I A) (pair : I × A)
    (returned : pair ∈ queryAnswers t calls) (bad : Bad pair.1 pair.2) :
    (∃ j b, t j = some b ∧ Bad j b) ∨
      ∃ assigned ∈ firstAssignments t calls, Bad assigned.1 assigned.2 :=
  selected_bad_answer_origin Bad calls t pair.1 pair.2
    (returned_answer_persists calls t pair returned) bad

#print axioms query_preserves_cache
#print axioms runQueries_preserves_cache
#print axioms returned_answer_persists
#print axioms returned_bad_answer_origin
#print axioms query_lookup_origin
#print axioms runQueries_lookup_origin
#print axioms firstAssignments_length
#print axioms empty_run_answer_assigned
#print axioms selected_bad_answer_origin
#print axioms public_prequery_charged_once
end AspisV8R17
