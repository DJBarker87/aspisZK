import FSQuerySampler

/-! Symbolic adequacy and typed output of the ACTUAL block-shaped sampler.
No probability, independent-candidate law or supplied valid schedule.
All old sampler definitions, including the extra boundary squeeze, unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSQuerySchedule
open FSOracleExecution FSBoundedTranscript FSQuerySampler

/-- Any two sufficiently large block allowances return identical result AND
state. For the source start draws0, eight blocks suffice. The proof uses the
actual eight-word advancement on nonstopping branches, not candidate success. -/
theorem fuel_stable (tape : Tape) (fuel other : Nat) (s : Transcript)
    (accepted : List Nat) (draws : Nat)
    (enough : 64 ≤ draws + 8*fuel) (otherEnough : 64 ≤ draws + 8*other) :
    reference tape fuel s accepted draws = reference tape other s accepted draws := by
  induction fuel generalizing other s accepted draws with
  | zero =>
    have cap : ¬ draws < 64 := by omega
    cases other <;> simp only [reference, if_neg cap]
  | succ fuel ih =>
    by_cases cap : draws < 64
    · cases other with
      | zero => omega
      | succ other =>
        simp only [reference, if_pos cap]
        by_cases stop : (scan (queryWords (squeeze tape s).1) accepted draws).stopped = true
        · simp only [stop, if_true]
        · simp only [stop, if_false]
          have notStopped : (scan (queryWords (squeeze tape s).1) accepted draws).stopped = false := by
            cases value : (scan (queryWords (squeeze tape s).1) accepted draws).stopped <;> simp_all
          have advanced := scan_unstopped_draws (queryWords (squeeze tape s).1) accepted draws notStopped
          rw [query_words_count] at advanced
          apply ih
          · omega
          · omega
    · cases other <;> simp only [reference, if_neg cap]

theorem eight_blocks_suffice (tape : Tape) (s : Transcript) (extra : Nat) :
    reference tape 8 s [] 0 = reference tape (8+extra) s [] 0 :=
  fuel_stable tape 8 (8+extra) s [] 0 (by decide) (by omega)

def ValidAccepted (accepted : List Nat) : Prop :=
  accepted.Nodup ∧ (∀ word ∈ accepted, word < 262144) ∧ accepted.length ≤ 22

theorem empty_valid : ValidAccepted [] := by simp [ValidAccepted]

theorem push_valid (accepted : List Nat) (word : Nat) (valid : ValidAccepted accepted)
    (bounded : word < 262144) (incomplete : accepted.length ≠ 22) :
    ValidAccepted (if word ∈ accepted then accepted else accepted ++ [word]) := by
  by_cases seen : word ∈ accepted
  · simpa only [if_pos seen] using valid
  · rw [if_neg seen]
    rcases valid with ⟨nodup, bounds, length⟩
    refine ⟨List.nodup_append.mpr ⟨nodup, by simp, ?_⟩, ?_, ?_⟩
    · intro a member b last
      have same : b = word := by simpa using last
      subst b
      intro eq
      subst a
      exact seen member
    · intro x member
      rcases List.mem_append.mp member with old | last
      · exact bounds x old
      · have same : x = word := by simpa using last
        simpa only [same] using bounded
    · simp only [List.length_append, List.length_singleton]
      omega

theorem scan_valid (words accepted : List Nat) (draws : Nat)
    (wordBounds : ∀ word ∈ words, word < 262144) (valid : ValidAccepted accepted) :
    ValidAccepted (scan words accepted draws).accepted := by
  induction words generalizing accepted draws with
  | nil => exact valid
  | cons word rest ih =>
    by_cases stop : accepted.length = 22 ∨ draws = 64
    · simpa only [scan, if_pos stop] using valid
    · simp only [scan, if_neg stop]
      apply ih
      · intro x member
        exact wordBounds x (List.mem_cons_of_mem _ member)
      · exact push_valid accepted word valid (wordBounds word List.mem_cons_self)
          (fun eq => stop (Or.inl eq))

theorem finish_success (accepted returned : List Nat) (valid : ValidAccepted accepted)
    (success : finish accepted = some returned) : ValidAccepted returned ∧ returned.length = 22 := by
  unfold finish at success
  split at success
  · rename_i count
    have same := Option.some.inj success
    subst returned
    exact ⟨valid, count⟩
  · contradiction

/-- Success of the reference loop itself establishes all invariants; no
membership/range/cardinality certificate is supplied for its returned list. -/
theorem reference_success (tape : Tape) (fuel : Nat) (s : Transcript)
    (accepted returned : List Nat) (draws : Nat) (valid : ValidAccepted accepted)
    (success : (reference tape fuel s accepted draws).1 = some returned) :
    ValidAccepted returned ∧ returned.length = 22 := by
  induction fuel generalizing s accepted draws with
  | zero =>
    by_cases cap : draws < 64
    · simp only [reference, if_pos cap, reduceCtorEq] at success
    · simp only [reference, if_neg cap] at success
      exact finish_success accepted returned valid success
  | succ fuel ih =>
    by_cases cap : draws < 64
    · simp only [reference, if_pos cap] at success
      have checked := scan_valid (queryWords (squeeze tape s).1) accepted draws
        (query_words_bounded _) valid
      by_cases stop : (scan (queryWords (squeeze tape s).1) accepted draws).stopped = true
      · simp only [stop, if_true] at success
        exact finish_success _ returned checked success
      · simp only [stop, if_false] at success
        exact ih (squeeze tape s).2 _ _ checked success
    · simp only [reference, if_neg cap] at success
      exact finish_success accepted returned valid success

structure Schedule where
  positions : Fin 22 → Fin 262144
  distinct : Function.Injective positions

def scheduleOf (accepted : List Nat) (valid : ValidAccepted accepted) (count : accepted.length = 22) : Schedule where
  positions i := ⟨accepted[i.val]'(by omega), valid.2.1 _ (List.getElem_mem (by omega))⟩
  distinct := by
    intro i j same
    apply Fin.ext
    exact (List.getElem_inj valid.1).mp (congrArg Fin.val same)

/-- The typed vector is made from the returned sampler values, not an
independent schedule. Proof arguments erase; positions are literal list reads. -/
def from_success (tape : Tape) (s : Transcript) (returned : List Nat)
    (success : (reference tape 8 s [] 0).1 = some returned) : Schedule :=
  let facts := reference_success tape 8 s [] returned 0 empty_valid success
  scheduleOf returned facts.1 facts.2

theorem from_success_values (tape : Tape) (s : Transcript) (returned : List Nat)
    (success : (reference tape 8 s [] 0).1 = some returned) (i : Fin 22) :
    ((from_success tape s returned success).positions i).val =
      returned[i.val]'(by have count := (reference_success tape 8 s [] returned 0 empty_valid success).2; omega) := rfl

#print reference_success
#print from_success
#print axioms fuel_stable
#print axioms eight_blocks_suffice
#print axioms reference_success
#print axioms from_success_values
end AspisV8Completion.FSQuerySchedule
