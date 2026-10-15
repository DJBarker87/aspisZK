import R1TraceWitnessExtract

/-! A small executable list wrapper around the existing single-trace
extractor. It returns the first successful checked witness. The length bound
below counts inspected candidates; it is not a full-log extraction or
cryptographic guarantee. -/

set_option autoImplicit false
namespace AspisR1.ListWitnessExtract

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase

/-- Return the first witness extracted from a trace in the list. -/
def extractList (pub : Public M31Exact) : List (Trace WideExact) → Option Wspend
  | [] => none
  | A :: tail =>
      match TraceWitnessExtract.extract pub A with
      | some w => some w
      | none => extractList pub tail

/-- Number of list entries inspected before the first success, or the full
list length when there is no success. -/
def scanCount (pub : Public M31Exact) : List (Trace WideExact) → Nat
  | [] => 0
  | A :: tail =>
      match TraceWitnessExtract.extract pub A with
      | some _ => 1 + 0
      | none => 1 + scanCount pub tail

theorem returned_checked (pub : Public M31Exact) (traces : List (Trace WideExact))
    (w : Wspend) (h : extractList pub traces = some w) :
    checkM31 pub w = true := by
  induction traces with
  | nil => simp [extractList] at h
  | cons A tail ih =>
      cases he : TraceWitnessExtract.extract pub A with
      | some w0 =>
          have hw : w0 = w := by simpa [extractList, he] using h
          subst w
          exact TraceWitnessExtract.returned_checked pub A w0 he
      | none =>
          apply ih
          simpa [extractList, he] using h

theorem returned_valid (pub : Public M31Exact) (traces : List (Trace WideExact))
    (w : Wspend) (h : extractList pub traces = some w) :
    Rspend pub w := by
  exact (check_eq_true_iff pub w).mp (returned_checked pub traces w h)

/-- If one member has a successful single-trace extraction, the list scan
returns some witness. The selected witness may come from an earlier member. -/
theorem some_result_of_member (pub : Public M31Exact)
    (traces : List (Trace WideExact)) (A : Trace WideExact)
    (hmem : A ∈ traces)
    (hex : ∃ w, TraceWitnessExtract.extract pub A = some w) :
    ∃ w, extractList pub traces = some w := by
  revert A hmem hex
  induction traces with
  | nil =>
      intro A hmem hex
      simp at hmem
  | cons head tail ih =>
      intro A hmem hex
      cases he : TraceWitnessExtract.extract pub head with
      | some w0 =>
          exact ⟨w0, by simp [extractList, he]⟩
      | none =>
          by_cases hA : A = head
          · subst A
            obtain ⟨w, hw⟩ := hex
            rw [he] at hw
            simp at hw
          · have htail : A ∈ tail := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact (hA hhead).elim
              · exact htail
            obtain ⟨w, hw⟩ := ih A htail hex
            exact ⟨w, by simpa [extractList, he] using hw⟩

theorem scanCount_le_length (pub : Public M31Exact)
    (traces : List (Trace WideExact)) :
    scanCount pub traces ≤ traces.length := by
  induction traces with
  | nil => simp [scanCount]
  | cons A tail ih =>
      cases he : TraceWitnessExtract.extract pub A with
      | some w => simp [scanCount, he]
      | none =>
          simp only [scanCount, he, List.length_cons]
          omega

theorem scanCount_le_100 (pub : Public M31Exact)
    (traces : List (Trace WideExact)) (hlen : traces.length ≤ 100) :
    scanCount pub traces ≤ 100 :=
  le_trans (scanCount_le_length pub traces) hlen

#print axioms returned_checked
#print axioms returned_valid
#print axioms some_result_of_member
#print axioms scanCount_le_length
#print axioms scanCount_le_100

end AspisR1.ListWitnessExtract
