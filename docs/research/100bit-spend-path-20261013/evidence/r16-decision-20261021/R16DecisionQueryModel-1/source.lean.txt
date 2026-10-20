import R16DecisionCheckpoint

/-! Strict literal query parsing composed with the construction-owned
first-match checkpoint decision. This is not the erased R19 decision map. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R16DecisionQueryModel
open R16DecisionCheckpoint
open R15WriterModel
attribute [local instance] Classical.propDecidable

def verify (data : Data) (queryBytes : List Nat) : Bool :=
  match LiteralQueryRead.decode queryBytes with
  | none => false
  | some q => decision data q

theorem accepted_writer (data : Data) (xs : List Nat) (q : Queries)
    (decoded : LiteralQueryRead.decode xs = some q)
    (accepted : verify data xs = true) :
    ∀ j, MatchingSupport.match0 (resume (write data q)).data (q j) := by
  apply accepted_first_match data q
  simpa only [verify, decoded] using accepted

theorem honest_decision (q : Queries) : decision honestData q = true := by
  have saved : Prefix honestData q 10 := fun _ _ => honest_match _
  have rest : ∀ j : Fin 22, 10 ≤ j.val →
      MatchingSupport.match0 honestData (q j) := fun _ _ => honest_match _
  unfold decision tx1
  rw [if_pos saved]
  change decide (10 = 10 ∧ ∀ j : Fin 22, 10 ≤ j.val →
    MatchingSupport.match0 honestData (q j)) = true
  exact decide_eq_true ⟨rfl, rest⟩

theorem honest_query_decode : ∃ q : Queries,
    LiteralQueryRead.decode (List.range 22) = some q := by
  have valid : (List.range 22).Nodup ∧ (List.range 22).length = 22 ∧
      ∀ x ∈ List.range 22, x < 262144 := by
    refine ⟨List.nodup_range, List.length_range, ?_⟩
    intro x hx
    have := List.mem_range.mp hx
    omega
  unfold LiteralQueryRead.decode
  rw [dif_pos valid]
  exact ⟨_, rfl⟩

theorem construction_nonvacuous : ∃ q : Queries,
    LiteralQueryRead.decode (List.range 22) = some q ∧
    verify honestData (List.range 22) = true ∧
    FirstMatchState honestData (resume (write honestData q)).data ∧
    (resume (write honestData q)).next = 10 := by
  obtain ⟨q, decoded⟩ := honest_query_decode
  refine ⟨q, decoded, ?_, writer_preserves _ _, rfl⟩
  simpa only [verify, decoded] using honest_decision q

#print axioms accepted_writer
#print axioms honest_decision
#print axioms honest_query_decode
#print axioms construction_nonvacuous
end AspisR1.R16DecisionQueryModel
end
