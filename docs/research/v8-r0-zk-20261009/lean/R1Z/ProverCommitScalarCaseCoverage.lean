import R1Z.ProverCommitCursor

/-! Coverage of the finite Kani word-slot cases. Counters and all digest
data remain arbitrary; constructing a counter as base+delta loses no state
whose unsigned wrapping difference is at most six. -/
set_option autoImplicit false
namespace R1Z.ProverCommitScalarCaseCoverage

theorem word_slot_cover (word : Nat) (valid : word ≤ 8) :
    ∃ slot : Fin 9, slot.val = word := ⟨⟨word, by omega⟩, rfl⟩

theorem counter_offset_cover (base counter : Fin (2^64))
    (valid : (counter.val + 2^64 - base.val) % 2^64 ≤ 6) :
    ∃ delta : Fin 7, (base.val + delta.val) % 2^64 = counter.val := by
  refine ⟨⟨(counter.val + 2^64 - base.val) % 2^64, by omega⟩, ?_⟩
  have hb := base.isLt
  have hc := counter.isLt
  norm_num only [Nat.reducePow] at hb hc valid ⊢
  omega

#print axioms word_slot_cover
#print axioms counter_offset_cover
end R1Z.ProverCommitScalarCaseCoverage
