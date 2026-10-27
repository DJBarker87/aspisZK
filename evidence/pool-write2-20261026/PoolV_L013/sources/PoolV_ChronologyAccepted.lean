import PoolV_ChronologyFacts
set_option autoImplicit false
namespace AspisR1.PoolV_ChronologyAccepted
open Aeneas Aeneas.Std Result PoolV_ChronologyFacts

theorem repeated (new old : Slice U64) (sequence next : U64)
    (accepted : PoolV_Chronology.chronology new old true sequence = ok (0#u8,next)) :
    (∀ a b : U64, (a,b) ∈ new.val.zip old.val → b.val ≤ a.val) ∧
    (∃ a b : U64, (a,b) ∈ new.val.zip old.val ∧ b.val < a.val) := by
  have facts := ((PoolV_ChronologyFacts.accepted new old true sequence next).mp accepted).1 rfl
  constructor
  · simpa [decreased] using facts.1
  · simpa [progressed] using facts.2

theorem sequence_bound (sequence : U64) (different : sequence ≠ core.num.U64.MAX) :
    sequence.val < U64.max := by
  have bound : sequence.val ≤ U64.max := by scalar_tac
  have maxval : (core.num.U64.MAX).val = U64.max := by
    simp [core.num.U64.MAX,U64.rMax,U64.max,U64.numBits]
  have notval : sequence.val ≠ U64.max := by
    intro h
    apply different
    apply UScalar.eq_of_val_eq
    simpa only [maxval] using h
  omega

theorem increment (sequence : U64) (different : sequence ≠ core.num.U64.MAX) :
    (U64.wrapping_add sequence 1#u64).val = sequence.val+1 := by
  rw [U64.wrapping_add_val_eq]
  have bound := sequence_bound sequence different
  have strict : sequence.val + (1#u64).val < UScalar.size .U64 := by
    simp only [UScalar.size,UScalarTy.numBits,U64.max] at bound ⊢
    scalar_tac
  rw [Nat.mod_eq_of_lt strict]
  rfl

theorem accepted_sequence (new old : Slice U64) (has : Bool) (sequence next : U64)
    (accepted : PoolV_Chronology.chronology new old has sequence = ok (0#u8,next)) :
    sequence.val < U64.max ∧ next.val = sequence.val+1 := by
  have h := (PoolV_ChronologyFacts.accepted new old has sequence next).mp accepted
  exact ⟨sequence_bound sequence h.2.1,by rw [h.2.2]; exact increment sequence h.2.1⟩

#print axioms repeated
#print axioms sequence_bound
#print axioms increment
#print axioms accepted_sequence
end AspisR1.PoolV_ChronologyAccepted
