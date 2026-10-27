import R1Z.BuilderRecordsArray
import R1Z.BuilderRecordsExtracted

set_option autoImplicit false
namespace R1Z.BuilderRecordsRecipient
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference
open R0Z.WriterRefine
open pool_v1.pair_forest_copy_builder R1Z.BuilderRecordsArray
abbrev Note := pool_v1.payment_relation.PoolV1OutputNoteWitnessV1

def owner (rec : Option Note) : Array U32 8#usize :=
  match rec with | none => ZERO8 | some r => r.owner_key

def salt (rec : Option Note) : Array U32 8#usize :=
  match rec with | none => ZERO8 | some r => r.salt

/-- Symbolic suffix induction: each iteration fills one lane and preserves
all earlier lanes, and the optional recipient itself is unchanged. -/
theorem loop_spec (rec : Option Note) (ro rs : Array U32 8#usize)
    (lane : Usize) (hl : lane.val ≤ 8)
    (hnone : rec = none → ro = ZERO8 ∧ rs = ZERO8)
    (ho : Prefix ro (owner rec) lane.val) (hs : Prefix rs (salt rec) lane.val) :
    records_reference.records_reference_with_roots_loop1 rec ro rs lane =
      ok (rec, owner rec, salt rec) := by
  generalize he : 8 - lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing lane ro rs with
  | h remaining ih =>
    rw [records_reference.records_reference_with_roots_loop1]
    by_cases hlt : lane.val < 8
    · have test : lane < 8#usize := by simpa [UScalar.lt_equiv] using hlt
      rw [if_pos test]
      have hn := next_val lane (by omega)
      cases rec with
      | none =>
        obtain ⟨rfl, rfl⟩ := hnone rfl
        simp only [bind_tc_ok, lift]
        apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
          ZERO8 ZERO8 (Usize.wrapping_add lane 1#usize) (by omega)
        · exact fun _ => ⟨rfl, rfl⟩
        · exact fun _ _ _ => rfl
        · exact fun _ _ _ => rfl
        · rfl
      | some r =>
        dsimp only
        rw [index_ok r.owner_key lane (by simpa using hlt)]
        simp only [bind_tc_ok]
        rw [update_gen ro lane _ (by simpa using hlt)]
        simp only [bind_tc_ok]
        rw [index_ok r.salt lane (by simpa using hlt)]
        simp only [bind_tc_ok]
        rw [update_gen rs lane _ (by simpa using hlt)]
        simp only [bind_tc_ok, lift]
        apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
          _ _ (Usize.wrapping_add lane 1#usize) (by omega)
        · intro h; cases h
        · simpa [hn, owner] using prefix_step ro (owner (some r)) lane (by simpa using hlt) ho
        · simpa [hn, salt] using prefix_step rs (salt (some r)) lane (by simpa using hlt) hs
        · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have e : lane.val = 8 := by omega
      rw [prefix_done ro (owner rec) (by simpa [e] using ho),
        prefix_done rs (salt rec) (by simpa [e] using hs)]

#print axioms loop_spec
end R1Z.BuilderRecordsRecipient
