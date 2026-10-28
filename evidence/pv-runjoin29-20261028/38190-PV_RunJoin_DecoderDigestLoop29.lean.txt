import R1Z.PV_RunJoin_DecoderDigest29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecoderDigestLoop29
open Aeneas Aeneas.Std Result ControlFlow R0Z.WriterRefine
open PV_RunJoin_DecoderDigest29
open AspisR1TerminalDecoder.pool_v1.pair_tree_profile
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Tail (d : Array U32 8#usize) (n : Nat) : Prop :=
  ∀ j, n ≤ j → j < 8 → d.val[j]!.val < 2147483647

theorem advance (i : Usize) (hi : i.val < 20) :
    ∃ j : Usize, (i + 1#usize : Result Usize) = ok j ∧ j.val = i.val + 1 := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  scalar_tac
#print axioms advance

/-- Symbolic loop correctness, including noncanonical words. No concrete
hash, large numeral or frontier is reduced. -/
theorem correct (d : Array U32 8#usize) (i : Usize) (hi : i.val ≤ 8) :
    digest_is_canonical_loop d i = ok (decide (Tail d i.val)) := by
  classical
  generalize he : 8-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    unfold digest_is_canonical_loop
    rw [loop.eq_def]
    by_cases hlt : i.val < 8
    · rw [body_in_range d i hlt]
      by_cases hc : d.val[i.val]!.val < 2147483647
      · rw [if_pos hc]
        obtain ⟨j,hj,hv⟩ := advance i (by omega)
        rw [hj]
        simp only [bind_tc_ok]
        change digest_is_canonical_loop d j = _
        rw [ih (8-j.val) (by omega) j (by omega) rfl]
        have ht : Tail d j.val ↔ Tail d i.val := by
          constructor
          · intro h k hk hk8
            by_cases heq : k = i.val
            · simpa only [heq] using hc
            · exact h k (by omega) hk8
          · intro h k hk hk8
            exact h k (by omega) hk8
        rw [propext ht]
      · rw [if_neg hc]
        simp only [bind_tc_ok]
        have ht : ¬ Tail d i.val := fun h => hc (h i.val (by omega) hlt)
        simp only [decide_eq_false ht]
    · rw [body_done d i (by omega)]
      simp only [bind_tc_ok]
      have ht : Tail d i.val := by intro k hk hk8; omega
      simp only [decide_eq_true ht]
#print axioms correct

theorem canonical_iff (d : Array U32 8#usize) :
    digest_is_canonical d = ok true ↔ Canon8 d := by
  rw [digest_is_canonical,correct d 0#usize (by decide)]
  simp only [Result.ok.injEq,decide_eq_true_eq,Tail]
  exact ⟨fun h j hj => h j (by omega) hj,fun h j _ hj => h j hj⟩
#print axioms canonical_iff
end R1Z.PV_RunJoin_DecoderDigestLoop29
