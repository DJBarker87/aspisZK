import R1Z.PV_RunJoin_DecoderDigestLoop29
import R1Z.PV_RunJoin_ResultDomain28
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PortDigest29
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_DecoderDigestLoop29
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem correct (d : Array U32 8#usize) (i : Usize) (hi : i.val ≤ 8) :
    pair_tree_profile.digest_is_canonical_loop d i = ok (decide (Tail d i.val)) := by
  generalize he : 8-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    rw [pair_tree_profile.digest_is_canonical_loop]
    simp only [Array.to_slice,Slice.len,lift,bind_tc_ok]
    by_cases hlt : i.val < 8
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt),index_ok_gen d i (by simpa using hlt)]
      simp only [bind_tc_ok]
      by_cases hc : d.val[i.val]!.val < 2147483647
      · have hn : ¬d.val[i.val]! ≥ aspis_core.field.P := by
          simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq,not_le] using hc
        rw [if_neg hn]
        simp only [lift,bind_tc_ok]
        have hv := BuilderRecordsArray.next_val i (by omega)
        rw [ih (8-(Usize.wrapping_add i 1#usize).val) (by omega)
          (Usize.wrapping_add i 1#usize) (by omega) rfl]
        have ht : Tail d (Usize.wrapping_add i 1#usize).val ↔ Tail d i.val := by
          constructor
          · intro h k hk hk8
            by_cases heq : k=i.val
            · simpa only [heq] using hc
            · exact h k (by omega) hk8
          · intro h k hk hk8
            exact h k (by omega) hk8
        rw [propext ht]
      · have hn : d.val[i.val]! ≥ aspis_core.field.P := by
          simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq,not_lt] using hc
        rw [if_pos hn]
        have ht : ¬ Tail d i.val := fun h => hc (h i.val (by omega) hlt)
        simp only [decide_eq_false ht]
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have ht : Tail d i.val := by intro k hk hk8; omega
      simp only [decide_eq_true ht]
#print axioms correct

theorem canonical_iff (d : Array U32 8#usize) :
    pair_tree_profile.digest_is_canonical d = ok true ↔ Canon8 d := by
  rw [pair_tree_profile.digest_is_canonical,correct d 0#usize (by decide)]
  simp only [Result.ok.injEq,decide_eq_true_eq,Tail,UScalar.ofNatCore_val_eq]
  exact ⟨fun h j hj => h j (Nat.zero_le j) hj,fun h j _ hj => h j hj⟩
#print axioms canonical_iff
end R1Z.PV_RunJoin_PortDigest29
