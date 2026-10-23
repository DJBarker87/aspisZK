import S6FullSourceCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.CanonicalTotal
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_forest_accounts

/-- TOTAL native canonicality scan on all eight raw words; no canonical-input
or successful-body premise. The source loop's index decreases the remaining size. -/
theorem scan_total (digest : Array U32 8#usize) :
    ∃ result, digest_is_canonical digest=ok result := by
  have hw : digest_is_canonical_loop digest 0#usize ⦃ _ => True ⦄ := by
    unfold digest_is_canonical_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 8-i.val) (fun i : Usize => i.val≤8)
      (fun _ : Option Bool => True)
      (fun i => digest_is_canonical_loop.body digest i) 0#usize ?_ ?_
    · intro i hi
      unfold digest_is_canonical_loop.body
      step*
      all_goals scalar_tac
    · scalar_tac
  obtain ⟨pending,hpending,_⟩ := spec_imp_exists hw
  unfold digest_is_canonical
  rw [hpending,bind_tc_ok]
  cases pending <;> exact ⟨_,rfl⟩

#print axioms scan_total
end AspisS6SourceCodec.CanonicalTotal
