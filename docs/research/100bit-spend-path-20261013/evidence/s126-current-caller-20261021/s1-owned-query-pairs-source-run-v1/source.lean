import S1OwnedQueryPairsSourceTailV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result

theorem adapt_bind {A : Type} (m : Result A) (k : A → Result NativeResult) :
    adapt (m >>= k)=(m >>= fun x => adapt (k x)) := by
  unfold adapt
  rw [bind_assoc_eq]

/-- Full-state source-driver induction with the concrete block instance;
valid ranges and successful child executions are obtained internally. -/
theorem sourceTail_eq_drive (ks : List (Fin 8)) (s : OwnedScan) (fallback : Block)
    (blocks advances : Blocks) (valid : Valid s) :
    sourceTail ks (project s) fallback blocks advances=
      adapt (drive ks s (lastBlock ks advances fallback) blocks advances) := by
  induction ks generalizing s fallback with
  | nil => rfl
  | cons k ks ih =>
    cases ks with
    | nil =>
      obtain ⟨after,next,stop,own,v,src,sel⟩ := step_source s
        (atBlock advances (index k) (index_bound k)) (index k) blocks advances (index_bound k) valid
      rw [sel] at own
      rw [drive_single,adapt_bind]
      simp only [sourceTail,lastBlock]
      rw [atBlock_call blocks (index k) (index_bound k)]
      simp only [bind_tc_ok]
      rw [src,own]
      simp only [bind_tc_ok]
      cases stop <;>
        change AspisR1Query31Transcript.finishAdvance advances (index k) (project after)=
          adapt (pairs_finish after (atBlock advances (index k) (index_bound k)))
      all_goals exact finish_source after advances (index k) (index_bound k)
    | cons j ks =>
      obtain ⟨after,next,stop,own,v,src,sel⟩ := step_source s
        (lastBlock (j::ks) advances fallback) (index k) blocks advances (index_bound k) valid
      rw [sel] at own
      rw [drive_cons,adapt_bind]
      simp only [sourceTail,lastBlock]
      rw [atBlock_call blocks (index k) (index_bound k)]
      simp only [bind_tc_ok]
      rw [src,own]
      simp only [bind_tc_ok]
      cases stop with
      | true =>
        change AspisR1Query31Transcript.finishAdvance advances (index k) (project after)=
          adapt (pairs_finish after (atBlock advances (index k) (index_bound k)))
        exact finish_source after advances (index k) (index_bound k)
      | false =>
        change sourceTail (j::ks) (project after) fallback blocks advances=
          adapt (drive (j::ks) after (lastBlock (j::ks) advances fallback) blocks advances)
        exact ih after fallback v

#print axioms sourceTail_eq_drive
end AspisS1OwnedQueryPairs.Model
