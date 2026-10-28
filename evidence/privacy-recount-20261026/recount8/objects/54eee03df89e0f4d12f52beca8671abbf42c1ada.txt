import R1Z.ProverRwQueryWordTotal

/-! A total source execution with an ordered chain of retained Q22 transitions.
Both terminal success and exhausted distinct-query rejection are covered. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryExecution
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryWord
open ProverRwQueryWordTotal ProverRwQueryTransition Query31ExplicitScanBody

inductive Chain (blocks : Blocks) : CurrentScan → List U32 → CurrentScan → Prop
  | stop (s : CurrentScan) : (s.accepted_len=22#usize ∨ s.draws=64#usize) → Chain blocks s [] s
  | next (s next final : CurrentScan) (word : U32) (words : List U32) (k : Usize) :
      (s.draws / 8#usize : Result Usize)=ok k →
      readWord blocks k s.draws=ok word →
      advance s word=ok next →
      AspisV8R19.Q22WordScan.scan (q22StateOf s) [word.val]=(q22StateOf next,false) →
      Chain blocks next words final → Chain blocks s (word::words) final

def finish (advances : Blocks) (s : CurrentScan) : Result Output := do
  if s.accepted_len=22#usize then
    if s.draws=64#usize then
      let a ← Array.index_usize advances 7#usize
      ok (.Ok (s.accepted,a))
    else
      let k ← s.draws / 8#usize
      let a ← Array.index_usize advances k
      ok (.Ok (s.accepted,a))
  else ok (.Err verifier.Error.Transcript)

theorem execute (blocks advances : Blocks) (fuel : Nat) (s : CurrentScan)
    (hlen : s.accepted_len.val≤22) (bound : s.draws.val+fuel=64) :
    ∃ words final output,
      host_transcript.scan_query_words blocks advances s.accepted s.accepted_len s.draws=ok output ∧
      Chain blocks s words final ∧ final.accepted_len.val≤22 ∧ final.draws.val≤64 ∧
      finish advances final=ok output := by
  induction fuel generalizing s with
  | zero =>
    have cap : s.draws=64#usize := by apply UScalar.eq_of_val_eq; change s.draws.val=64; omega
    have src := source_factored blocks advances s.accepted s.accepted_len s.draws
    by_cases full : s.accepted_len=22#usize
    · have ha := ProverCommitArrayIndex25.array_index_usize_ok advances 7#usize (by decide)
      refine ⟨[],s,.Ok (s.accepted,advances.val[(7#usize).val]'(by simpa [advances.property] using (show (7#usize).val < (8#usize).val by decide))),?_,.stop s (Or.inr cap),hlen,by omega,?_⟩
      · rw [src]; simp only [factored,cap,full,if_true,ha,bind_tc_ok]
      · simp only [finish,cap,full,if_true,ha,bind_tc_ok]
    · refine ⟨[],s,.Err verifier.Error.Transcript,?_,.stop s (Or.inr cap),hlen,by omega,?_⟩
      · rw [src]; simp only [factored,cap,full,if_true,if_false]
      · simp only [finish,full,if_false]
  | succ fuel ih =>
    have hd : s.draws.val<64 := by omega
    have cap : s.draws≠64#usize := by intro he; have hv := congrArg UScalar.val he; change s.draws.val=64 at hv; omega
    obtain ⟨k,hk,hkv⟩ := division_total s.draws hd
    by_cases full : s.accepted_len=22#usize
    · have ha := ProverCommitArrayIndex25.array_index_usize_ok advances k (by exact hkv)
      refine ⟨[],s,.Ok (s.accepted,advances.val[k.val]'(by simpa [advances.property] using hkv)),?_,.stop s (Or.inl full),hlen,by omega,?_⟩
      · rw [source_factored]; simp only [factored,cap,full,if_false,if_true,hk,ha,bind_tc_ok]
      · simp only [finish,cap,full,if_false,if_true,hk,ha,bind_tc_ok]
    · have active : s.accepted_len.val<22 := by
        have ne : s.accepted_len.val≠22 := by intro he; apply full; apply UScalar.eq_of_val_eq; exact he
        omega
      obtain ⟨word,hw⟩ := read_total blocks k s.draws hkv
      obtain ⟨next,hn,hnlen,hndraw,hmodel⟩ := advance_q22 s word active hd
      obtain ⟨words,final,output,hr,hchain,hfl,hfd,hfinish⟩ := ih next hnlen (by omega)
      refine ⟨word::words,final,output,?_,.next s next final word words k hk hw hn hmodel hchain,hfl,hfd,hfinish⟩
      rw [source_factored]
      simp only [factored,cap,full,if_false,hk,bind_tc_ok,hw,hn]
      exact hr

theorem queries_execute (blocks advances : Blocks) :
    ∃ words final output,
      host_transcript.queries_from_pairs blocks advances=ok output ∧
      Chain blocks ⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ words final ∧
      final.accepted_len.val≤22 ∧ final.draws.val≤64 ∧ finish advances final=ok output := by
  exact execute blocks advances 64 ⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ (by decide) (by rfl)

#print axioms execute
#print axioms queries_execute
end R1Z.ProverRwQueryExecution
