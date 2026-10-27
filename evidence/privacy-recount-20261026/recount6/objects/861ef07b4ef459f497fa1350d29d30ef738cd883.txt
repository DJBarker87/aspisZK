import R1Z.ProverRwQueryModelChain

/-! Final query status and advance-state selection, including block boundaries. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryResult
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryExecution
open ProverRwQueryModelChain ProverRwQueryWordTotal Query31ExplicitScanBody

def selected (advances : Blocks) (s : CurrentScan) : Array U8 32#usize :=
  advances.val[min 7 (s.draws.val/8)]'(by have h:=Nat.min_le_left 7 (s.draws.val/8); simpa [advances.property] using (show min 7 (s.draws.val/8)<8 by omega))

theorem finish_exact (advances : Blocks) (s : CurrentScan) (bound : s.draws.val≤64) :
    finish advances s =
      if s.accepted_len=22#usize then ok (.Ok (s.accepted,selected advances s))
      else ok (.Err verifier.Error.Transcript) := by
  by_cases full : s.accepted_len=22#usize
  · by_cases cap : s.draws=64#usize
    · have ha := ProverCommitArrayIndex25.array_index_usize_ok advances 7#usize (by decide)
      simp only [finish,full,cap,if_true,ha,bind_tc_ok,selected]
      rfl
    · have hd : s.draws.val<64 := by
        have ne : s.draws.val≠64 := by intro he; apply cap; apply UScalar.eq_of_val_eq; exact he
        omega
      obtain ⟨k,hk,hkv⟩ := UScalar.div_spec s.draws (y := 8#usize) (by decide)
      have hv : k.val=s.draws.val/8 := hkv
      have kb : k.val<8 := by omega
      have ha := ProverCommitArrayIndex25.array_index_usize_ok advances k kb
      have index : min 7 (s.draws.val/8)=k.val := by omega
      simp only [finish,full,cap,if_true,if_false,hk,ha,bind_tc_ok,selected,index]
  · simp only [finish,full,if_false]

theorem queries_characterization (blocks advances : Blocks) :
    ∃ words final,
      Chain blocks ⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ words final ∧
      AspisV8R19.Q22WordScan.scan ⟨[],0⟩ (words.map UScalar.val)=(q22StateOf final,false) ∧
      words.length≤64 ∧ (acceptedPrefix final).Nodup ∧
      host_transcript.queries_from_pairs blocks advances =
        if final.accepted_len=22#usize then ok (.Ok (final.accepted,selected advances final))
        else ok (.Err verifier.Error.Transcript) := by
  obtain ⟨words,final,output,hr,hc,_,hd,hf⟩ := queries_execute blocks advances
  have model := chain_scan hc
  have draws := chain_draws hc
  have initial : q22StateOf (⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ : CurrentScan)=⟨[],0⟩ := rfl
  rw [initial] at model
  have nd := scan_nodup ⟨[],0⟩ (words.map UScalar.val) List.nodup_nil
  rw [model] at nd
  refine ⟨words,final,hc,model,?_,nd,?_⟩
  · change final.draws.val=0+words.length at draws; omega
  · rw [hr,←hf,finish_exact advances final hd]

#print axioms finish_exact
#print axioms queries_characterization
end R1Z.ProverRwQueryResult
