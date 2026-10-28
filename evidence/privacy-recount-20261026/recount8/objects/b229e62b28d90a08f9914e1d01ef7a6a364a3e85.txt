import R1Z.ProverRwQueryExecution

/-! Compose the real ordered word chain into the retained Q22 mathematical scan. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryModelChain
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryExecution
open Query31ExplicitScanBody AspisV8R19.Q22WordScan

theorem scan_cons_of_one (s next : ScanState) (word : Nat) (words : List Nat)
    (one : scan s [word]=(next,false)) : scan s (word::words)=scan next words := by
  by_cases stop : s.accepted.length=22 ∨ s.draws=64
  · simp only [scan,stop,if_true,Prod.mk.injEq,Bool.true_eq_false,and_false] at one
  · simp only [scan,stop,if_false] at one ⊢
    have shape : (⟨keep s.accepted word,s.draws+1⟩ : ScanState)=next := congrArg Prod.fst one
    rw [shape]

theorem chain_scan {blocks : Blocks} {s final : CurrentScan} {words : List U32}
    (chain : Chain blocks s words final) :
    scan (q22StateOf s) (words.map UScalar.val)=(q22StateOf final,false) := by
  induction chain with
  | stop s _ => rfl
  | next s next final word words k _ _ _ model _ ih =>
    rw [List.map_cons,scan_cons_of_one _ _ _ _ model]
    exact ih

theorem chain_draws {blocks : Blocks} {s final : CurrentScan} {words : List U32}
    (chain : Chain blocks s words final) :
    final.draws.val=s.draws.val+words.length := by
  have hs := scan_progress (q22StateOf s) (words.map UScalar.val) (by rw [chain_scan chain])
  rw [chain_scan chain] at hs
  simpa only [q22StateOf,List.length_map] using hs

theorem scan_nodup (s : ScanState) (words : List Nat) (nodup : s.accepted.Nodup) :
    (scan s words).1.accepted.Nodup := by
  induction words generalizing s with
  | nil => exact nodup
  | cons word words ih =>
    by_cases stop : s.accepted.length=22 ∨ s.draws=64
    · simpa only [scan,stop,if_true] using nodup
    · simp only [scan,stop,if_false]
      apply ih
      by_cases member : word ∈ s.accepted
      · simpa only [keep,member,if_true] using nodup
      · simp only [keep,member,if_false,List.nodup_append,List.nodup_singleton,true_and,and_true]
        refine ⟨nodup,?_⟩
        simp only [List.mem_singleton,forall_eq]
        intro a ha he
        exact member (he ▸ ha)

theorem queries_model (blocks advances : Blocks) :
    ∃ words final output,
      host_transcript.queries_from_pairs blocks advances=ok output ∧
      Chain blocks ⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ words final ∧
      scan ⟨[],0⟩ (words.map UScalar.val)=(q22StateOf final,false) ∧
      words.length≤64 ∧ (acceptedPrefix final).Nodup ∧ finish advances final=ok output := by
  obtain ⟨words,final,output,hr,hc,_,hd,hf⟩ := queries_execute blocks advances
  have model := chain_scan hc
  have draws := chain_draws hc
  have initial : q22StateOf (⟨Array.repeat 22#usize 0#u32,0#usize,0#usize⟩ : CurrentScan)=⟨[],0⟩ := rfl
  rw [initial] at model
  have nd := scan_nodup ⟨[],0⟩ (words.map UScalar.val) (by exact List.nodup_nil)
  rw [model] at nd
  refine ⟨words,final,output,hr,hc,model,?_,nd,hf⟩
  change final.draws.val=0+words.length at draws
  omega

#print axioms scan_cons_of_one
#print axioms chain_scan
#print axioms chain_draws
#print axioms scan_nodup
#print axioms queries_model
end R1Z.ProverRwQueryModelChain
