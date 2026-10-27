import RPt_BEi_CutProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_RecorderCut
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- Delta is taken at the chronological recorder cut, never by set difference.
Repeated identical calls remain separate occurrences. -/
def issued (before after : Log) : Log := after.drop before.length

/-- The interpreter's exact dependence on the existing history. -/
theorem run_append {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (before : Log) :
    BEf_Carrier.run call code state before =
      ((BEf_Carrier.run call code state []).1,
       (BEf_Carrier.run call code state []).2.1,
       before ++ (BEf_Carrier.run call code state []).2.2) := by
  have complete := BEi_ExecutionComplete.complete call code state []
  have extended := BEi_ExecutionHistory.prepend call code state _ [] _ before _ complete
  simpa only [List.append_nil] using BEi_Execution.sound call code state _ _ _ _ extended

/-- Exact recorder segment, derived from operational steps on the SAME state. -/
theorem exact_cut {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    log = before ++ issued before log ∧
    issued before log = (BEf_Carrier.run call code state []).2.2 := by
  have eq := (BEi_Execution.sound call code state after before log value execution).symm.trans
    (run_append call code state before)
  have logs : log = before ++ (BEf_Carrier.run call code state []).2.2 := congrArg (fun x => x.2.2) eq
  have delta : issued before log = (BEf_Carrier.run call code state []).2.2 := by
    simp only [issued,logs,List.drop_left]
  exact ⟨by rw [delta];exact logs,delta⟩

/-- A source binding can be applied to the exported segment without replacing
its cut by a fresh independent execution or discarding a rejected final call. -/
theorem source_cut {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    issued before log = (SdkC_Source.run hashv code []).2 := by
  rw [(exact_cut call code state after before log value execution).2]
  exact congrArg Prod.snd (BEf_Carrier.source call hashv binding code state [])

#print axioms run_append
#print axioms exact_cut
#print axioms source_cut
end AspisR1.BEi_RecorderCut
end
