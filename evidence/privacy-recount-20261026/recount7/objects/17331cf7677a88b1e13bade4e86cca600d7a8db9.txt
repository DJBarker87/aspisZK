import R1Z.ProverRwQuerySourceWindow
import R1Z.ProverRwQueryResult
set_option autoImplicit false
namespace R1Z.ProverRwQueryStop
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryWord
open ProverRwQuerySourceWindow Query31ExplicitScanBody

def finishAt (advances : Blocks) (k : Usize) (s : CurrentScan) : Result Output :=
  if s.accepted_len=22#usize then do
    let a ← Array.index_usize advances k
    ok (.Ok (s.accepted,a))
  else ok (.Err verifier.Error.Transcript)

theorem run_finish (blocks advances : Blocks) (s : CurrentScan)
    (terminal : s.accepted_len=22#usize ∨ s.draws=64#usize) :
    run blocks advances s=ProverRwQueryExecution.finish advances s := by
  unfold run
  rw [source_factored]
  by_cases full : s.accepted_len=22#usize
  · by_cases cap : s.draws=64#usize <;>
      simp only [factored,ProverRwQueryExecution.finish,full,cap,if_true,if_false]
  · have cap := terminal.resolve_left full
    simp only [factored,ProverRwQueryExecution.finish,full,cap,if_true,if_false]

theorem run_at (blocks advances : Blocks) (k : Usize) (s : CurrentScan)
    (terminal : s.accepted_len=22#usize ∨ s.draws=64#usize)
    (bound : s.draws.val≤64) (hk : k.val<8)
    (index : min 7 (s.draws.val/8)=k.val) :
    run blocks advances s=finishAt advances k s := by
  rw [run_finish blocks advances s terminal,ProverRwQueryResult.finish_exact advances s bound]
  have ha := ProverCommitArrayIndex25.array_index_usize_ok advances k hk
  simp only [finishAt,ha,bind_tc_ok,ProverRwQueryResult.selected,index]

#print axioms run_finish
#print axioms run_at
end R1Z.ProverRwQueryStop
