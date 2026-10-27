import JGv_DotLoop
import Port3_FlushInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof AspisR1FinishRelationCurrent JGv_DotOps

theorem kernel (fm : Slice U8) (ws : Slice Q)
    (length : ws.val.length=64)
    (read : ∀ i : Usize,i.val<64 → ∃ x,finishField fm i=ok x ∧ CanonicalFinish x)
    (canonical : ∀ q∈ws.val,CanonQ q) :
    ∃ out,verifier.finish_query_dot ops fm ws=ok (.Ok out) ∧ CanonicalFinish out := by
  obtain ⟨dot,loopCall⟩ := JGv_DotLoop.source fm ws EbyKNewToPushStateABI.pushZero 0#usize length
    (by decide) (by rfl) read canonical
  obtain ⟨out,finish,c⟩ := JGv_DotOps.finish dot
  refine ⟨out,?_,c⟩
  unfold verifier.finish_query_dot
  rw [JGv_DotOps.initial,bind_tc_ok,loopCall,bind_tc_ok]
  dsimp only
  rw [finish,bind_tc_ok]
#print axioms kernel

theorem source (fm : Slice U8) (ws : Slice AspisR1Stage2.Stage2Finish.K)
    (length : ws.val.length=64)
    (read : ∀ i : Usize,i.val<64 → ∃ x,finishField fm i=ok x ∧ CanonicalFinish x)
    (canonical : ∀ q∈ws.val,Port3_FlushInstall.Canonical q) :
    ∃ out,SAG_DotClosed.source fm ws=ok (.Ok out) := by
  have cm : ∀ q∈(SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws).val,CanonQ q := by
    intro q hq
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp hq
    exact canonical original member
  obtain ⟨out,run,c⟩ := kernel fm (SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ ws)
    (by simpa only [SAG_DotAdapter.mapSlice,List.length_map] using length) read cm
  refine ⟨SAG_DotAdapter.toStageE out,?_⟩
  change (do let result ← SAG_DotAdapter.kernel SAG_DotClosed.seed fm ws
             match result with
             | core.result.Result.Ok value=>ok (core.result.Result.Ok (SAG_DotAdapter.toStageE value))
             | core.result.Result.Err error=>ok (core.result.Result.Err (SAG_DotAdapter.toStageError error)))=_
  rw [show SAG_DotAdapter.kernel SAG_DotClosed.seed fm ws=ok (.Ok out) from run,bind_tc_ok]
#print axioms source
end AspisR1.JGv_DotTotal
end
