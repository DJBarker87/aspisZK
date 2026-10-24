import Port10AUTH_Leaves
import Port10AUTH_TerminalCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_LoopTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open MultiproofConeRef
open Port9OR_BatchStep (Indices Values)

/-- At the actual terminal cursor, an accepted emitted loop has exactly one
terminal body and no invented continuation. Its entire body log is preserved. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot : Usize)
    (keys : Array U64 16#usize) (s : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (small : n.val<256) (fuel : Nat)
    (success : erase D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel s.idx s.val s.n n)=
      ok (outIdx,outVal,some (.Ok ()))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (Port9OR_BatchStep.ops base)
      D proof root kind hash lo n slot keys s.idx s.val s.n n=ok (.done (outIdx,outVal,some (.Ok ()))) ∧
    (Port9OR_Code.trace D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel s.idx s.val s.n n)).1=
      (Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n)).1 := by
  cases fuel with
  | zero => cases success
  | succ fuel =>
    have native := (Port9OR_BatchLoop.source base D D hash proof root kind lo n slot keys small
      (fuel+1) s.idx s.val s.n n (by simp)).symm.trans success
    have body := Port4B_TreeCuts.terminal (Port4B_VerifyInstall.install base) D hash proof root kind lo n slot s.n
      keys s.idx outIdx s.val outVal native
    refine ⟨body,?_⟩
    have value := (Port9OR_Code.trace_value D hash _).trans ((Port9OR_BatchStep.source base D hash proof root kind lo n slot
      keys s.idx s.val s.n n).trans body)
    simp only [Port9OR_BatchLoop.code,Port10AUTH_Trace.trace_bind]
    cases h : Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n) with
    | mk log result =>
      rw [h] at value
      dsimp only at value
      rw [value]
      simp only [Port10AUTH_Leaf.pure_trace,List.append_nil]

#print axioms accepted
end AspisR1.Port10AUTH_LoopTail
end
