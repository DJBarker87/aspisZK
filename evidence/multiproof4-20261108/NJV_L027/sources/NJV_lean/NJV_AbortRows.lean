import NJV_PendingBind

set_option autoImplicit false
noncomputable section
namespace NJV_AbortRows
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Native abort prefix inside one row loop, including the exact pending frame.
No Rust Err and no reply for the final pending call. -/
inductive Invocation (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → Nat → Nat → List (Request × Digest) → Request → Scratch → Prop where
 | here (fuel : Nat) (s pending : Scratch) (i w : Nat) (q : Request)
     (cut : NJV_Pending.Cut s i length nodes pending q) :
   Invocation H nodes length (fuel+1) s i w [] q pending
 | next (fuel : Nat) (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
     (history : List (Request × Digest)) (q : Request) (pending : Scratch) (active : i<s.n)
     (cut : NJP_NativeRowCut.Cut s i w length nodes
       (H (NJP_NativeRowCut.request log)) after ni nw true log)
     (tail : Invocation H nodes length fuel after ni nw history q pending) :
   Invocation H nodes length (fuel+1) s i w (NJV_NativeRows.events H log++history) q pending

theorem same (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s : Scratch) (i w : Nat) (history : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : Invocation H nodes length fuel s i w history q pending) :
 NJP_AbortPrefix.pending H history.length (rows nodes length fuel s i w)=some (history,q) := by
 induction native with
 | here fuel s pending i w q cut =>
   have pendingNode := NJV_Pending.request H nodes length s pending i w q cut
   have notDone : ¬ (s.n ≤ i) := by have h := cut.active;omega
   simp only [rows,if_neg notDone,bindRun,List.length_nil]
   exact NJV_PendingBind.pending_bind H _ _ 0 [] q pendingNode
 | next fuel s after i w ni nw log history q pending active cut tail ih =>
   have observed := NJP_NativeStep.one H nodes length s i w after ni nw true log cut
   simp only [ite_true] at observed
   have notDone : ¬ (s.n ≤ i) := by omega
   simp only [rows,if_neg notDone,bindRun,List.length_append]
   exact NJV_PendingBind.after_return H _ _ (NJV_NativeRows.events H log) history
     (ok (Row.next after ni nw)) history.length q observed ih

#print same
#print axioms same
end NJV_AbortRows
end
