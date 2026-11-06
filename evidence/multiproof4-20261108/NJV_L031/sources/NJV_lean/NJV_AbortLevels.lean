import NJV_AbortRows
import NJV_NativeLevels

set_option autoImplicit false
noncomputable section
namespace NJV_AbortLevels
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

inductive Invocation (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → List (Request × Digest) → Request → Scratch → Prop where
 | here (height : Nat) (s pending : Scratch) (history : List (Request × Digest)) (q : Request)
     (row : NJV_AbortRows.Invocation H nodes length s.n s 0 0 history q pending) :
   Invocation H nodes length (height+1) s history q pending
 | next (height : Nat) (s after pending : Scratch) (first rest : List (Request × Digest)) (q : Request)
     (row : NJV_NativeRows.Invocation H nodes length s.n s 0 0 first (.done after))
     (tail : Invocation H nodes length height after rest q pending) :
   Invocation H nodes length (height+1) s (first++rest) q pending

theorem same (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s : Scratch) (history : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : Invocation H nodes length height s history q pending) :
 NJP_AbortPrefix.pending H history.length (levels nodes length height s)=some (history,q) := by
 induction native with
 | here height s pending history q row =>
   have pendingRow := NJV_AbortRows.same H nodes length s.n s 0 0 history q pending row
   simp only [levels,bindRun]
   exact NJV_PendingBind.pending_bind H _ _ history.length history q pendingRow
 | next height s after pending first rest q row tail ih =>
   have returned := NJV_NativeRows.observation H nodes length s.n s 0 0 first (.done after) row
   simp only [levels,bindRun,List.length_append]
   exact NJV_PendingBind.after_return H _ _ first rest (ok (Level.done after)) rest.length q returned ih

theorem run (H : Request → Digest) (nodes : Nat → U8) (length : Nat) (root : Digest)
    (s : Scratch) (history : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : Invocation H nodes length 18 {s with cursor:=0} history q pending) :
 NJP_AbortPrefix.pending H history.length (NJP_LoopModel.run root nodes length s)=some (history,q) := by
 have pendingPrefix := same H nodes length 18 {s with cursor:=0} history q pending native
 simp only [NJP_LoopModel.run,bindRun]
 exact NJV_PendingBind.pending_bind H _ _ history.length history q pendingPrefix

#print same
#print axioms same
#print run
#print axioms run
end NJV_AbortLevels
end
