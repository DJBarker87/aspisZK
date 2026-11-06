import NJV_NativeRows

set_option autoImplicit false
noncomputable section
namespace NJV_NativeLevels
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The native 18-height controller consumes row loops in order, reinitializes
(i,w) to (0,0), and installs their returned n. NJP_K066/067 (entry),
K062/063 (row exit) and K068/069 (terminal) retain their own separate cuts;
NJP_K062 is not used for any data value. Exact receipt map is NJV_CUTS.md.

Native controller source: evidence/multiproof3-20261108/NJP_frontier_cuts.rs,
sha256 d7437c9e40b56e1886d4441396d5bcea65cd3d53ff53ec893f1da382b88dcd51 (NJP_K064/065).
Assertion excerpts: `assert_eq!(i,0);assert_eq!(w,0);`
`assert_eq!(log.count,core::cmp::min(stop+1,18));`
`assert_eq!(log.before[selected],if selected==0{n}else{log.after[selected-1]});`
Rows are supplied by the separate full-state cuts, never by this control gate.
 -/
inductive Invocation (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → List (Request × Digest) → Level → Prop where
 | final (s : Scratch) : Invocation H nodes length 0 s [] (.done s)
 | stop (height : Nat) (s after : Scratch) (history : List (Request × Digest))
     (row : NJV_NativeRows.Invocation H nodes length s.n s 0 0 history (.stop after)) :
   Invocation H nodes length (height+1) s history (.stop after)
 | next (height : Nat) (s after : Scratch) (first rest : List (Request × Digest)) (out : Level)
     (row : NJV_NativeRows.Invocation H nodes length s.n s 0 0 first (.done after))
     (tail : Invocation H nodes length height after rest out) :
   Invocation H nodes length (height+1) s (first++rest) out

theorem observation (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s : Scratch) (history : List (Request × Digest)) (out : Level)
    (native : Invocation H nodes length height s history out) :
 eval H (levels nodes length height s)=(history,ok out) := by
 induction native with
 | final s => rfl
 | stop height s after history row =>
   have observed := NJV_NativeRows.observation H nodes length s.n s 0 0 history (.stop after) row
   simp only [levels,level,bindRun,eval_bind,observed,eval,List.append_nil]
 | next height s after first rest out row tail ih =>
   have observed := NJV_NativeRows.observation H nodes length s.n s 0 0 first (.done after) row
   simp only [levels,level,bindRun,eval_bind,observed,ih]

/-- SAME-state returning invocation, after the native entry resets its local
cursor. Both full scratch buffers appear in the conclusion. -/
theorem returning (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (root : Digest) (s : Scratch) (history : List (Request × Digest)) (out : Level)
    (native : Invocation H nodes length 18 {s with cursor:=0} history out) :
 eval H (run root nodes length s)=(history,ok (finish root length out)) := by
 have observed := observation H nodes length 18 {s with cursor:=0} history out native
 simp only [run,bindRun,eval_bind,observed,eval,List.append_nil]

#print observation
#print axioms observation
#print returning
#print axioms returning
end NJV_NativeLevels
end
