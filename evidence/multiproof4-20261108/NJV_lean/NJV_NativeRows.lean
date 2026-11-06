import NJP_NativeStep
import NJP_LoopBind

set_option autoImplicit false
noncomputable section
namespace NJV_NativeRows
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def events (H : Request → Digest) (log : NJP_NativeRowCut.Log) :=
 if log.calls=0 then [] else [(NJP_NativeRowCut.request log,H (NJP_NativeRowCut.request log))]

/-- Reviewed native while cuts, NJP_K017..056 plus K060..063. Every
constructor retains the SAME whole pre/post buffers and the exact recursive
program counter. Child reply is installed at request(log), not a free result.
This is the (ai)(5) invocation relation for the binary row loop.

Native sources: evidence/multiproof3-20261108/NJP_multiproof.rs,
sha256 bf98425cd64ba4b1ae42ad2fadb443065339fbdfa1481265a0c9cbdfc0b593ed; NJP_frontier_cuts.rs,
sha256 d7437c9e40b56e1886d4441396d5bcea65cd3d53ff53ec893f1da382b88dcd51.
Assertion excerpts: `assert_eq!(log.calls,1);`
`assert_eq!(idx[k],if k==oldw{parent}else{beforeidx});`
`assert_eq!(log.write_byte,expectedreply);`
`assert_eq!(val[k][h],beforeval);` and, on row exit/missing,
`assert_eq!(log.calls,0);assert_eq!(log.write_calls,0);`
`assert_eq!(i,oldi);assert_eq!(w,oldw);assert_eq!(at,oldat);`
Every byte coordinate is universal; NJP_K023 stays excluded.
 -/
inductive Invocation (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
    Nat → Scratch → Nat → Nat → List (Request × Digest) → Level → Prop where
 | halt (fuel : Nat) (s : Scratch) (i w : Nat) (halted : s.n ≤ i) :
   Invocation H nodes length fuel s i w [] (.done {s with n:=w})
 | stop (fuel : Nat) (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
     (active : i<s.n)
     (cut : NJP_NativeRowCut.Cut s i w length nodes
       (H (NJP_NativeRowCut.request log)) after ni nw false log) :
   Invocation H nodes length (fuel+1) s i w (events H log) (.stop after)
 | next (fuel : Nat) (s after : Scratch) (i w ni nw : Nat) (log : NJP_NativeRowCut.Log)
     (history : List (Request × Digest)) (out : Level) (active : i<s.n)
     (cut : NJP_NativeRowCut.Cut s i w length nodes
       (H (NJP_NativeRowCut.request log)) after ni nw true log)
     (tail : Invocation H nodes length fuel after ni nw history out) :
   Invocation H nodes length (fuel+1) s i w (events H log++history) out

theorem observation (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s : Scratch) (i w : Nat) (history : List (Request × Digest)) (out : Level)
    (native : Invocation H nodes length fuel s i w history out) :
 eval H (rows nodes length fuel s i w)=(history,ok out) := by
 induction native with
 | halt fuel s i w halted =>
   cases fuel <;> simp only [rows,if_pos halted,eval]
 | stop fuel s after i w ni nw log active cut =>
   have step := NJP_NativeStep.one H nodes length s i w after ni nw false log cut
   have notDone : ¬ (s.n ≤ i) := by omega
   simp only [Bool.false_eq_true,ite_false] at step
   simp only [rows,if_neg notDone,bindRun,eval_bind,step,eval,List.append_nil,events]
 | next fuel s after i w ni nw log history out active cut tail ih =>
   have step := NJP_NativeStep.one H nodes length s i w after ni nw true log cut
   have notDone : ¬ (s.n ≤ i) := by omega
   simp only [ite_true] at step
   simp only [rows,if_neg notDone,bindRun,eval_bind,step,ih,events]

#print observation
#print axioms observation
end NJV_NativeRows
end
