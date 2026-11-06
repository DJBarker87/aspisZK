import NJP_RowModel

set_option autoImplicit false
noncomputable section
namespace NJP_LoopModel
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result NJP_RowModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

inductive Level where
 | stop (state : Scratch)
 | done (state : Scratch)

/-- A nonreturning Result has no continuation, hence no query suffix. -/
def bindRun {α β : Type} (p : Program Request Digest (Result α))
    (f : α → Program Request Digest (Result β)) : Program Request Digest (Result β) :=
 bind p fun r => match r with
 | .ok a => f a
 | .fail e => .done (.fail e)
 | .div => .done .div

def rows (nodes : Nat → U8) (length : Nat) : Nat → Scratch → Nat → Nat → Program Request Digest (Result Level)
 | 0,s,i,w => .done (if s.n ≤ i then ok (.done {s with n:=w}) else div)
 | fuel+1,s,i,w =>
   if s.n ≤ i then .done (ok (.done {s with n:=w})) else
   bindRun (node nodes length s i w) fun result => match result with
   | .stop stopped => .done (ok (.stop stopped))
   | .next after ni nw => rows nodes length fuel after ni nw

def level (nodes : Nat → U8) (length : Nat) (s : Scratch) : Program Request Digest (Result Level) :=
 rows nodes length s.n s 0 0

def levels (nodes : Nat → U8) (length : Nat) : Nat → Scratch → Program Request Digest (Result Level)
 | 0,s => .done (ok (.done s))
 | h+1,s => bindRun (level nodes length s) fun result => match result with
   | .stop stopped => .done (ok (.stop stopped))
   | .done after => levels nodes length h after

/-- The terminal conjunction observes exactly the first full digest and cursor.
No sortedness or successful-child outcome is baked into this terminal. -/
def terminal (root : Digest) (length : Nat) (s : Scratch) : Bool :=
 decide (s.n=1  ∧  index s 0=0  ∧  value s 0=root  ∧  s.cursor=length)

def finish (root : Digest) (length : Nat) : Level → Bool × Scratch
 | .stop stopped => (false,stopped)
 | .done after => (terminal root length after,after)

/-- Full returning carrier, including both mutable buffers, after 18 heights.
This is a source G support definition; cohort association remains separate. -/
def run (root : Digest) (nodes : Nat → U8) (length : Nat) (s : Scratch) :
    Program Request Digest (Result (Bool × Scratch)) :=
 bindRun (levels nodes length 18 {s with cursor:=0}) fun result => .done (ok (finish root length result))

theorem no_suffix_fail {α β : Type} (H : Request → Digest)
    (p : Program Request Digest (Result α)) (f : α → Program Request Digest (Result β))
    (history : List (Request × Digest)) (error : Error) (failed : eval H p=(history,fail error)) :
 eval H (bindRun p f)=(history,fail error) := by
 simp only [bindRun,eval_bind,failed,eval,List.append_nil]

theorem no_suffix_div {α β : Type} (H : Request → Digest)
    (p : Program Request Digest (Result α)) (f : α → Program Request Digest (Result β))
    (history : List (Request × Digest)) (diverged : eval H p=(history,div)) :
 eval H (bindRun p f)=(history,div) := by
 simp only [bindRun,eval_bind,diverged,eval,List.append_nil]

#print no_suffix_fail
#print axioms no_suffix_fail
#print no_suffix_div
#print axioms no_suffix_div
end NJP_LoopModel
end
