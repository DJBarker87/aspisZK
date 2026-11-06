import NKK_LogClauses
import NKK_NativeRaw
set_option autoImplicit false
noncomputable section
namespace NKK_RawFold
open Aeneas Aeneas.Std Result NKK_NativeRaw

structure Event (n : Usize) where
 before : Reader
 reply : Result (Array U8 n × Reader)

structure State (n : Usize) where
 values : List (Array U8 n)
 reader : Reader
 status : Result Unit

def step {n : Usize} (state : State n) (event : Event n) : State n :=
 match state.status with
 | .fail _ => state
 | .div => state
 | .ok _ => match event.reply with
   | .fail err => {state with status:=.fail err}
   | .div => {state with status:=.div}
   | .ok (bytes,next) => ⟨state.values++[bytes],next,.ok ()⟩

def fold {n : Usize} (events : List (Event n)) (state : State n) : State n :=
 events.foldl step state

def observed (n : Usize) : Nat → Reader → NJU_Log.Run (Event n) (List (Array U8 n) × Reader)
 | 0,r => pure ([],r)
 | count+1,r => do
   let (b,next) ← NJU_Log.record (fun reply=>⟨r,reply⟩) (NJC_ConcreteUnwrap.raw n r)
   let (bs,last) ← observed n count next
   pure (b::bs,last)

/-- Complete success state; identical abort status and retained prefix on
failure. The source log, rather than a free list, is supplied to the fold. -/
def Matches {n : Usize} (before : List (Array U8 n)) (state : State n) :
 Result (List (Array U8 n) × Reader) → Prop
 | .ok (bs,last) => state=⟨before++bs,last,.ok ()⟩
 | .fail err => state.status=.fail err
 | .div => state.status=.div

theorem fold_nil {n : Usize} (s : State n) : fold [] s=s := rfl

theorem fold_cons {n : Usize} (e : Event n) (es : List (Event n)) (s : State n) :
 fold (e::es) s=fold es (step s e) := rfl

theorem fail_stays {n : Usize} (es : List (Event n)) (s : State n) (err : Error)
 (failed : s.status=.fail err) : fold es s=s := by
 induction es generalizing s with
 | nil => rfl
 | cons e es ih =>
  rw [fold_cons]
  have next : step s e=s := by simp only [step,failed]
  rw [next]
  exact ih s failed

theorem div_stays {n : Usize} (es : List (Event n)) (s : State n)
 (failed : s.status=.div) : fold es s=s := by
 induction es generalizing s with
 | nil => rfl
 | cons e es ih =>
  rw [fold_cons]
  have next : step s e=s := by simp only [step,failed]
  rw [next]
  exact ih s failed

#print axioms fold_nil
#print axioms fold_cons
#print axioms fail_stays
#print axioms div_stays
end NKK_RawFold
