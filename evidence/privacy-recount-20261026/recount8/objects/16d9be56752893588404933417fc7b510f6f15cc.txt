import Aeneas.Std

/-! Explicit std models for the successful-source admission extraction.
Short-circuit scans retain the exact consumed iterator index, and thread
mutable predicate state between calls. No opaque declaration is introduced. -/
set_option autoImplicit false
namespace R1Z.BuilderAdmissionStd
open Aeneas Aeneas.Std Result

variable {T C E O U V : Type}

def mapErr (f : core.ops.function.FnOnce O E V)
    (r : core.result.Result T E) (c : O) : Result (core.result.Result T V) :=
  match r with
  | .Ok x => ok (.Ok x)
  | .Err e => do let e' ← f.call_once c e; ok (.Err e')

/-- Return the first stopping truth value and consumed element count. -/
def scan (f : core.ops.function.FnMut C T Bool) (stop : Bool) :
    List T → C → Result (Bool × Nat)
  | [], _ => ok (!stop, 0)
  | x :: xs, c => do
      let (b,c') ← f.call_mut c x
      if b = stop then ok (b,1)
      else do let (b',n) ← scan f stop xs c'; ok (b',n+1)

def iterScan (f : core.ops.function.FnMut C T Bool) (stop : Bool)
    (it : core.slice.iter.Iter T) (c : C) : Result (Bool × core.slice.iter.Iter T) := do
  let (b,n) ← scan f stop (it.slice.val.drop it.i) c
  ok (b,{it with i := it.i+n})

def all (f : core.ops.function.FnMut C T Bool) := iterScan f false
def any (f : core.ops.function.FnMut C T Bool) := iterScan f true

theorem mapErr_ok (f : core.ops.function.FnOnce O E V) (x : T) (c : O) :
    mapErr f (.Ok x) c = ok (.Ok x) := rfl

theorem scan_pure (f : core.ops.function.FnMut C T Bool) (g : T → Bool)
    (hf : ∀ c x, f.call_mut c x = ok (g x,c))
    (stop : Bool) (xs : List T) (c : C) :
    ∃ b n, scan f stop xs c = ok (b,n) ∧ n ≤ xs.length ∧
      (b ≠ stop ↔ ∀ x ∈ xs, g x ≠ stop) := by
  induction xs generalizing c with
  | nil =>
      refine ⟨!stop,0,rfl,by simp,?_⟩
      cases stop <;> simp
  | cons x xs ih =>
      rw [scan, hf]
      simp only [bind_tc_ok]
      by_cases h : g x = stop
      · rw [if_pos h]
        refine ⟨g x,1,rfl,by simp,?_⟩
        simp [h]
      · rw [if_neg h]
        obtain ⟨b,n,hs,hn,hb⟩ := ih c
        rw [hs]
        simp only [bind_tc_ok]
        exact ⟨b,n+1,rfl,by simpa using Nat.add_le_add_right hn 1,by simpa [h] using hb⟩

theorem iterScan_pure (f : core.ops.function.FnMut C T Bool) (g : T → Bool)
    (hf : ∀ c x, f.call_mut c x = ok (g x,c))
    (stop : Bool) (it : core.slice.iter.Iter T) (c : C) :
    ∃ b after, iterScan f stop it c = ok (b,after) ∧
      after.slice = it.slice ∧ it.i ≤ after.i ∧ after.i ≤ max it.i it.slice.val.length ∧
      (b ≠ stop ↔ ∀ x ∈ it.slice.val.drop it.i, g x ≠ stop) := by
  obtain ⟨b,n,hs,hn,hb⟩ := scan_pure f g hf stop (it.slice.val.drop it.i) c
  refine ⟨b,{it with i := it.i+n},?_,rfl,by dsimp; omega,?_,hb⟩
  · rw [iterScan, hs]; rfl
  · dsimp only
    simp only [List.length_drop] at hn
    omega

#print axioms mapErr_ok
#print axioms scan_pure
#print axioms iterScan_pure
end R1Z.BuilderAdmissionStd
