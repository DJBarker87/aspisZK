import PV_L1D_RetryCount
set_option autoImplicit false
namespace PV_L1E_EntryOrder
open Aeneas Aeneas.Std Result
open PV_L1D_Logged PV_L1D_CallbackSafe
variable {S P : Type}

def entryRange : Nat → Nat → List Nat
  | _,0 => []
  | k,n+1 => k :: entryRange (k+1) n

theorem entryRange_length (k n : Nat) : (entryRange k n).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih (k+1))
#print axioms entryRange_length

/-- Ordered entries, including outer failure/divergence and ordinary stop.
No final-success conditioning or independent reconstruction of a native log. -/
theorem all_outcomes (a : PV_L1D_RetryFold.Attempt S P)
    (entries : ∀ k s, callbacks (a k s).events = [k])
    (n k : Nat) (s : S) :
    ∃ m ≤ n, callbacks (PV_L1D_RetryFold.run a n k s).events = entryRange k m := by
  induction n generalizing k s with
  | zero => exact ⟨0,Nat.le_refl 0,rfl⟩
  | succ n ih =>
    cases leaf : a k s with
    | mk es status =>
      have emitted : callbacks es = [k] := by simpa only [leaf] using entries k s
      simp only [PV_L1D_RetryFold.run,leaf]
      cases status with
      | fail e => exact ⟨1,by omega,emitted⟩
      | div => exact ⟨1,by omega,emitted⟩
      | ok pair =>
        rcases pair with ⟨out,after⟩
        cases out with
        | done proof =>
          refine ⟨1,by omega,?_⟩
          change callbacks (es ++ []) = _
          rw [callbacks_append,emitted]
          rfl
        | stop e =>
          refine ⟨1,by omega,?_⟩
          change callbacks (es ++ []) = _
          rw [callbacks_append,emitted]
          rfl
        | retry =>
          obtain ⟨m,bound,rest⟩ := ih (k+1) after
          refine ⟨m+1,by omega,?_⟩
          change callbacks (es ++ (PV_L1D_RetryFold.run a n (k+1) after).events) = _
          rw [callbacks_append,emitted,rest]
          rfl
#print axioms all_outcomes
end PV_L1E_EntryOrder
