import PV_STX_Machine
set_option autoImplicit false
namespace PV_STX_PrefixLaws
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine
variable {Op : Type → Type 1} {W E A : Type}

theorem returned_stable (handler : Handler Op W E) (n : Nat)
    (r : Result A) (w : W) (es : List E) :
    advance handler n ⟨.returned r,w,es⟩ = ⟨.returned r,w,es⟩ := by
  cases n <;> rfl

theorem fault_stable (handler : Handler Op W E) (n : Nat)
    (f : Fault) (w : W) (es : List E) :
    advance (A := A) handler n ⟨.fault f,w,es⟩ = ⟨.fault f,w,es⟩ := by
  cases n <;> rfl

/-- Resumption uses the retained world and continuation, and appends ordered
new events. It never restarts from the original entry or initial world. -/
theorem advance_add (handler : Handler Op W E) (m n : Nat) (p : Prefix Op W E A) :
    advance handler (m+n) p = advance handler n (advance handler m p) := by
  induction m generalizing p with
  | zero => simp only [Nat.zero_add,advance]
  | succ m ih =>
    rcases p with ⟨status,w,es⟩
    cases status with
    | returned r => simp only [returned_stable]
    | fault f => simp only [fault_stable]
    | running c =>
      simp only [Nat.succ_add,advance]
      exact ih _

theorem events_retained (handler : Handler Op W E) (n : Nat) (p : Prefix Op W E A) :
    ∃ suffix, (advance handler n p).events = p.events ++ suffix := by
  induction n generalizing p with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ n ih =>
    cases hp : p.status with
    | returned r => exact ⟨[],by simp only [advance,hp,List.append_nil]⟩
    | fault f => exact ⟨[],by simp only [advance,hp,List.append_nil]⟩
    | running c =>
      let q := step handler c p.world
      obtain ⟨suffix,hs⟩ := ih ⟨q.status,q.world,p.events ++ q.events⟩
      exact ⟨q.events ++ suffix,by simpa only [advance,hp,List.append_assoc] using hs⟩

/-- All finite observations of a divergent run remain in the run family.
This law is unconditional: no success filter or totality assumption. -/
theorem longer_prefix (handler : Handler Op W E) (m n : Nat) (code : Code Op A) (w : W) :
    ∃ suffix, (run handler (m+n) code w).events = (run handler m code w).events ++ suffix := by
  unfold run
  rw [advance_add]
  exact events_retained handler n _

#print axioms returned_stable
#print axioms fault_stable
#print axioms advance_add
#print axioms events_retained
#print axioms longer_prefix
end PV_STX_PrefixLaws
