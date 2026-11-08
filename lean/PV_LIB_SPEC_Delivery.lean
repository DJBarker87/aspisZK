import PV_LIB_SPEC_Boundary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Delivery
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_Boundary

/-- A successful callback return with an additional suspended intrinsic caller
is administrative, not the enclosing row's own completion/delivery. All failed,
divergent, fault and model-gap outcomes remain explicit. -/
def Terminal {W E : Type} (entry out : State W E) : Prop :=
  (∃ value store, out.current.status = .returned (.ok value) store ∧
    out.suspended = entry.suspended) ∨
  (∃ error store, out.current.status = .returned (.fail error) store) ∨
  (∃ store, out.current.status = .returned .div store) ∨
  (∃ fault store, out.current.status = .fault fault store) ∨ RepresentationGap out

def Boundary {W E : Type} (m : Machine W E) (entry : State W E) (n : Nat) : Prop :=
  OwnComplete entry (run m n entry) ∨ Terminal entry (run m n entry) ∨
    ∃ k, n = k+1 ∧ ConsumedPending m (run m k entry)

def First {W E : Type} (m : Machine W E) (entry : State W E) (n : Nat) : Prop :=
  Boundary m entry n ∧ ∀ k, k < n → ¬ Boundary m entry k

def Diverges {W E : Type} (m : Machine W E) (entry : State W E) : Prop :=
  ∀ n, ¬ Boundary m entry n

theorem run_succ {W E : Type} (m : Machine W E) (q : State W E) (n : Nat) :
    run m (n+1) q = step m (run m n q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => exact ih (step m q)

theorem callback_return_not_boundary {W E : Type} (m : Machine W E) (q : State W E)
    (n : Nat) (value : Data) (store : Store Data)
    (returned : (run m n q).current.status = .returned (.ok value) store)
    (nested : (run m n q).suspended ≠ q.suspended) : ¬ Boundary m q n := by
  rintro (own | terminal | pending)
  · obtain ⟨before,after,result,_,running,_⟩ := own
    rw [returned] at running
    cases running
  · rcases terminal with h | h | h | h | h
    · obtain ⟨v,s,_,suffix⟩ := h
      exact nested suffix
    · obtain ⟨err,s,h⟩ := h; rw [returned] at h; cases h
    · obtain ⟨s,h⟩ := h; rw [returned] at h; cases h
    · obtain ⟨f,s,h⟩ := h; rw [returned] at h; cases h
    · obtain ⟨a,s,h⟩ := h; rw [returned] at h; cases h
  · obtain ⟨k,rfl,c,wait,_,_,_,_,_,_,after,running,_⟩ := pending
    rw [run_succ] at returned
    rw [returned] at running
    cases running

theorem first_unique {W E : Type} (m : Machine W E) (q : State W E)
    (a b : Nat) (ha : First m q a) (hb : First m q b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact False.elim (hb.2 a h ha.1)
  · exact h
  · exact False.elim (ha.2 b h hb.1)

#print axioms run_succ
#print axioms callback_return_not_boundary
#print axioms first_unique
end PV_LIB_SPEC_Delivery
