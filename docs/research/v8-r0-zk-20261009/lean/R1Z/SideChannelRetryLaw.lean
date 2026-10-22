import R1Z.SideChannelL1AttemptRecord
import R0Z.FsAbortBounds

/-! Exact finite-carrier hazard identities. The carrier may contain the
whole ROM, raw tapes, adversarial policy and retained history. No iid,
stationarity or fixed acceptance probability is assumed. Iterations are
zero-based internally; human attempt k is index k-1. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SideChannelRetryLaw
open SideChannelL1AttemptRecord
open R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable
variable {State Proof Sample : Type}

/-- Counterfactual continuation states are harmless: only the prior before
first success/non-Rejected error is entered. Every actual update is retained. -/
def stateAt (owner : Owner State Proof) (initial : State) : Nat → State
  | 0 => initial
  | k+1 => (owner k (stateAt owner initial k)).2

def recordAt (owner : Owner State Proof) (initial : State) (k : Nat) :=
  (owner k (stateAt owner initial k)).1

def reached (owner : Owner State Proof) (initial : State) : Nat → Prop
  | 0 => True
  | k+1 => reached owner initial k ∧ (recordAt owner initial k).result = .retry

def rejectionPrefix (owner : Owner State Proof) (initial : State) (k : Nat) : Prop :=
  ∀ j, j < k → (recordAt owner initial j).result = .retry

theorem reached_iff (owner : Owner State Proof) (initial : State) (k : Nat) :
    reached owner initial k ↔ rejectionPrefix owner initial k := by
  induction k with
  | zero => simp [reached,rejectionPrefix]
  | succ k ih =>
    rw [reached,ih]
    constructor
    · rintro ⟨prior,last⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with before | same
      · exact prior j before
      · simpa only [same] using last
    · intro prior
      exact ⟨fun j hj => prior j (Nat.lt_succ_of_lt hj),prior k (Nat.lt_succ_self k)⟩

/-- This is the exact native step recurrence from the erased richer owner.
Callback errors are already stop, even if their error label is Rejected. -/
theorem entered_rejection_advances (owner : Owner State Proof) (initial : State)
    (k : Nat) (prior : reached owner initial k)
    (retry : (recordAt owner initial k).result = .retry) :
    reached owner initial (k+1) := ⟨prior,retry⟩

theorem callback_abort_blocks_next (owner : Owner State Proof) (initial : State)
    (k : Nat) (e : Error)
    (stop : (recordAt owner initial k).result = .stop e) :
    ¬ reached owner initial (k+1) := by
  rintro ⟨_,retry⟩
  rw [stop] at retry
  cases retry

/-- Entered iterations are exactly the source owner's returned record
positions. This connects the conditional event to executed control, rather
than merely defining an abstract rejection-prefix probability. -/
theorem run_length_gt_iff (owner : Owner State Proof) (initial : State)
    (fuel index k : Nat) :
    k < (run owner fuel index (stateAt owner initial index)).1.attempts.length ↔
      k < fuel ∧ ∀ j, index ≤ j → j < index+k →
        (recordAt owner initial j).result = .retry := by
  induction fuel generalizing index k with
  | zero => simp only [run,List.length_nil,Nat.not_lt_zero,false_and]
  | succ fuel ih =>
    have step : owner index (stateAt owner initial index) =
        (recordAt owner initial index,stateAt owner initial (index+1)) := rfl
    cases k with
    | zero =>
      simp only [run,step]
      cases hr : (recordAt owner initial index).result <;>
        simp only [List.length_cons,List.length_nil,Nat.zero_lt_succ,Nat.add_zero,true_and]
      all_goals
        constructor
        · intro _ j lower upper; omega
        · intro _; trivial
    | succ k =>
      simp only [run,step]
      cases hr : (recordAt owner initial index).result with
      | done proof =>
        simp only [List.length_cons,List.length_nil]
        constructor
        · intro h; omega
        · rintro ⟨_,prior⟩
          have impossible := prior index (Nat.le_refl _) (by omega)
          rw [hr] at impossible
          cases impossible
      | stop e =>
        simp only [List.length_cons,List.length_nil]
        constructor
        · intro h; omega
        · rintro ⟨_,prior⟩
          have impossible := prior index (Nat.le_refl _) (by omega)
          rw [hr] at impossible
          cases impossible
      | retry =>
        simp only [List.length_cons,Nat.succ_lt_succ_iff]
        rw [ih (index+1) k]
        constructor
        · rintro ⟨small,prior⟩
          refine ⟨by omega,?_⟩
          intro j lower upper
          by_cases same : j=index
          · simpa only [same] using hr
          · exact prior j (by omega) (by omega)
        · rintro ⟨small,prior⟩
          exact ⟨by omega,fun j lower upper => prior j (by omega) (by omega)⟩

theorem actual_entry_iff (owner : Owner State Proof) (initial : State) (k : Fin 8) :
    k.val < (run owner 8 0 initial).1.attempts.length ↔
      rejectionPrefix owner initial k.val := by
  have h := run_length_gt_iff owner initial 8 0 k.val
  simpa only [stateAt,Nat.zero_add,Nat.zero_le,forall_const,and_iff_right k.isLt,
    rejectionPrefix] using h

abbrev mass [Fintype Sample] (event : Sample → Prop) := R0Z.FsAbortBounds.mass event

/-- Zero-mass conditioning uses the conventional value zero; the product
identity remains true, so no impossible history is excluded. -/
def hazard [Fintype Sample] (prior event : Sample → Prop) : ℚ :=
  mass (fun s => prior s ∧ event s) / mass prior

theorem conditional_identity [Fintype Sample] (prior event : Sample → Prop) :
    mass (fun s => prior s ∧ event s) = mass prior * hazard prior event := by
  by_cases zero : mass prior = 0
  · have bound := mass_mono (fun s => prior s ∧ event s) prior (fun _ h => h.1)
    have nonneg := mass_nonneg (fun s => prior s ∧ event s)
    have null : mass (fun s => prior s ∧ event s) = 0 := le_antisymm (zero ▸ bound) nonneg
    simp only [null,zero,zero_mul]
  · unfold hazard
    field_simp

/-- Human attempt k ranges from one through eight. All randomness and
history dependence stays in owners/initial, hence in the conditional hazard. -/
def C (owners : Sample → Owner State Proof) (initial : Sample → State) (k : Nat) : Sample → Prop :=
  fun s => rejectionPrefix (owners s) (initial s) (k-1)

def S (owners : Sample → Owner State Proof) (initial : Sample → State) (k : Nat) : Sample → Prop :=
  fun s => ∃ proof, (recordAt (owners s) (initial s) (k-1)).result = .done proof

def E (owners : Sample → Owner State Proof) (initial : Sample → State) (k : Nat) (e : Error) : Sample → Prop :=
  fun s => (recordAt (owners s) (initial s) (k-1)).result = .stop e

theorem success_hazard [Fintype Sample] (owners : Sample → Owner State Proof)
    (initial : Sample → State) (k : Fin 8) :
    mass (fun s => C owners initial (k.val+1) s ∧ S owners initial (k.val+1) s) =
      mass (C owners initial (k.val+1)) *
        hazard (C owners initial (k.val+1)) (S owners initial (k.val+1)) :=
  conditional_identity _ _

theorem abort_hazard [Fintype Sample] (owners : Sample → Owner State Proof)
    (initial : Sample → State) (k : Fin 8) (e : Error) :
    mass (fun s => C owners initial (k.val+1) s ∧ E owners initial (k.val+1) e s) =
      mass (C owners initial (k.val+1)) *
        hazard (C owners initial (k.val+1)) (E owners initial (k.val+1) e) :=
  conditional_identity _ _

theorem entry_law [Fintype Sample] (owners : Sample → Owner State Proof)
    (initial : Sample → State) (k : Fin 8) :
    mass (fun s => reached (owners s) (initial s) k.val) =
      mass (C owners initial (k.val+1)) := by
  apply mass_congr
  intro s
  simpa only [C,Nat.add_sub_cancel] using reached_iff (owners s) (initial s) k.val

/-- Rejected-prefix control really reaches cap exhaustion in the richer
owner, with exactly fuel records, all state updates retained. -/
theorem all_rejected_exhausts (owner : Owner State Proof) (initial : State)
    (fuel index : Nat) (prior : rejectionPrefix owner initial (index+fuel)) :
    (run owner fuel index (stateAt owner initial index)).1.result = .stop .AttemptsExhausted ∧
    (run owner fuel index (stateAt owner initial index)).1.attempts.length = fuel := by
  induction fuel generalizing index with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    have rejected := prior index (by omega)
    have step : owner index (stateAt owner initial index) =
        (recordAt owner initial index,stateAt owner initial (index+1)) := rfl
    rw [rejected_prefix owner fuel index _ _ _ step rejected]
    have rest := ih (index+1) (fun j hj => prior j (by omega))
    exact ⟨rest.1,congrArg Nat.succ rest.2⟩

theorem actual_entry_mass [Fintype Sample] (owners : Sample → Owner State Proof)
    (initial : Sample → State) (k : Fin 8) :
    mass (fun s => k.val < (run (owners s) 8 0 (initial s)).1.attempts.length) =
      mass (C owners initial (k.val+1)) := by
  apply mass_congr
  intro s
  simpa only [C,Nat.add_sub_cancel] using actual_entry_iff (owners s) (initial s) k

/-- All eight rejections, not a power of one unconditional rejection mass. -/
theorem exhaustion_prefix (owner : Owner State Proof) (initial : State) :
    reached owner initial 8 ↔ ∀ k : Fin 8, (recordAt owner initial k.val).result = .retry := by
  rw [reached_iff]
  exact ⟨fun h k => h k.val k.isLt,fun h j hj => h ⟨j,hj⟩⟩

/-- History-conditioned identities use the SAME history on both factors;
this handles callback faults and all precise failure-origin predicates too. -/
theorem history_hazard [Fintype Sample] (history prior event : Sample → Prop) :
    mass (fun s => (history s ∧ prior s) ∧ event s) =
      mass (fun s => history s ∧ prior s) *
        hazard (fun s => history s ∧ prior s) event := conditional_identity _ _

#print axioms reached_iff
#print axioms entered_rejection_advances
#print axioms callback_abort_blocks_next
#print axioms run_length_gt_iff
#print axioms actual_entry_iff
#print axioms conditional_identity
#print axioms success_hazard
#print axioms abort_hazard
#print axioms entry_law
#print axioms all_rejected_exhausts
#print axioms actual_entry_mass
#print axioms exhaustion_prefix
#print axioms history_hazard
end R1Z.SideChannelRetryLaw
