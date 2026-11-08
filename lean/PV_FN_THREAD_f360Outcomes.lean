import PV_FN_THREAD_f360Frame
import PV_THR2_Packet124Children
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f360Outcomes
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_LibrarySemantics_ArcClone

/-- Both constructor sites use W1's actual AtomicUsize descriptor, so the
count-gap witness does not identify descriptors merely by function number. -/
theorem counter_descriptors :
    PV_THR2_Packet124Children.fn7 =
      PV_W1_NamedLeafBoundary.function PV_THR2_F6.node16 ∧
    PV_THR2_Packet124Children.fn9 =
      PV_W1_NamedLeafBoundary.function PV_THR2_F6.node16 := ⟨rfl,rfl⟩

/-- A well-shaped AtomicUsize representation; the two kinds are the named
AtomicUsize and UnsafeCell descriptors. Zero is a valid AtomicUsize value. -/
def atomicValue (atomicKind unsafeCellKind : Data) (n : Nat) : Data :=
  PV_THR2_KeyValues.pack atomicKind
    [PV_THR2_KeyValues.pack unsafeCellKind [.number n]]

/-- The currently CLOSED121 contract permits a well-shaped zero value even
for argument1. Thus the gap is not limited to the null witness. -/
theorem zero_admitted {E : Type} (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER) (events : List E)
    (atomicKind unsafeCellKind : Data) (pre : PV_W1_ClosedLeaves.Pre e w) :
    ∃ H : PV_W1_OwnerNativeFrame.Backend E,
      PV_W1_ClosedLeaves.Post121 C e H w [.number 1] events ∧
      (H (.child PV_THR2_Packet124Children.fn7 e.store.nextActivation [.number 1])
        (world w)).answer = .returned (.ok (atomicValue atomicKind unsafeCellKind 0)) := by
  let H : PV_W1_OwnerNativeFrame.Backend E := fun _ backend =>
    ⟨.returned (.ok (atomicValue atomicKind unsafeCellKind 0)),backend,[]⟩
  exact ⟨H,PV_W1_ClosedLeaves.f121 C e H w [.number 1] events pre,rfl⟩

theorem zero_count (C : Carrier OWNER Data) (b : Bool)
    (atomicKind unsafeCellKind weak packet : Data) :
    readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) [0,0,0]
      (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
        [atomicValue atomicKind unsafeCellKind 0,weak,packet]) = some (.number 0) := rfl

theorem zero_not_positive (C : Carrier OWNER Data) (b : Bool)
    (atomicKind unsafeCellKind weak packet : Data) :
    ¬ ∃ n, 0 < n ∧
      readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) [0,0,0]
        (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
          [atomicValue atomicKind unsafeCellKind 0,weak,packet]) = some (.number n) := by
  rintro ⟨n,positive,read⟩
  rw [zero_count] at read
  have equal : (0 : Nat) = n := Data.number.inj (Option.some.inj read)
  exact (Nat.ne_of_gt positive) equal.symm

/-- The source's post-fetch_add overflow guard. It is not a success filter:
overflow becomes the actual abort answer; every other answer is unchanged. -/
def sourceAnswer (oldCount : Nat) (answer : Answer Data) : Answer Data :=
  match answer with
  | .returned (.ok value) =>
      if maxRefcount < oldCount then .fault .abort else .returned (.ok value)
  | other => other

theorem source_abort (oldCount : Nat) (value : Data)
    (tooLarge : maxRefcount < oldCount) :
    sourceAnswer oldCount (.returned (.ok value)) = .fault .abort := by
  exact if_pos tooLarge

theorem other_answers (oldCount : Nat) (answer : Answer Data)
    (other : ∀ value, answer ≠ .returned (.ok value)) :
    sourceAnswer oldCount answer = answer := by
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned r =>
    cases r with
    | ok value => exact False.elim (other value rfl)
    | fail err => rfl
    | div => rfl

/-- A reply satisfying the named fact is already closed under the source
overflow guard. Thus the contract does not silently replace source abort
with a normal return, or remove any other answer. -/
theorem fact_guard {E : Type} (C : Carrier OWNER Data)
    (H : PV_W1_OwnerNativeFrame.Backend E)
    (effects : PV_W1_LeafBoundary.Entry → OWNER → Address → Option Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (arcClone : Fact C e H w (effects e w))
    (v : Valid C e w) :
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child e.callee e.store.nextActivation e.arguments) w
    sourceAnswer v.count r.answer = r.answer := by
  dsimp only
  generalize answerEq : (PV_THR2_OwnUniformResourceHandler.lift H
    (.child e.callee e.store.nextActivation e.arguments) w).answer = answer
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned r =>
    cases r with
    | fail err => rfl
    | div => rfl
    | ok result =>
      have bounded := (arcClone v result answerEq).bounded
      exact if_neg (Nat.not_lt.mpr bounded)

/-- Exact abort administration, with the supplied explicit effects store,
world and event suffix. No count write made before abort is discarded. -/
theorem abort_boundary {E : Type} (C : Carrier OWNER Data)
    (e : PV_W1_LeafBoundary.Entry) (w : OWNER) (events suffix : List E) :
    let r : Reply OWNER E Data := ⟨.fault .abort,w,suffix⟩
    let out := PV_W1_LeafBoundary.deliver C e r events
    out.current.status = .fault .abort (PV_W1_LeafBoundary.pending e).store ∧
    out.current.world = w ∧ out.current.events = events ++ suffix := by
  have boundary := PV_W1_LeafBoundary.full_reply C e
    (⟨.fault .abort,w,suffix⟩ : Reply OWNER E Data) events
  exact ⟨boundary.1,boundary.2.1,boundary.2.2.1⟩
#print axioms zero_admitted
#print axioms zero_count
#print axioms zero_not_positive
#print axioms counter_descriptors
#print axioms source_abort
#print axioms other_answers
#print axioms fact_guard
#print axioms abort_boundary
end PV_FN_THREAD_f360Outcomes
