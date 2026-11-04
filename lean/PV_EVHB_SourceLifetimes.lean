import PV_EVHB_OwnerRegistry
/-! Source-place lifetime association, constructed at Vec::new and transported
by moves. Header slots are indexed by minted lifetimes, not current places.
This supplies the missing constructor/receiver mechanism; full original-entry
reachability and the native primitive interpretation are separate obligations.
The pointer argument must still be bound to Alignment::of::<T>()'s
without_provenance pointer. Its Nat type alone proves no provenance. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_SourceLifetimes
open PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld

/-- An activation distinguishes recursive/repeated uses of the same source
local. Fields distinguish the local, enum payload, and aggregate payload. -/
structure Place where
  activation : Nat
  fields : List Nat
  deriving DecidableEq

structure State (S F : Type) where
  world : NativeWorld S F
  next : Nat
  places : Place → Option Nat

def headerAt {S F : Type} (s : State S F) (p : Place) : Option Header :=
  (s.places p).bind (lookup s.world)

def Fresh {S F : Type} (s : State S F) : Prop :=
  ∀ p id, s.places p = some id → id < s.next

/-- Lifetime numbers are never reused, including slots no longer named by a
current source place. This is stronger than freshness of occupied places. -/
def SlotsBefore {S F : Type} (s : State S F) : Prop :=
  ∀ id h, lookup s.world id = some h → id < s.next

/-- Initialize the ghost source table at entry, retaining the allocator heap.
This is not a permissible reset of an already-running source interpretation;
its association to the original entry remains to be constructed. -/
def start {S F : Type} (w : NativeWorld S F) : State S F :=
  {world := {w with frame := {w.frame with slots := fun _ => none}}
   next := 0
   places := fun _ => none}

theorem start_fresh {S F : Type} (w : NativeWorld S F) :
    Fresh (start w) ∧ SlotsBefore (start w) := by
  constructor
  · intro p id selected
    cases selected
  · intro id h selected
    cases selected

def emptyHeader (shape : Shape) (alignmentAddress : Nat) : Header :=
  ⟨alignmentAddress,0,0,shape,true⟩

/-- Vec::new -> RawVec::new -> RawVec::new_in(Global) ->
RawVecInner::new_in. It installs the new lifetime in the actual result place.
Freshness rules out aliasing any currently occupied source place. -/
def newAt {S F : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat) : State S F :=
  {world := store s.world s.next (emptyHeader shape alignmentAddress)
   next := s.next+1
   places := fun q => if q=p then some s.next else s.places q}

theorem constructor_receiver {S F : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat) :
    (newAt s p shape alignmentAddress).places p = some s.next ∧
    headerAt (newAt s p shape alignmentAddress) p =
      some (emptyHeader shape alignmentAddress) ∧
    OwnedAt (newAt s p shape alignmentAddress).world s.next := by
  refine ⟨?_,?_,?_⟩
  · simp only [newAt,ite_true]
  · simp only [headerAt,newAt,ite_true,Option.bind_some,lookup_store]
  · exact ⟨emptyHeader shape alignmentAddress,lookup_store _ _ _,Or.inr ⟨rfl,rfl⟩⟩

theorem new_fresh {S F : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat) (fresh : Fresh s) :
    Fresh (newAt s p shape alignmentAddress) := by
  intro q id selected
  by_cases same : q=p
  · simp only [newAt,same,ite_true,Option.some.injEq] at selected
    subst id
    exact Nat.lt_succ_self _
  · simp only [newAt,same,ite_false] at selected
    exact Nat.lt.step (fresh q id selected)

theorem constructor_distinct {S F : Type} (s : State S F) (q : Place)
    (id : Nat) (fresh : Fresh s) (selected : s.places q=some id) : id≠s.next :=
  Nat.ne_of_lt (fresh q id selected)

theorem new_slotsBefore {S F : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat) (before : SlotsBefore s) :
    SlotsBefore (newAt s p shape alignmentAddress) := by
  intro id h selected
  by_cases same : id=s.next
  · subst id
    exact Nat.lt_succ_self _
  · change lookup (store s.world s.next (emptyHeader shape alignmentAddress)) id = some h at selected
    rw [lookup_other _ _ _ _ same] at selected
    exact Nat.lt.step (before id h selected)

/-- Moves update only the source-place environment; lifetime/header do not
move. The destination must be vacant or separately dropped by source control.
No silent destruction of an overwritten allocation is asserted here. -/
def move {S F : Type} (s : State S F) (source target : Place) : State S F :=
  {s with places := fun q =>
    if q=target then s.places source else if q=source then none else s.places q}

theorem move_receiver {S F : Type} (s : State S F) (source target : Place)
    (different : source≠target) :
    (move s source target).places target=s.places source ∧
    (move s source target).places source=none ∧
    headerAt (move s source target) target=headerAt s source ∧
    (move s source target).world=s.world := by
  simp only [move,headerAt,ite_true,different,ite_false]
  exact ⟨True.intro,True.intro,True.intro,True.intro⟩

theorem move_fresh {S F : Type} (s : State S F) (source target : Place)
    (fresh : Fresh s) : Fresh (move s source target) := by
  intro q id selected
  by_cases toTarget : q=target
  · simp only [move,toTarget,ite_true] at selected
    exact fresh source id selected
  · by_cases fromSource : q=source
    · simp only [move,toTarget,ite_false,fromSource,ite_true] at selected
      cases selected
    · simp only [move,toTarget,ite_false,fromSource] at selected
      exact fresh q id selected

/-- Selection is a computation on the borrowed receiver place. There is no
caller-supplied owner number and no search through initialized values. -/
def receiverWorld {S F : Type} (s : State S F) (p : Place) :
    Option (World (PV_EVHB_OwnerRegistry.State (Heap S)) F) :=
  (s.places p).map (fun id => PV_EVHB_OwnerRegistry.project id s.world)

structure Run (S F A : Type) where
  outcome : PV_EVH_Runtime.Outcome A
  state : State S F
  events : List PV_RJ4IDB.NativeEvent

/-- Resolve BOTH lifetime and header from the receiver place. Unmapped or
moved-from places admit no call. On the corresponding source-valid domain the
lookup succeeds; no chosen header/owner is a parameter of the operation. -/
def callAt {S F A : Type} (s : State S F) (p : Place)
    (operation : Nat → Header → PV_EVHB_RawVecSource.Q S F A) : Option (Run S F A) :=
  (s.places p).bind fun id =>
    (lookup s.world id).map fun h =>
      let r := operation id h s.world
      ⟨r.outcome,{s with world := r.world},r.events⟩

def tryReserveExactAt {S F : Type} (runtime : PV_EVHB_RawVecSource.Runtime S F)
    (wordMax byteMax : Nat) (s : State S F) (p : Place) (additional : Nat) :
    Option (Run S F (Except PV_EVHB_RawVecSource.ReserveError Unit)) :=
  callAt s p fun id h =>
    PV_EVHB_RawVecSource.tryReserveExact runtime wordMax byteMax id h additional

theorem constructor_call {S F A : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat)
    (operation : Nat → Header → PV_EVHB_RawVecSource.Q S F A) :
    callAt (newAt s p shape alignmentAddress) p operation =
      some (let r := operation s.next (emptyHeader shape alignmentAddress)
        (store s.world s.next (emptyHeader shape alignmentAddress));
        {outcome := r.outcome
         state := {newAt s p shape alignmentAddress with world := r.world}
         events := r.events}) := by
  simp only [callAt,newAt,ite_true,Option.bind_some,lookup_store,Option.map_some]

/-- Return, allocation Err, source failure, divergence, fault and exhaustion
ALL carry the same lifetime environment into their exact post-world. -/
theorem call_preserves_places {S F A : Type} (s : State S F) (p : Place)
    (operation : Nat → Header → PV_EVHB_RawVecSource.Q S F A)
    (r : Run S F A) (called : callAt s p operation = some r) :
    r.state.places=s.places ∧ r.state.next=s.next := by
  unfold callAt at called
  cases selected : s.places p with
  | none => simp only [selected,Option.bind_none] at called; cases called
  | some id =>
    simp only [selected,Option.bind_some] at called
    cases header : lookup s.world id with
    | none => simp only [header,Option.map_none] at called; cases called
    | some h =>
      simp only [header,Option.map_some,Option.some.injEq] at called
      subst r
      exact ⟨rfl,rfl⟩

theorem constructor_selection {S F : Type} (s : State S F) (p : Place)
    (shape : Shape) (alignmentAddress : Nat) :
    receiverWorld (newAt s p shape alignmentAddress) p =
      some (PV_EVHB_OwnerRegistry.project s.next
        (store s.world s.next (emptyHeader shape alignmentAddress))) := by
  simp only [receiverWorld,newAt,ite_true,Option.map_some]

theorem move_selection {S F : Type} (s : State S F) (source target : Place) :
    receiverWorld (move s source target) target=receiverWorld s source := by
  simp only [receiverWorld,move,ite_true]

/-- The lifetime is selected once from the source receiver; both RawVec header
stores address that lifetime. Source-place identity is unchanged by stores. -/
def installAt {S F : Type} (s : State S F) (p : Place) (h : Header)
    (pointer cap : Nat) : State S F :=
  match s.places p with
  | none => s
  | some id => {s with world := install s.world id h pointer cap}

theorem receiver_install {S F : Type} (s : State S F) (p : Place)
    (id : Nat) (h : Header) (pointer cap : Nat) (selected : s.places p=some id) :
    (installAt s p h pointer cap).places p=some id ∧
    headerAt (installAt s p h pointer cap) p =
      some (capacityStore (pointerStore h pointer) cap) := by
  simp only [installAt,selected,headerAt,Option.bind_some,install_lookup]
  exact ⟨True.intro,True.intro⟩

/-- Result/argument/return/aggregate payload moves use the same operation.
The original salts constructor site is identified by its activation and local
path [0]; the reserve receiver is that very local. The source binding receipt
records this initial prefix. Later loop moves/drop coverage remains OPEN. -/
def saltsLocal (activation : Nat) : Place := ⟨activation,[0]⟩

def originalSaltsNew {S F : Type} (s : State S F) (activation : Nat)
    (shape : Shape) (alignmentAddress : Nat) : State S F :=
  newAt s (saltsLocal activation) shape alignmentAddress

theorem original_initial_receiver {S F : Type} (s : State S F) (activation : Nat)
    (shape : Shape) (alignmentAddress : Nat) :
    receiverWorld (originalSaltsNew s activation shape alignmentAddress)
      (saltsLocal activation) =
      some (PV_EVHB_OwnerRegistry.project s.next
        (store s.world s.next (emptyHeader shape alignmentAddress))) :=
  constructor_selection s (saltsLocal activation) shape alignmentAddress

#print axioms constructor_receiver
#print axioms start_fresh
#print axioms new_fresh
#print axioms constructor_distinct
#print axioms new_slotsBefore
#print axioms move_receiver
#print axioms move_fresh
#print axioms constructor_selection
#print axioms move_selection
#print axioms constructor_call
#print axioms call_preserves_places
#print axioms receiver_install
#print axioms original_initial_receiver
end PV_EVHB_SourceLifetimes
