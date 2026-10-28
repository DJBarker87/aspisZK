import R1Z.PV_RDB2D_CollectorTrace
import R1Z.PV_RDB2D_PV_B3P_Closure133
namespace R1Z.PV_RDB2D_CollectorProgram
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
open PV_RDB2D_CollectorTrace PV_B3P_Schedule133
set_option autoImplicit false

abbrev Returned := Except Error (Buffer Nat)
abbrev Handler (S F : Type) := Action → State S F → Result (Returned × State S F)

def request {T S F : Type} (allocate : Allocator S) (handler : Handler S F)
    (shape : Shape) (b : Buffer T) (additional : Nat) (state : State S F)
    (next : Nat → State S F → Result (Returned × State S F)) :
    Result (Returned × State S F) := do
  let (out,after) ← issue allocate shape b additional state
  match out.returned with
  | .error _ => abortWith handler ((b.values.length+additional)*shape.width) after
  | .ok () => next out.buffer.address after

/-- cap127 survives filtering and translation. The original checker supplies
all value and endpoint guards; these writes do not allocate or shrink. -/
def filtered {S F : Type} (address : Nat) (state : State S F) : State S F :=
  store address (.links ((legacyLinks.filter (fun x => !x.path)).map translate)) state

def retained (address : Nat) : Buffer Link :=
  ⟨address,127,(legacyLinks.filter (fun x => !x.path)).map translate,by
    rw [List.length_map,PV_RDB2D_CollectorShape.filtered_length]; omega⟩

def sortedBuffer (address : Nat) : Buffer Nat :=
  ⟨address,272,PV_B3P_Sorted133.expected,by
    rw [PV_B3P_SortedResult133.expected_length]; omega⟩

def afterFlat {S F : Type} (deallocate : Nat → Nat → Nat → S → Result S)
    (linkAddress rowAddress : Nat) (rows : List Nat) (state : State S F) :
    Result (Returned × State S F) := do
  let raw := (forestLinks legacyLinks).flatMap (fun link => [link.producer,link.consumer])
  let state := store rowAddress (.rows raw) state
  let state ← release deallocate linkAddress 2032 state
  let state := store rowAddress (.rows rows) state
  ok (.ok (sortedBuffer rowAddress),state)

/-- Value reading of sort_unstable+dedup supplied by the original complete
Result checker, after source iterator destruction. No heap sort scratch exists
in the deployed u16 unstable-sort source. -/
def flat {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (linkAddress : Nat) (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨2,alignment2⟩ (empty Nat) 272 state fun rowAddress after =>
    match PV_B3P_SortedResult133.active with
    | .error e => ok (.error e,after)
    | .ok rows => afterFlat deallocate linkAddress rowAddress rows after

def flatReference {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (linkAddress : Nat) (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨2,alignment2⟩ (empty Nat) 272 state fun rowAddress after =>
    afterFlat deallocate linkAddress rowAddress PV_B3P_Sorted133.expected after

def reserve {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (address : Nat) (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨8,alignment2⟩ (retained address) 190 (filtered address state)
    fun grown after =>
      flat allocate deallocate handler grown
        (store grown (.links (forestLinks legacyLinks)) after)

def reserveReference {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (address : Nat) (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨8,alignment2⟩ (retained address) 190 (filtered address state)
    fun grown after =>
      flatReference allocate deallocate handler grown
        (store grown (.links (forestLinks legacyLinks)) after)

def source {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨8,alignment2⟩ (empty Link) 127 state fun address after =>
    match PV_B3P_Schedule133.legacy with
    | .error e => ok (.error e,after)
    | .ok links =>
      match PV_B3P_Schedule133.forest with
      | .error e => ok (.error e,after)
      | .ok _ => reserve allocate deallocate handler address
          (store address (.links links) after)

def reference {S F : Type} (allocate : Allocator S) (deallocate : Nat → Nat → Nat → S → Result S)
    (handler : Handler S F)
    (state : State S F) : Result (Returned × State S F) :=
  request allocate handler ⟨8,alignment2⟩ (empty Link) 127 state fun address after =>
    reserveReference allocate deallocate handler address
      (store address (.links legacyLinks) after)

theorem flat_complete {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (address : Nat) (state : State S F) :
    flat allocate deallocate handler address state =
      flatReference allocate deallocate handler address state := by
  unfold flat flatReference
  rw [PV_B3P_SortedResult133.complete_result]

theorem reserve_complete {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (address : Nat) (state : State S F) :
    reserve allocate deallocate handler address state =
      reserveReference allocate deallocate handler address state := by
  simp only [reserve,reserveReference,flat_complete]

/-- Complete Result/world equality: every primitive outcome and the actual
handler post-state is shared. Allocation success is not a premise. The source
binding gate, not this theorem's name, must justify the resource program. -/
theorem complete {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) :
    source allocate deallocate handler state =
      reference allocate deallocate handler state := by
  unfold source reference
  rw [PV_B3P_ScheduleResult133.legacy_success,PV_B3P_ScheduleResult133.forest_success]
  simp only [reserve_complete]

theorem with_caller {S F A : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F)
    (caller : Returned × State S F → Result A) :
    (source allocate deallocate handler state >>= caller) =
      (reference allocate deallocate handler state >>= caller) := by
  rw [complete]

#print axioms flat_complete
#print axioms reserve_complete
#print axioms complete
#print axioms with_caller
end R1Z.PV_RDB2D_CollectorProgram
