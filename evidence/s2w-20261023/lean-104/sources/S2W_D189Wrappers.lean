import S2W_D189Entry

/-! D189 interpretation of the two non-extracted wrappers. Kani004 (real SDK
write) and union019 (all selected-coordinate wrappers) check this source
control flow. The primitive SDK/std interpretations retain their named trust
boundaries. Native acceptance below is the wrapper execution, not a supplied
post-account equality. Allocation errors abort and cannot return inner Ok. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_D189Wrappers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open S2W_TrustedStd S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_CommittedCheckpoint

/-- Runtime allocator interface on its private region. P2-P4 admit this
separation from account cells. Allocation or cleanup failure aborts; the
caller proves nothing about an aborted transaction's committed accounts. -/
structure Allocator (A : Type) where
  allocate : A → Nat → Result A
  cleanup : A → Result A

def reserve {A : Type} (allocator : Allocator A) : List Nat → A → Result A
  | [], state => ok state
  | size :: sizes, state => S2W_Trace.thenResult (allocator.allocate state size)
      (fun next => reserve allocator sizes next)

def admittedSizes (e : Entry) (count : Nat) (sizes : Nat → Nat × Nat) : List Nat :=
  (List.range count).filterMap (fun a =>
    let len := (e.buffers (e.handles a).1).val.length
    if len = (sizes a).1 ∨ len = (sizes a).2 then some len else none)

def firstSizes : Nat → Nat × Nat
  | 0 => (58295,58295) | 1 => (1880,1880) | _ => (1768,1768)

def secondSizes : Nat → Nat × Nat
  | 0 => (58295,58295) | 1 => (384,384) | 2 => (192,192)
  | 3 => (768,768) | 4 => (128,256) | 5 => (192,320) | _ => (1768,1768)

/-- Account-only state extension of std Vec allocation/cleanup. to_vec's
complete byte law is Snapshot.to_vec_identity; the allocator does not receive
an AccountInfo or a heap capability. This is the runtime allocator premise's
interpretation, not a claim that allocator state remains unchanged. -/
def allocateSnapshots {A : Type} (allocator : Allocator A) (e : Entry)
    (count : Nat) (sizes : Nat → Nat × Nat) (state : A) :
    Result (A × Heap (Nat → Record)) :=
  S2W_Trace.thenResult (reserve allocator (admittedSizes e count sizes) state)
    (fun next => ok (next,e.heap))

 theorem allocation_frame {A : Type} (allocator : Allocator A) (e : Entry)
    (count : Nat) (sizes : Nat → Nat × Nat) (state next : A) (heap : Heap (Nat → Record))
    (returned : allocateSnapshots allocator e count sizes state = ok (next,heap)) :
    heap = e.heap := by
  unfold allocateSnapshots at returned
  cases allocated : reserve allocator (admittedSizes e count sizes) state with
  | fail error => simp [allocated,S2W_Trace.thenResult] at returned
  | div => simp [allocated,S2W_Trace.thenResult] at returned
  | ok value =>
    simp only [allocated,S2W_Trace.thenResult] at returned
    exact (congrArg Prod.snd (Result.ok.inj returned)).symm

/-- The native first wrapper: same snapshot bounds, owned call, one mutable
borrow/copy/drop, then owned-Vec cleanup. SDK acquisition/drop use the approved
interpretation; bulk copy is the separately named TrustedStd primitive. -/
def first {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (state : A) :
    Result (core.result.Result (alloc.vec.Vec U8 × Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 3 firstSizes) state
  let result ← native program e.first data
  match result with
  | .Err error => ok (.Err error)
  | .Ok saved =>
    match copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved)) with
    | .panic => .fail .assertionFailure
    | .returned written =>
      let cleaned ← allocator.cleanup allocated
      ok (.Ok (saved,release written (exclusiveGuard e.heap 2 0 0),cleaned))

def second {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state : A) :
    Result (core.result.Result (Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 7 secondSizes) state
  let result ← native program (e.second secondSizes) data slot
  match result with
  | .Err error => ok (.Err error)
  | .Ok () =>
    let cleaned ← allocator.cleanup allocated
    ok (.Ok (e.heap,cleaned))

/-- Invert wrapper acceptance. The actual returned heap is derived from the
single trusted std copy; no savedAtWrite or after-account observation supplied. -/
theorem first_accepted {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (after : Heap (Nat → Record))
    (accepted : first native copy allocator e program data state = ok (.Ok (saved,after,final))) :
    native program e.first data = ok (.Ok saved) ∧
    after = writeBracket e.heap 2 0 0 (source (nativeBytes saved)) := by
  unfold first at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
        (e.heap.accounts 2).1 (source (nativeBytes value)) with
    | panic => simp only [copied] at rest; cases rest
    | returned written =>
      rw [copied] at rest
      obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
      have same := congrArg Prod.fst equal
      subst value
      refine ⟨called,?_⟩
      have actual := std.slice_copy_from_slice
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved))
      rw [copied] at actual
      unfold specification at actual
      split at actual
      · have w := Outcome.returned.inj actual
        rw [w] at equal
        exact (congrArg (fun pair => pair.2.1) equal).symm
      · cases actual

 theorem second_accepted {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (after : Heap (Nat → Record))
    (accepted : second native allocator e program data slot state = ok (.Ok (after,final))) :
    native program (e.second secondSizes) data slot = ok (.Ok ()) ∧ after = e.heap := by
  unfold second at accepted
  obtain ⟨allocated,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
  obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    obtain ⟨cleaned,_,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
    have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
    exact ⟨called,(congrArg Prod.fst equal).symm⟩

#print axioms allocation_frame
#print axioms first_accepted
#print axioms second_accepted
end AspisR1.S2W_D189Wrappers
end
