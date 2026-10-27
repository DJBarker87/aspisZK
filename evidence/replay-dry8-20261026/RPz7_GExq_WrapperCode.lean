import RPz7_GExq_Caller
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_WrapperCode
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint
open CheckpointBytes5Effect
local instance : MonadLift Result Code where monadLift := liftResult

def first {A : Type} (body : Code S2W_Observation.Answer)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state : A) :
    Code (core.result.Result (alloc.vec.Vec U8 × Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 3 firstSizes) state
  let result ← body
  match result with
  | .Err error => pure (.Err error)
  | .Ok saved =>
    match copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved)) with
    | .panic => liftResult (.fail .assertionFailure)
    | .returned written =>
      let cleaned ← allocator.cleanup allocated
      pure (.Ok (saved,release written (exclusiveGuard e.heap 2 0 0),cleaned))

def second {A : Type} (body : Code (core.result.Result Unit AdapterRw.Cuts.PE))
    (allocator : Allocator A) (e : Entry) (state : A) :
    Code (core.result.Result (Heap (Nat → Record) × A) AdapterRw.Cuts.PE) := do
  let allocated ← reserve allocator (admittedSizes e 7 secondSizes) state
  let result ← body
  match result with
  | .Err error => pure (.Err error)
  | .Ok () =>
    let cleaned ← allocator.cleanup allocated
    pure (.Ok (e.heap,cleaned))

theorem first_source {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (body : Code S2W_Observation.Answer)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state : A)
    (native : S2W_ExtractionBoundary.First) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (law : erase (SdkC_Source.dictionary hashv) () body = native id e.first data) :
    erase (SdkC_Source.dictionary hashv) () (first body copy allocator e state) =
      S2W_D189Wrappers.first native copy allocator e id data state := by
  simp only [first,S2W_D189Wrappers.first,erase_bind,GExp_FirstErasure.erase_liftM,law]
  apply congrArg (fun k => reserve allocator (admittedSizes e 3 firstSizes) state >>= k)
  funext allocated
  apply congrArg (fun k => native id e.first data >>= k)
  funext result
  cases result with
  | Err e => rfl
  | Ok saved =>
    dsimp only
    cases copied : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive) (e.heap.accounts 2).1
        (source (nativeBytes saved)) with
    | panic => simp only [copied]; rfl
    | returned written =>
      simp only [copied,erase_bind,GExp_FirstErasure.erase_liftM,erase_pure]

theorem second_source {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (body : Code (core.result.Result Unit AdapterRw.Cuts.PE))
    (allocator : Allocator A) (e : Entry) (state : A)
    (native : S2W_ExtractionBoundary.Second) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot)
    (law : erase (SdkC_Source.dictionary hashv) () body = native id (e.second secondSizes) data slot) :
    erase (SdkC_Source.dictionary hashv) () (second body allocator e state) =
      S2W_D189Wrappers.second native allocator e id data slot state := by
  simp only [second,S2W_D189Wrappers.second,erase_bind,GExp_FirstErasure.erase_liftM,law]
  apply congrArg (fun k => reserve allocator (admittedSizes e 7 secondSizes) state >>= k)
  funext allocated
  apply congrArg (fun k => native id (e.second secondSizes) data slot >>= k)
  funext result
  cases result with
  | Err e => rfl
  | Ok u => cases u; simp only [erase_bind,GExp_FirstErasure.erase_liftM,erase_pure]

#print axioms first_source
#print axioms second_source
end AspisR1.GExq_WrapperCode
end
