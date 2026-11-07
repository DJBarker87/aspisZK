import NNE_Allocator
set_option autoImplicit false
noncomputable section
namespace NNE_AllocatorNecessary
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Necessary private-state transitions, derived from D189 acceptance itself.
Neither transition is present in RSL's allocation-erasing row observation. -/
theorem first {A : Type} (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (allocator : Allocator A) (e : Entry) (p : S2W_ExtractionBoundary.Program)
 (data : Slice U8) (initial final : A) (saved : alloc.vec.Vec U8)
 (post : Heap (Nat → Record))
 (accepted : S2W_D189Wrappers.first native copy allocator e p data initial =
   ok (.Ok (saved,post,final))) :
 ∃ allocated, reserve allocator (admittedSizes e 3 firstSizes) initial = ok allocated ∧
   allocator.cleanup allocated = ok final := by
 unfold S2W_D189Wrappers.first at accepted
 obtain ⟨allocated,ha,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
 obtain ⟨reply,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
 cases reply with
 | Err error => cases rest
 | Ok value =>
  dsimp only at rest
  cases hc : copy (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive)
    (e.heap.accounts 2).1 (S2W_CommittedCheckpoint.source (S2W_ReturnedCheckpoint.nativeBytes value)) with
  | panic => simp only [hc] at rest; cases rest
  | returned written =>
   rw [hc] at rest
   obtain ⟨cleaned,hh,heq⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
   have hp := core.result.Result.Ok.inj (Result.ok.inj heq)
   have hf : cleaned = final := congrArg (fun x => x.2.2) hp
   exact ⟨allocated,ha,hf ▸ hh⟩

theorem second {A : Type} (native : S2W_ExtractionBoundary.Second)
 (allocator : Allocator A) (e : Entry) (p : S2W_ExtractionBoundary.Program)
 (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (initial final : A)
 (post : Heap (Nat → Record))
 (accepted : S2W_D189Wrappers.second native allocator e p data slot initial =
   ok (.Ok (post,final))) :
 ∃ allocated, reserve allocator (admittedSizes e 7 secondSizes) initial = ok allocated ∧
   allocator.cleanup allocated = ok final := by
 unfold S2W_D189Wrappers.second at accepted
 obtain ⟨allocated,ha,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
 obtain ⟨reply,_,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
 cases reply with
 | Err error => cases rest
 | Ok value =>
  obtain ⟨cleaned,hh,heq⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  have hp := core.result.Result.Ok.inj (Result.ok.inj heq)
  have hf : cleaned = final := congrArg Prod.snd hp
  exact ⟨allocated,ha,hf ▸ hh⟩

/-- This is a legal inhabitant of the headline Allocator binder. It prevents
acceptance even with no snapshots (reserve [] succeeds), independently of
native1/native2, TrustedStd, or RuntimeEntrypointAdmission. -/
def rejecting (A : Type) : Allocator A :=
 ⟨fun _ _ => fail .assertionFailure,fun _ => fail .assertionFailure⟩

theorem rejecting_first {A : Type} (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (initial final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) :
 S2W_D189Wrappers.first native copy (rejecting A) e p data initial ≠
   ok (.Ok (saved,post,final)) := by
 intro h
 obtain ⟨allocated,_,hc⟩ := first native copy (rejecting A) e p data initial final saved post h
 cases hc

theorem rejecting_second {A : Type} (native : S2W_ExtractionBoundary.Second)
 (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (slot : S2W_ExtractionBoundary.Slot) (initial final : A) (post : Heap (Nat → Record)) :
 S2W_D189Wrappers.second native (rejecting A) e p data slot initial ≠
   ok (.Ok (post,final)) := by
 intro h
 obtain ⟨allocated,_,hc⟩ := second native (rejecting A) e p data slot initial final post h
 cases hc
#print axioms first
#print axioms second
#print axioms rejecting_first
#print axioms rejecting_second
end NNE_AllocatorNecessary
end
