import NLI_ResourceState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Resource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Proposed source-site resource carrier: source129's exact1392-byte
allocation, transfer of its owner on Ok, and allocator cleanup on a later
returned Err. Native Box/drop/source-site association is an OPEN obligation;
these definitions alone supply no realization or row credit. -/
def finishPost {A H : Type} (allocator : S2W_D189Wrappers.Allocator (Heap A))
 (s : State A H) (heap : Heap A) (post : NLC_Finish.Post H) : StepObservation A H :=
 match post with
 | .inr after =>
   let owner := if s.machine.next = .claims then some heap.2 else s.claimsOwner
   ⟨after.input,[],ok (.inr ⟨after,heap,owner⟩)⟩
 | .inl out =>
   let owner := if s.machine.next = .claims then some heap.2 else s.claimsOwner
   match out,owner with
   | .Err _,some _ =>
     let cleanup := allocator.cleanup heap
     ⟨s.machine.input,[.cleanup heap cleanup],(do let after ← cleanup; ok (.inl (out,after,none)))⟩
   | _,_ => ⟨s.machine.input,[],ok (.inl (out,heap,owner))⟩
def semanticStep {A H : Type} (allocator : S2W_D189Wrappers.Allocator (Heap A))
 (s : State A H) (heap : Heap A) : StepObservation A H :=
 let source := PreparedHashCode.run (NLC_Finish.step s.machine)
 let log := source.1.map Event.digest
 match source.2 with
 | .fail e => ⟨s.machine.input,log,.fail e⟩
 | .div => ⟨s.machine.input,log,.div⟩
 | .ok post =>
   let after := finishPost allocator s heap post
   {after with trace := log ++ after.trace}
def step {A H : Type} (allocator : S2W_D189Wrappers.Allocator (Heap A))
 (s : State A H) : StepObservation A H :=
 let entered := Event.occurrence s.machine.next
 if s.machine.next = .claims then
  let allocated := NKA_ClaimsEffects.allocate allocator s.heap
  let enteredLog := [entered,.allocate s.heap allocated]
  match allocated with
  | .fail e => ⟨s.machine.input,enteredLog,.fail e⟩
  | .div => ⟨s.machine.input,enteredLog,.div⟩
  | .ok heap =>
    let after := semanticStep allocator s heap
    {after with trace := enteredLog ++ after.trace}
 else
  let after := semanticStep allocator s s.heap
  {after with trace := entered :: after.trace}
end AspisR1.NLI_Resource
end
