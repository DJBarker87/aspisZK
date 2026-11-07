import NMC_FrameComplete
import NMC_RegionFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Original arguments, allocator state and ALL other heap regions accompany
one native segment. The selected word windows do not replace this context. -/
structure Context (A : Type) where
 input : NLC_Finish.Input Unit
 frame : NMC_Frame.Value
 allocator : A
 heap : NMC_Parent.Heap
/-- Returned-error frontiers retain the parent frame BEFORE exit cleanup.
An aborting child has no returned after-state; it is outside this window. -/
structure Observation (A R : Type) where
 reply : R
 context : Context A
/-- Literal full-effect obligation for one segment. A collection of partial
native projections is not asserted to satisfy this contract. This is an
intermediate reviewed-cut interface, never a root or a new trust item. -/
def Cut {A P R : Type} (native expected : Context A→P→Observation A R) : Prop :=
 ∀ before args,
 let actual:=native before args
 let wanted:=expected before args
 actual.reply=wanted.reply ∧
 actual.context.input=wanted.context.input ∧
 actual.context.allocator=wanted.context.allocator ∧
 (∀ address,actual.context.heap address=wanted.context.heap address) ∧
 NMC_Frame.Same actual.context.frame wanted.context.frame
theorem context_ext {A : Type} (a b : Context A)
 (input : a.input=b.input) (frame : a.frame=b.frame)
 (allocator : a.allocator=b.allocator) (heap : a.heap=b.heap) : a=b := by
 cases a;cases b;cases input;cases frame;cases allocator;cases heap;rfl
theorem observation_ext {A R : Type} (a b : Observation A R)
 (reply : a.reply=b.reply) (context : a.context=b.context) : a=b := by
 cases a;cases b;cases reply;cases context;rfl
/-- Reassembly is forward from universally quantified native windows; it
never guesses an execution or equates a seed with an actual child post. -/
theorem from_windows {A P R : Type} (native expected : Context A→P→Observation A R)
 (cut : Cut native expected) (before : Context A) (args : P) :
 native before args=expected before args := by
 obtain ⟨reply,input,allocator,heap,frame⟩:=cut before args
 exact observation_ext _ _ reply (context_ext _ _ input (NMC_Frame.complete _ _ frame) allocator (funext heap))
#print axioms context_ext
#print axioms observation_ext
#print axioms from_windows
set_option pp.proofs false in #print from_windows
end AspisR1.NMC_Window
end
