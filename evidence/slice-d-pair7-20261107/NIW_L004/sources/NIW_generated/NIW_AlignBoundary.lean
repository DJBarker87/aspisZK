import NIW_AlignPair
import NIT_PairControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignBoundary
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl

/-- Selector-independent decoded post-state of the regular child. The native
assertions are pointwise windows; equality here uses the same finite-array
all-limb convention as NIT_Cuts. No model call equation is part of the cut. -/
structure Log where
 regular : Reply Unit
 partialReply : Reply Powers
 high : Reply Unit
 scratchReply : Scratch
 partsReply : Parts
 commonReply : CommonCells
 highPartsReply : Parts
 partialCommon : K
 highBefore : E
 highPartial : E
 highPointer : Nat
 events : Nat → Nat
 count : Nat

def enteredPartial (shared : Bool) (l : Log) : Prop :=
 l.regular=.Ok () ∧ shared=true

def enteredHigh (shared : Bool) (l : Log) : Prop :=
 enteredPartial shared l ∧ ∃ values,l.partialReply=.Ok values

def expected (shared : Bool) (l : Log) : Reply Unit :=
 match l.regular with
 | .Err e=>.Err e
 | .Ok _=>if shared then
    match l.partialReply with | .Err e=>.Err e | .Ok _=>l.high
   else .Ok ()

/-- Reviewed transcription of NIW_boundary.rs.txt alignment_boundary. The
scratchReply is the before-call owned oracle value, not a post-hoc witness.
This cut carries only the selected native observation, not a callee equation. -/
def cut (shared : Bool) (partsAddress : Nat) (i slot power : Nat)
 (l : Log) (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit) : Prop :=
 i<16 ∧ slot<7 ∧ power<4 ∧ canonical l.partsReply ∧ canonical l.highPartsReply ∧
 (∀ values,l.partialReply=.Ok values → canonical values) ∧
 out=expected shared l ∧
 l.count=(if ¬enteredPartial shared l then 1 else if ¬enteredHigh shared l then 3 else 4) ∧
 l.events 0=0 ∧
 (enteredPartial shared l → l.events 1=1 ∧ l.events 2=2) ∧
 (enteredHigh shared l → l.events 3=3) ∧
 alloc.vec.Vec.deref afterScratch=alloc.vec.Vec.deref l.scratchReply ∧ (alloc.vec.Vec.deref afterScratch).val.length=64 ∧
 epick afterParts slot=epick (if enteredHigh shared l then l.highPartsReply else l.partsReply) slot ∧
 (enteredPartial shared l → l.partialCommon=kpick l.commonReply i) ∧
 (enteredHigh shared l → l.highPointer=partsAddress ∧
  l.highBefore=epick l.partsReply slot ∧
  ∀ values,l.partialReply=.Ok values → l.highPartial=epick values power)

/-- Mutable post of regular is precisely the pre-value observed at high's
selected cell, even if high itself returns Err after modifying Parts. -/
theorem regular_to_high (shared : Bool) (partsAddress : Nat) (i slot power : Nat)
 (l : Log) (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared partsAddress i slot power l afterScratch afterParts out)
 (entered : enteredHigh shared l) :
 l.highPointer=partsAddress ∧ l.highBefore=epick l.partsReply slot := by
 rcases native with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,high⟩
 exact ⟨(high entered).1,(high entered).2.1⟩

/-- The native partial/high boundary forwards the actual successful array,
not a selected model array with a coincident address. -/
theorem partial_to_high (shared : Bool) (partsAddress : Nat) (i slot power : Nat)
 (l : Log) (afterScratch : Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared partsAddress i slot power l afterScratch afterParts out)
 (entered : enteredHigh shared l) (values : Powers) (returned : l.partialReply=.Ok values) :
 l.highPartial=epick values power := by
 rcases native with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,high⟩
 exact (high entered).2.2 values returned

#print axioms regular_to_high
#print axioms partial_to_high
end AspisR1.NIW_AlignBoundary
