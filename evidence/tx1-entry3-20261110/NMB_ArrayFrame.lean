import NMB_Stage1Source
set_option autoImplicit false
namespace NMB_ArrayFrame
open Aeneas Aeneas.Std AspisR1
abbrev PE := AdapterRw.solana_program_error.ProgramError
structure Header where
 allocation : Nat
 length : Nat
 capacity : Nat
structure Metadata where
 key : List U8
 owner : List U8
 signer : Bool
 writable : Bool
 executable : Bool
 length : Nat
structure Native where
 metadata : Metadata
 bytes : Except PE Header
structure Value where
 metadata : Metadata
 bytes : Except PE (List U8)
abbrev Heap := Nat → List U8
def value (heap : Heap) (n : Native) : Value :=
 ⟨n.metadata,n.bytes.map (fun h=>(heap h.allocation).take h.length)⟩
/-- Local array-constructor cut transcription: complete headers AND error tags,
and the full old-buffer frame. Header equality alone is deliberately insufficient.
The native modifies check and lifetime/allocator interpretation must supply frame. -/
structure Cut (before after : List Native) (old new : Heap) : Prop where
 headers : after=before
 frame : ∀ n, n∈before → ∀ h, n.bytes=.ok h → new h.allocation=old h.allocation
theorem one (old new : Heap) (n : Native)
 (frame : ∀ h, n.bytes=.ok h → new h.allocation=old h.allocation) :
 value new n=value old n := by
 cases n with
 | mk metadata bytes =>
  cases bytes with
  | error e => rfl
  | ok h =>
   have same := frame h rfl
   simp only [value,Except.map]
   rw [same]
/-- Full byte-value transport uses the SAME old allocations and a proved
frame; it never infers byte equality from an integer address comparison. -/
theorem source (before after : List Native) (old new : Heap) (cut : Cut before after old new) :
 after.map (value new)=before.map (value old) := by
 rw [cut.headers]
 apply List.map_congr_left
 intro n member
 exact one old new n (cut.frame n member)
#print Cut
#print source
#print axioms one
#print axioms source
end NMB_ArrayFrame
