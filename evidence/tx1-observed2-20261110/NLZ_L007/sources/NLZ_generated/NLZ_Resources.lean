import NLJ_ObservedInitial
import NLR_PrepareInitialized
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Resources
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Resource carrier for the pending physical segment interpretation. IDs are
allocation identities, not integer-address equality proofs. -/
structure Object where
 bytes : List U8
 alignment : Nat
 owner : Nat
 initialized : List Bool
 deriving DecidableEq
structure Heap where
 objects : Nat → Option Object
 external : Nat → List U8
 metadata : Nat → List Nat
 borrowCount : Nat → Int
structure Window where
 allocation : Nat
 offset : Nat
 length : Nat
 deriving DecidableEq
inductive Effect where
 | allocate (id size align : Nat) (succeeded : Bool)
 | write (at : Window) (bytes : List U8)
 | acquire (at : Window) (exclusive : Bool)
 | release (at : Window) (exclusive : Bool)
 | drop (id : Nat)
 | digest (attempt : PreparedHashCode.Log)
 | abort
/-- Entire before/after states are retained at each occurrence. No resource
law is inferred from constructing this record. -/
structure Occurrence where
 before : Heap
 after : Heap
 effects : List Effect
/-- All fields outside a finite modified allocation set are framed, including
account metadata and borrow counters. -/
def Frame (allowed : List Nat) (a b : Heap) : Prop :=
 (∀ id, id ∉ allowed → b.objects id = a.objects id) ∧
 b.external = a.external ∧ b.metadata = a.metadata ∧
 b.borrowCount = a.borrowCount
/-- Physical window content and initialization, never pointer-only identity. -/
def View (h : Heap) (w : Window) (bytes : List U8) : Prop :=
 ∃ o, h.objects w.allocation = some o ∧
 w.offset + w.length ≤ o.bytes.length ∧ bytes.length = w.length ∧
 (o.bytes.drop w.offset).take w.length = bytes ∧
 (o.initialized.drop w.offset).take w.length = List.replicate w.length true
end AspisR1.NLZ_Resources
end
