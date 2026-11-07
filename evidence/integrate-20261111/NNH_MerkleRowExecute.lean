import NJV_NativeRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleRowExecute
open Aeneas Aeneas.Std NJP_RowModel NJP_NativeRowCut
attribute [local instance] Classical.propDecidable
/-- Literal native one-step capture, computed from the current row state.
The digest request is independent of the returned digest and write payload. -/
def seed (nodes : Nat → U8) (length : Nat) (s : Scratch) (i w : Nat) : Log where
 calls := if writes s i length then 1 else 0
 kind := if paired s i then 1 else 2
 callIndex := i
 values := s.values
 sibling := window nodes s.cursor
 left := decide (index s i % 2 = 0)
 writeCalls := if writes s i length then 1 else 0
 writeIndex := w
 writeDigest := fun _ => 0#u8

def capture (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
 (s : Scratch) (i w : Nat) : Log :=
 { seed nodes length s i w with writeDigest := H (request (seed nodes length s i w)) }

def after (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
 (s : Scratch) (i w : Nat) : Scratch where
 indices := fun k => if writes s i length ∧ k.val=w then index s i / 2 else s.indices k
 values := fun k j => if writes s i length ∧ k.val=w
  then H (request (capture H nodes length s i w)) j else s.values k j
 n := s.n
 cursor := NJP_NativeRowCut.cursor s i length

def returned (s : Scratch) (i length : Nat) : Bool :=
 decide (¬i<s.n ∨ paired s i ∨ s.cursor+32≤length)

/-- Every field of the already admitted native cut is constructed from this
SAME prestate and oracle reply. No endpoint or native invocation is assumed. -/
theorem cut (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
 (s : Scratch) (i w : Nat) :
 Cut s i w length nodes (H (request (capture H nodes length s i w)))
  (after H nodes length s i w) (nextI s i length)
  (if writes s i length then w+1 else w) (returned s i length)
  (capture H nodes length s i w) := by
 constructor
 · rfl
 · intro _; rfl
 · intro _; rfl
 · intro _ k j; rfl
 · intro _ _ _ j; rfl
 · intro _ _ _; rfl
 · rfl
 · intro _; rfl
 · intro _ j; rfl
 · rfl
 · rfl
 · intro k; rfl
 · intro k j; rfl
 · rfl
 · rfl
 · rfl
#print axioms cut
end AspisR1.NNH_MerkleRowExecute
