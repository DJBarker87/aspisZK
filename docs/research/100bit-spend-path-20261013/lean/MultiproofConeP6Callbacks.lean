import MultiproofConeP6Batch

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeP6Callbacks
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalDigest MultiproofConeP6Composition
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Parent := Digest → Digest → Program Address Digest Digest

/-- Exact one-call address, arbitrary oracle answer, and no other effects.
The Kani arbitrary-coordinate/length contracts supply this local P6 meaning
for binary_parent and the occupied/sibling callback adapters. This Prop
is explicit; no external proof result is installed as a Lean axiom. -/
def ParentGate (H : Address → Digest) (callback : Parent) : Prop :=
  ∀ left right, eval H (callback left right)=
    ([(parts left right,H (parts left right))],H (parts left right))

def parent (callback : Parent) (s : reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) : Run reference.Row :=
  bind (callback left right) fun digest => .done (finish s digest ni cursor index w)

theorem parent_eq (H : Address → Digest) (callback : Parent) (gate : ParentGate H callback)
    (s : reference.Scratch) (left right : Digest) (ni cursor : Usize) (index : U32) (w : Usize) :
    eval H (parent callback s left right ni cursor index w)=
      eval H (writer s left right ni cursor index w) := by
  simp only [parent,eval_bind,gate left right,eval,List.append_nil]
  rfl

/-- All three callback contracts are consumed at the checked mutation
continuation. In particular a digest-only equation would not prove this. -/
theorem three_parents (H : Address → Digest) (binary occupied sibling : Parent)
    (binaryGate : ParentGate H binary) (occupiedGate : ParentGate H occupied)
    (siblingGate : ParentGate H sibling)
    (s : reference.Scratch) (left right : Digest) (ni cursor : Usize) (index : U32) (w : Usize) :
    eval H (parent binary s left right ni cursor index w)=eval H (writer s left right ni cursor index w) ∧
    eval H (parent occupied s left right ni cursor index w)=eval H (writer s left right ni cursor index w) ∧
    eval H (parent sibling s left right ni cursor index w)=eval H (writer s left right ni cursor index w) :=
  ⟨parent_eq H binary binaryGate s left right ni cursor index w,
    parent_eq H occupied occupiedGate s left right ni cursor index w,
    parent_eq H sibling siblingGate s left right ni cursor index w⟩

/-- Physical source node after the certified window/callback lowering.
Only the parent callbacks vary. Occupied and supplied children retain the
same source order; the actual reply is written before the next node runs. -/
def nodeWith (occupied sibling : Parent) (s : reference.Scratch) (physical : Slice U8)
    (i w : Usize) : Run reference.Row :=
  checked (Array.index_usize s.idx i) fun index =>
  checked (Array.index_usize s.val i) fun value =>
  checked (i+1#usize) fun ni =>
  let supplied : Run reference.Row :=
    checked (Slice.len physical-s.«at») fun remaining =>
    if remaining<32#usize then .done (.ok (.Stop s)) else
    checked (s.«at»+32#usize) fun cursor =>
    checked (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      physical {start:=s.«at»,«end»:=cursor}) fun chunk =>
    checked (reference.read32 chunk) fun valueSibling =>
    if index &&& 1#u32=0#u32 then parent sibling s value valueSibling ni cursor index w
    else parent sibling s valueSibling value ni cursor index w
  if ni<s.n then
    checked (Array.index_usize s.idx ni) fun nextIndex =>
    if nextIndex=index^^^1#u32 then
      checked (Array.index_usize s.val ni) fun right =>
      checked (i+2#usize) fun next => parent occupied s value right next s.«at» index w
    else supplied
  else supplied

theorem checked_eval {α β : Type} (H : Address → Digest) (r : Result α) (f : α → Run β) :
    eval H (checked r f)=match r with
      | .ok x => eval H (f x)
      | .fail e => ([],.fail e)
      | .div => ([],.div) := by
  cases r <;> rfl

theorem conditional_eval {α : Type} (H : Address → Digest) (test : Prop) [Decidable test]
    (yes no : Run α) :
    eval H (if test then yes else no)=if test then eval H yes else eval H no := by
  split <;> rfl

theorem nodeWith_eq (H : Address → Digest) (occupied sibling : Parent)
    (occupiedGate : ParentGate H occupied) (siblingGate : ParentGate H sibling)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    eval H (nodeWith occupied sibling s physical i w)=eval H (node s physical i w) := by
  simp only [nodeWith,node,checked_eval,conditional_eval,
    parent_eq H occupied occupiedGate,parent_eq H sibling siblingGate]

/-- The single-node certificate is derived from the callback contracts.
The window/rebase/node-body lowering is the named P6 source boundary of
nodeWith, not an extra whole-verifier or whole-level premise. -/
theorem node_gate (H : Address → Digest) (occupied sibling : Parent)
    (occupiedGate : ParentGate H occupied) (siblingGate : ParentGate H sibling) :
    NodeGate H (nodeWith occupied sibling) := by
  intro physical _ s i w _ _
  exact nodeWith_eq H occupied sibling occupiedGate siblingGate s physical i w

#print axioms parent_eq
#print axioms three_parents
#print axioms checked_eval
#print axioms conditional_eval
#print axioms nodeWith_eq
#print axioms node_gate
end AspisR1.MultiproofConeP6Callbacks
end
