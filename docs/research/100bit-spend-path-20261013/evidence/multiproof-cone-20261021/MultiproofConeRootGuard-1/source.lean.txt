import MultiproofConeLeafFold
import MultiproofConePhysicalFrozenLevels

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeRootGuard
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalViews MultiproofConeLeafFold
open OraclePortFrozenOrder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
attribute [local instance] Classical.propDecidable

def sourceRoot (root : Digest) (physical : Slice U8) (s : reference.Scratch) : Bool :=
  decide (s.n.val=1 ∧ s.idx.val[0]!.val=0 ∧ s.val.val[0]! = root ∧ s.«at».val=physical.val.length)

def modelRoot (root : State) : Option (Live × Bytes) → Bool
  | some ([(i,d)],remaining) => decide (i=0 ∧ d=root ∧ remaining=[])
  | _ => false

theorem live_length (s : reference.Scratch) (start count : Nat) :
    (live s start count).length=count := by
  simp only [live,MultiproofConePhysicalLive.view,List.length_map,List.length_range]

theorem cursor_empty (physical : Slice U8) (cursor : Usize)
    (bound : cursor.val≤physical.val.length) :
    remaining physical cursor=[] ↔ cursor.val=physical.val.length := by
  constructor
  · intro eq
    have len := congrArg List.length eq
    simp only [remaining,MultiproofConeCanonical.bytesOf,List.length_map,List.length_drop,List.length_nil] at len
    omega
  · intro eq
    simp only [remaining,MultiproofConeCanonical.bytesOf,eq,List.drop_length,List.map_nil]

/-- The source compares the final physical digest and exact cursor, not just
the root's bytes in isolation. Singleton Live and empty remaining are equivalent. -/
theorem root_guard (root : Digest) (physical : Slice U8) (s : reference.Scratch)
    (bound : s.«at».val≤physical.val.length) :
    sourceRoot root physical s =
      modelRoot (decodeState root) (some (live s 0 s.n.val,remaining physical s.«at»)) := by
  by_cases one : s.n.val=1
  · simp only [sourceRoot,one,eq_self_iff_true,true_and,live_cons,live_empty,
      MultiproofConePhysicalLive.cell,decodeEntry,modelRoot,Nat.zero_add,decode_injective,
      cursor_empty physical s.«at» bound]
  · have len := live_length s 0 s.n.val
    cases eq : live s 0 s.n.val with
    | nil => simp [sourceRoot,one,modelRoot,eq]
    | cons entry rest =>
      cases rest with
      | nil => simp only [eq,List.length_singleton] at len;exact (one len.symm).elim
      | cons next tail => simp [sourceRoot,one,modelRoot,eq]

#print axioms live_length
#print axioms cursor_empty
#print axioms root_guard
end AspisR1.MultiproofConeRootGuard
end
