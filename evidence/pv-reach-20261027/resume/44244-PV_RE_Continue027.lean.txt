import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue027
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.BinaryTree.root`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_tree.BinaryTree) (out : Payload (multiproof.LEAF_BITS)) : Result (Array Std.U8 32#usize) := do
  let i := out
  let i1 ← Aeneas.Std.lift (UScalar.cast .Usize i)
  let v ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec
      (Array Std.U8 32#usize))) self.levels i1
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
    32#usize)) v 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : host_tree.BinaryTree) :
    host_tree.BinaryTree.root (self := self) =
      (multiproof.LEAF_BITS >>= fun out => continueAfter (self := self) out) := by
  rw [host_tree.BinaryTree.root]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : host_tree.BinaryTree) (out : Payload (multiproof.LEAF_BITS))
    (h : (multiproof.LEAF_BITS) = .ok out) :
    host_tree.BinaryTree.root (self := self) = continueAfter (self := self) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : host_tree.BinaryTree) (e : Error)
    (h : (multiproof.LEAF_BITS) = .fail e) :
    host_tree.BinaryTree.root (self := self) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : host_tree.BinaryTree)
    (h : (multiproof.LEAF_BITS) = .div) :
    host_tree.BinaryTree.root (self := self) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue027
