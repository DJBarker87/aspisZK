import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue026
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.BinaryTree.multiproof`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_tree.BinaryTree) (indices : Slice Std.U32) (out : Payload (multiproof.LEAF_BITS)) : Result (Option (alloc.vec.Vec Std.U8)) := do
  let i := out
  let bits ← Aeneas.Std.lift (UScalar.cast .Usize i)
  let o ← host_tree.node_count indices
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize val)
    let out := alloc.vec.Vec.with_capacity Std.U8 i1
    let level ← alloc.slice.Slice.to_vec core.clone.CloneU32 indices
    let out1 ← host_tree.multiproof_levels self out level 0#usize bits
    let i2 := alloc.vec.Vec.len out1
    let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize val)
    if i2 = i3
    then ok (some out1)
    else ok none
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      (alloc.vec.Vec Std.U8) residual

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (self : host_tree.BinaryTree) (indices : Slice Std.U32) :
    host_tree.BinaryTree.multiproof (self := self) (indices := indices) =
      (multiproof.LEAF_BITS >>= fun out => continueAfter (self := self) (indices := indices) out) := by
  rw [host_tree.BinaryTree.multiproof]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (self : host_tree.BinaryTree) (indices : Slice Std.U32) (out : Payload (multiproof.LEAF_BITS))
    (h : (multiproof.LEAF_BITS) = .ok out) :
    host_tree.BinaryTree.multiproof (self := self) (indices := indices) = continueAfter (self := self) (indices := indices) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (self : host_tree.BinaryTree) (indices : Slice Std.U32) (e : Error)
    (h : (multiproof.LEAF_BITS) = .fail e) :
    host_tree.BinaryTree.multiproof (self := self) (indices := indices) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (self : host_tree.BinaryTree) (indices : Slice Std.U32)
    (h : (multiproof.LEAF_BITS) = .div) :
    host_tree.BinaryTree.multiproof (self := self) (indices := indices) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue026
