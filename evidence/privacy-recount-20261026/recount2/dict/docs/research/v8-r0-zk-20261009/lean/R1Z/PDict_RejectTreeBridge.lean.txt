import R1Z.PDict_RejectTree
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RejectTreeBridge
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_RejectionStd.native
abbrev selected := PDict_RejectionStd.selected
/-- The actual tree caller preserves the external LEAF_BITS outcome and cast,
then rejects empty indices without allocation, hashing, or the count loop. -/
theorem empty_multiproof (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) (tree : host_tree.BinaryTree)
    (indices : Slice U32) (empty : indices.length = 0) :
    @host_tree.BinaryTree.multiproof (native base) (selected base ops) tree indices =
      (do let bits ← (selected base ops).op235
          let _ ← Aeneas.Std.lift (UScalar.cast .Usize bits)
          .ok none) := by
  simp only [host_tree.BinaryTree.multiproof,
    PDict_RejectTree.empty_node_count base ops indices empty,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    PDict_RejectionStd.op9_installed,PDict_RejectionStd.op10_installed,
    PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    PDict_RejectionStdSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    PDict_RejectionStdSource.optionTag]
  simp

#print axioms empty_multiproof
end R1Z.PDict_RejectTreeBridge
