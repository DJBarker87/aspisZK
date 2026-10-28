import NDO_JGf_TX2_Keys
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_Sort
open Aeneas Aeneas.Std Result

theorem source (kind : Nat) : ∃ out : Array U64 16#usize,
    Port4B_Install.leaves.op5 (JGf_TX2_Keys.raw kind) 12#usize=ok out ∧
    out.val.take 12=(OraclePortFrozenOrder.sortedPositions
      (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 kind).map
        (MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 kind) ∧
    out.val.drop 12=(JGf_TX2_Keys.raw kind).val.drop 12 := by
  obtain ⟨out,run,front,suffix⟩ := MultiproofConeSortOrder.sorted_positions
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 kind
    (JGf_TX2_Keys.raw kind) 12#usize (by decide) (JGf_TX2_Keys.prefix_keys kind)
  rw [MultiproofConeSortOrder.source_start_one _ _ (by decide)] at run
  exact ⟨out,run,front,suffix⟩
#print axioms source
end AspisR1.JGf_TX2_Sort
end
