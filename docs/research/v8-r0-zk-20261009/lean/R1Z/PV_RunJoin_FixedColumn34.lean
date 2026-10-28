import R1Z.PV_CBL_ArrayCopied
import R1Z.PV_CBL_ArrayExt
import R1Z.PV_W_R_FixedColumn
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixedColumn34
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

/-- Literal source loop identity, preserving the complete Result; this is
not a native library/copy certificate. No concrete loop is reduced. -/
theorem loop_source (values : Slice Q) (out : Array Q 1024#usize) (i : Usize) :
    prover.fixed_k_column_loop values out i =
      PV_CBL_ArrayKernel.array_reference_loop values out i := rfl

/-- Symbolic traversal of exactly 1024 input cells. The initial contents
are irrelevant because every cell is overwritten before return. -/
theorem loop_exact (input out : Array Q 1024#usize) :
    prover.fixed_k_column_loop (Array.to_slice input) out 0#usize = .ok input := by
  letI : Inhabited Q := ⟨input.val[0]' (by rw [input.property]; decide)⟩
  rw [loop_source]
  obtain ⟨a,ha,hcopy⟩ := PV_CBL_ArrayCopied.total_copied (Array.to_slice input)
    (by simp only [Array.to_slice,input.property]; rfl) out 0#usize (by decide)
    (PV_CBL_ArrayPrefix.initial _ _)
  have selfcopy : PV_CBL_ArrayPrefix.copied input (Array.to_slice input) (1024#usize).val := by
    intro j hj hn
    rfl
  have same := PV_CBL_ArrayExt.copied_unique a input (Array.to_slice input) hcopy selfcopy
  exact ha.trans (congrArg Result.ok same)

/-- Entire emitted helper, including failure/divergence of its ZERO leaf.
Only the array-copy loop is discharged here; no native allocation purity is
asserted by this value equation. -/
theorem complete (input : Array Q 1024#usize) :
    prover.fixed_k_column (Array.to_slice input) =
      (do let _ ← aspis_core.field.QM31.ZERO; .ok input) := by
  unfold prover.fixed_k_column
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q hq
  exact loop_exact input _

/-- The recursively reified pv-world helper has the same complete source
Result, retaining its ZERO failure and divergence boundary. -/
theorem world_source (ops : ExternalFuns) (input : Array Q 1024#usize) :
    PV_W_ReachedEffects.erase ops (PV_W_R_FixedColumn.program (Array.to_slice input)) =
      (do let _ ← @aspis_core.field.QM31.ZERO _ ops; .ok input) := by
  rw [PV_W_R_FixedColumn.erase_program]
  exact @complete _ ops input

#print axioms loop_source
#print axioms loop_exact
#print axioms complete
#print axioms world_source
end R1Z.PV_RunJoin_FixedColumn34
