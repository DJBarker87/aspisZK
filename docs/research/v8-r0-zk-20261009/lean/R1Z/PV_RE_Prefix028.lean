import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix028
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_tree.append_levels` (op235).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) :
  ∃ next, @host_tree.append_levels _ _ H aspis_coredigestDigest32Inst hash levels depth =
    (multiproof.LEAF_BITS >>= next) := by
  unfold host_tree.append_levels
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix028
