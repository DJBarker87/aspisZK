import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee017
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.build_with_helper_mode` (callee `host_semantic.check_semantic_columns`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error)) (CommitmentsInst : host_semantic.Commitments T2) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1) (commitments : T2) (hash : H) (variant : transport.Variant) :
  ∃ next, host_semantic.build_with_helper_mode (H := H) (T1 := T1) (T2 := T2) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst := coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst) (CommitmentsInst := CommitmentsInst) (public1 := public1) (c1 := c1) (d := d) (g := g) (h1_padding := h1_padding) (helper := helper) (commitments := commitments) (hash := hash) (variant := variant) =
    (host_semantic.check_semantic_columns c1 d g >>= next) := by
  unfold host_semantic.build_with_helper_mode
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee017
