import R1Z.ProverRwP6BindTotal
import R1Z.ProverRwP6BoundaryReduce
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundaryTotal
open Aeneas Aeneas.Std Result ProverRwFull
theorem total (p : Array aspis_core.field.QM31 28#usize) :
    ∃ out, ProverRwP6BoundarySource.boundary_flat p = ok out := by
  unfold ProverRwP6BoundarySource.boundary_flat
  simp only [lift, bind_tc_ok]
  repeat' first
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ArrayRead.read _ _ (by decide)); intro _
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BoundaryStep.total _ _); intro _
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BoundaryReduce.total _); intro _
    | simp only [ProverRwP6BoundarySource.aspis_core.field.CM31.new,
        ProverRwDictionaryBytes.Src.complex,
        ProverRwDictionaryBytesSource.aspis_core.field.CM31.new, bind_tc_ok]
  exact ⟨_, rfl⟩
#print axioms total
end R1Z.ProverRwP6BoundaryTotal
