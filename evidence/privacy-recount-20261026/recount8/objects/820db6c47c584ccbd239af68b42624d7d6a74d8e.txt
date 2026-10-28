import R1Z.ProverRwP6BodyStore
import R1Z.PV_CB3_Op120Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CB3Boundary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev S := PV_CB3_Op120Source.Raw.BoundaryAcc
abbrev R := ProverRwP6BoundarySource.BoundaryAcc
def decode (x : S) : R := ⟨x.a,x.b,x.c,x.d⟩
theorem reduce (x : U64) :
    PV_CB3_Op120Source.Raw.aspis_core.field.ct.reduce64 x =
      ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64 x := by
  unfold PV_CB3_Op120Source.Raw.aspis_core.field.ct.reduce64
    ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
    PV_CB3_Op120Source.Raw.aspis_core.field.ct.subtract_p
    ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
    PV_CB3_Op120Source.Raw.aspis_core.field.P
    ProverRwSuccessNativePorts.aspis_core.field.P AspisR1ProducerRelease47.field.P
  rfl
/-- Compare a single symbolic accumulator step before the fixed straight-line body. -/
theorem step (x : aspis_core.field.QM31) (s : S) :
    (do let t ← PV_CB3_Op120Source.Raw.boundary_acc_step x s; ok (decode t)) =
      ProverRwP6BoundarySource.boundary_acc_step x (decode s) := by
  simp only [PV_CB3_Op120Source.Raw.boundary_acc_step,
    ProverRwP6BoundarySource.boundary_acc_step,decode,lift,bind_assoc_eq,bind_tc_ok]
/-- All 28 inputs stay symbolic; no finite-array enumeration or numeral reduction. -/
theorem body (p : Array aspis_core.field.QM31 28#usize) :
    PV_CB3_Op120Source.Raw.boundary_flat p = ProverRwP6BoundarySource.boundary_flat p := by
  simp (maxSteps := 1000000) only [PV_CB3_Op120Source.Raw.boundary_flat,ProverRwP6BoundarySource.boundary_flat,
    PV_CB3_Op120Source.Raw.boundary_acc_step,ProverRwP6BoundarySource.boundary_acc_step,
    PV_CB3_Op120Source.Raw.aspis_core.field.M31.reduce_u64,
    ProverRwP6BoundarySource.aspis_core.field.M31.reduce_u64,reduce,
    PV_CB3_Op120Source.Raw.aspis_core.field.CM31.new,
    ProverRwP6BoundarySource.aspis_core.field.CM31.new,
    ProverRwDictionaryBytes.Src.complex,lift,bind_assoc_eq,bind_tc_ok]
variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (p : Array aspis_core.field.QM31 28#usize) :
    (ProverRwP6BodyStore.selected ops).op120 p = (PV_CB3_Op120Source.selected ops).op120 p := by
  change ProverRwP6BoundarySource.boundary_flat p = PV_CB3_Op120Source.Raw.boundary_flat p
  exact (body p).symm
theorem op120_source (ops : ExternalFuns) (p : Array aspis_core.field.QM31 28#usize) :
    (ProverRwP6BodyStore.selected ops).op120 p = PV_CB3_Op120Source.Raw.boundary_flat p :=
  (selected_bridge ops p).trans (PV_CB3_Op120Source.op120_source ops p)
#print axioms reduce
#print axioms step
#print axioms body
#print axioms selected_bridge
#print axioms op120_source
end R1Z.PV_Join_CB3Boundary
