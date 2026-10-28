import R1Z.PV_RDB2_Applied_25_compress
import R1Z.PV_RDB2_P6CompressSource
import R1Z.PV_RDB2_Index

/-! Complete Result law for the actual deployed candidate helper, in the
import-narrowed owned cohort. Only the five arithmetic operations reached by
the compressor are selected. All other dictionary entries remain parameters
and cannot change this helper. No generic native-source correspondence is
obtained merely by declaring an ExternalFuns value. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDB2_Compress
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

@[reducible] def primitives (ops : ExternalFuns) : ExternalFuns :=
  {ops with
    op61 := PV_Op223_Applied.aspis_core.field.CM31.from_m31
    op66 := PV_Op223_Applied.aspis_core.field.QM31.from_cm31
    op67 := PV_Op223_Applied.aspis_core.field.QM31.add
    op69 := PV_Op223_Applied.aspis_core.field.QM31.mul
    op70 := PV_Op223_Applied.aspis_core.field.QM31.mul_m31}

theorem body (ops : ExternalFuns) :
    PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop.body =
      @ProverRwP6CompressSource.compress_loop.body _ (primitives ops) := by
  rfl

theorem loop (ops : ExternalFuns) :
    PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop =
      @ProverRwP6CompressSource.compress_loop _ (primitives ops) := by
  funext values lambda out power i
  unfold PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop
    ProverRwP6CompressSource.compress_loop
  rw [body ops]

/-- Failure, divergence, raw inputs and arbitrary slice lengths are retained. -/
theorem complete (ops : ExternalFuns) :
    PV_Op223_Applied.prover_shared.compress_tagged_tuple =
      @ProverRwP6CompressSource.compress _ (primitives ops) := by
  rfl

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op223 := PV_Op223_Applied.prover_shared.compress_tagged_tuple}

theorem installed (ops : ExternalFuns) :
    (selected ops).op223 = @ProverRwP6CompressSource.compress _ (primitives ops) :=
  complete ops

theorem callback_removed (ops : ExternalFuns)
    (callback : aspis_core.field.M31 → Slice aspis_core.field.M31 →
      aspis_core.field.QM31 → Result aspis_core.field.QM31) :
    (selected {ops with op223 := callback}).op223 = (selected ops).op223 := rfl

#print axioms body
#print axioms loop
#print axioms complete
#print axioms installed
#print axioms callback_removed
end R1Z.PV_RDB2_Compress
