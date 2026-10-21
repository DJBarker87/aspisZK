import OraclePortAcceptedContextC6
import OraclePortSelectedArithmeticC4

/-! Physical checkpoint bytes depend on the selected second-fold observations
and transcript scalars, not on the unqueried coordinates of recovered words. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortCheckpointObservationsC6
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5 OraclePortSelectedArithmeticC4
open AspisPool.AlgorithmicCircleDecoderV7
attribute [local irreducible] OraclePortCheckpointStateC3.write QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis

/-- Recomputed query values agree even when the recovered words have extra
nonselected leaves. -/
theorem model_eq (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (rho : K) (q : Fin 22 → Fin 262144)
    (same : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    model d rho q = model (withWords d W V) rho q := by
  have values := funext (fun j => second_value d W V q j (same j))
  unfold model OraclePortCheckpointStateC3.fromData
  rw [values]

theorem prepared_eq (c : Context) (d : MatchingSupport.Data E)
    (W : Fin 29 → InitialWord E) (V : FinalWord E) (rho : K) (q : Fin 22 → Fin 262144) :
    prepared c d rho q = prepared c (withWords d W V) rho q := rfl

/-- Authentic saved bytes, including the computed ten-step accumulator and
checksum, are identical. No equality of full matching data is needed. -/
theorem save_eq (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (rho : K) (q : Fin 22 → Fin 262144)
    (same : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    save H stored pub c d rho q = save H stored pub c (withWords d W V) rho q := by
  unfold save
  rw [model_eq d W V rho q same,prepared_eq c d W V rho q]

/-- The real oracle Program write/resume values agree on these observations;
the checkpoint is computed inside the program for the same oracle. -/
theorem writeResume_value_eq (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (rho : K) (q : Fin 22 → Fin 262144)
    (same : ∀ j slot, d.V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot) =
      V (childIndex (n := 65536) (parentIndex (n := 65536) (q j)) slot)) :
    (eval H (OraclePortCheckpointOracleC5.writeResume stored pub c d rho q)).2 =
      (eval H (OraclePortCheckpointOracleC5.writeResume stored pub c (withWords d W V) rho q)).2 := by
  rw [OraclePortCheckpointOracleC5.writeResume_value,OraclePortCheckpointOracleC5.writeResume_value]
  have values := funext (fun j => second_value d W V q j (same j))
  rw [values]

#print axioms model_eq
#print axioms prepared_eq
#print axioms save_eq
#print axioms writeResume_value_eq
end AspisR1.OraclePortCheckpointObservationsC6
end
