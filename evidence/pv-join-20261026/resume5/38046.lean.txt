import R1Z.PV_Join_OwnedStep5_11
import R1Z.PV_Join_OwnedCtBridge5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_OwnedScalarBridge5
open Aeneas Aeneas.Std Result
namespace S
abbrev F := PV_Join_Direct5Source.aspis_core.field.M31
end S

theorem reduce (x : U64) : PV_Join_Direct5Source.aspis_core.field.M31.reduce_u64 x =
    AspisR1ProducerRelease47.field.M31.reduce_u64 x := by
  simp only [PV_Join_Direct5Source.aspis_core.field.M31.reduce_u64,
    PV_Join_Direct5Source.aspis_core.field.reduce_u64,PV_Join_OwnedCtBridge5.reduce,
    AspisR1ProducerRelease47.field.M31.reduce_u64]

theorem mul (a b : U32) : PV_Join_Direct5Source.aspis_core.field.M31.mul a b =
    AspisR1ProducerRelease47.field.M31.mul a b := by
  simp only [PV_Join_Direct5Source.aspis_core.field.M31.mul,
    PV_Join_Direct5Source.aspis_core.field.reduce_u64,PV_Join_OwnedCtBridge5.reduce,
    AspisR1ProducerRelease47.field.M31.mul,lift,bind_tc_ok]

theorem add (a b : U32) : PV_Join_Direct5Source.aspis_core.field.M31.add a b =
    AspisR1ProducerRelease47.field.M31.add a b := by
  unfold PV_Join_Direct5Source.aspis_core.field.M31.add
  change (do let x ← PV_Join_OwnedCtBridge5.S.add a b; ok x) = _
  rw [PV_Join_OwnedCtBridge5.add]
  cases AspisR1ProducerRelease47.field.M31.add a b <;> rfl

theorem sub (a b : U32) : PV_Join_Direct5Source.aspis_core.field.M31.sub a b =
    AspisR1ProducerRelease47.field.M31.sub a b := by
  unfold PV_Join_Direct5Source.aspis_core.field.M31.sub
  change (do let x ← PV_Join_OwnedCtBridge5.S.sub a b; ok x) = _
  rw [PV_Join_OwnedCtBridge5.sub]
  cases AspisR1ProducerRelease47.field.M31.sub a b <;> rfl

#print axioms reduce
#print axioms mul
#print axioms add
#print axioms sub
end R1Z.PV_Join_OwnedScalarBridge5
