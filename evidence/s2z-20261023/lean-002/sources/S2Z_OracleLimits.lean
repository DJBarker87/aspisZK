import S2Z_Oracle

set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Z.Oracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- A nonreturning backend satisfies the successful-call law vacuously.
Thus totality cannot be silently inferred from CheckpointBytes5Inputs.Oracle. -/
theorem nonreturning_success_law (ops : AdapterRw.Ops) (H : Bytes → State) :
    CheckpointBytes5Inputs.Oracle
      (leadDigest {ops with op43 := fun _ _ => .div}) () H := by
  intro parts digest returned
  change Result.div = ok digest at returned
  cases returned

/-- The SAME dictionary fails the lead's total law at every supplied input.
This is an interface counterexample, not a shipped-backend counterexample. -/
theorem nonreturning_not_total (ops : AdapterRw.Ops) (H : Bytes → State)
    (parts : Parts) :
    (leadDigest {ops with op43 := fun _ _ => .div}).digest () parts ≠
      ok (MultiproofConePhysicalTransport.rawOracle H parts) := by
  intro returned
  cases returned

#print axioms nonreturning_success_law
#print axioms nonreturning_not_total
end AspisR1.S2Z.Oracle
end
