import R1Z.PV_RunJoin_RuntimeBody38
import R1Z.PV_W_ErrorSyntax
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeFault38
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]
variable {W S F D DF ZF C : Type}

def run (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (input : PV_RunJoin_RuntimeBody38.Inputs) (secret : PV_RunJoin_RuntimeBody38.Secret) :=
  PV_W_ErrorSyntax.actionError PV_W_OsFile.Fault.extraction
    (PV_RunJoin_RuntimeBody38.run base memory input secret)

/-- Put the actual entry on the OS-fault carrier without changing any of its
ordered effects or final world. OS reply interpretation remains runtime data. -/
theorem executes (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (input : PV_RunJoin_RuntimeBody38.Inputs) (secret : PV_RunJoin_RuntimeBody38.Secret) :
    PV_W_Syntax.eval
      (fun op => PV_W_ErrorSyntax.actionError PV_W_OsFile.Fault.extraction
        (PV_W_ReachedThreading.interpret (PV_RunJoin_RuntimeMemory38.algebra base memory) op))
      (PV_W_ErrorSyntax.programError PV_W_OsFile.Fault.extraction
        (PV_RunJoin_RuntimeBody38.program input secret)) = run base memory input secret :=
  PV_W_ErrorSyntax.error_eval _ _ _

theorem world_and_calls (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (input : PV_RunJoin_RuntimeBody38.Inputs) (secret : PV_RunJoin_RuntimeBody38.Secret) (w : W) :
    (run base memory input secret w).world=(PV_RunJoin_RuntimeBody38.run base memory input secret w).world ∧
    (run base memory input secret w).calls=(PV_RunJoin_RuntimeBody38.run base memory input secret w).calls :=
  ⟨rfl,rfl⟩

theorem failed (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (input : PV_RunJoin_RuntimeBody38.Inputs) (secret : PV_RunJoin_RuntimeBody38.Secret)
    (w : W) (e : Aeneas.Std.Error)
    (h : (PV_RunJoin_RuntimeBody38.run base memory input secret w).outcome=.fail e) :
    (run base memory input secret w).outcome=.fail (.extraction e) := by
  change PV_W_ErrorSyntax.outcomeError PV_W_OsFile.Fault.extraction _ = _
  rw [h]
  rfl

#print axioms executes
#print axioms world_and_calls
#print axioms failed
end R1Z.PV_RunJoin_RuntimeFault38
