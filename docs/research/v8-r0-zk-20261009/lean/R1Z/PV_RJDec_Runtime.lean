import R1Z.PV_RJDec_Entry
import R1Z.PV_RJDec_MemoryInstalled
import R1Z.PV_RunJoin_RuntimeBody38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Runtime
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]
abbrev Inputs := PV_RunJoin_RuntimeBody38.Inputs
abbrev Secret := PV_RunJoin_RuntimeBody38.Secret
abbrev Output := PV_RunJoin_RuntimeBody38.Output

def program (input : Inputs) (secret : Secret) :=
  PV_RJDec_Entry.program input.publicInput input.compiled .S2
    (PV_RunJoin_RuntimeHash38.reify input.hash) secret input.store

variable {W S F D DF ZF AF C : Type}
def run (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (zero : PV_RJDec_AsmMemory.Memory W AF)
    (input : Inputs) (secret : Secret) : M W (Option C) Aeneas.Std.Error Output :=
  PV_W_Syntax.eval (PV_W_ReachedThreading.interpret (PV_RJDec_MemoryInstalled.algebra base memory zero))
    (program input secret)

theorem source (ops : ExternalFuns) (input : Inputs) (secret : Secret) :
    PV_W_ReachedEffects.erase (PV_RJDec_ZeroizingSelected.selected ops) (program input secret) =
      @prover.prove_masked_attempt _ (PV_RJDec_ZeroizingSelected.selected ops)
        input.publicInput input.compiled .S2 input.hash secret input.store := by
  rw [program,PV_RJDec_Entry.erase_program,PV_RunJoin_RuntimeHash38.source]

theorem executes (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : PV_RunJoin_RuntimeMemory38.Memory W S F D DF ZF)
    (zero : PV_RJDec_AsmMemory.Memory W AF) (input : Inputs) (secret : Secret) (w : W) :
    PV_W_Syntax.Executes
      (PV_W_ReachedThreading.interpret (PV_RJDec_MemoryInstalled.algebra base memory zero))
      (program input secret) w (run base memory zero input secret w) :=
  PV_W_Syntax.execution_complete _ _ _
#print axioms source
#print axioms executes
end R1Z.PV_RJDec_Runtime
