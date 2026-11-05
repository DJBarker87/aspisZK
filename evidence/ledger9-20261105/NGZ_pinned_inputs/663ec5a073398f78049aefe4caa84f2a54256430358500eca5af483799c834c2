import Lean
import NFY_Part058
import NFY_Part034

set_option autoImplicit false
noncomputable section
namespace NGF_NEY_ReachedResultDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
open AspisR1.S2K
abbrev Statement := StatementAdmission.Statement
abbrev Record := PoolV1PairForestTerminalResultV1

def DerivedRecord (record : Record) : Prop := ∃ s : Statement, record=ResultAdmission.value s

def ReadyRecord (record : Record) : Prop :=
  ∃ s : Statement, record=ResultAdmission.value s ∧
    validate_pool_v1_pair_forest_terminal_statement_v1 s=ok (.Ok ())

theorem binding_argument (s : Statement) : DerivedRecord (ResultAdmission.value s) := ⟨s,rfl⟩

/-- This is the actual reached branch condition at emit_result's encoder call. -/
theorem encoder_argument (s : Statement)
    (bound : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (ResultAdmission.value s)=ok (.Ok ())) : ReadyRecord (ResultAdmission.value s) :=
  ⟨s,rfl,NFY_NEY_BindingSuccess.binding_success s bound⟩

theorem ready_payload (record : Record) (ready : ReadyRecord record) :
    ∃ s : Statement, record=ResultAdmission.value s ∧
      encode_pool_v1_pair_forest_terminal_result_v1 record=
        ok (.Ok (ResultPayload.bytes s)) := by
  obtain ⟨s,same,valid⟩ := ready
  refine ⟨s,same,?_⟩
  rw [same]
  exact ResultPayload.encoded s valid

#print axioms binding_argument
#print axioms encoder_argument
#print axioms ready_payload
end NGF_NEY_ReachedResultDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
