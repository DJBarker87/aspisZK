import PV_B3P_ResidualSource572227
namespace PV_B3P_ResidualFamily572227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_ResidualSource572227
set_option autoImplicit false
/-- All sixteen captured specializations have this exact source-local state
map. Environment/carrier provenance is retained in SOURCE-GUARDS-D572.json. -/
def sourceState {α : Type} (_site : Fin 16) (prior : Store α) (residual : Value α) : Store α :=
  assertionState prior residual

theorem family_guard {α : Type} (site : Fin 16) (prior : Store α) (residual : Value α) :
    condition (sourceState site prior residual) = true :=
  reached_guard _ ⟨prior,residual,rfl⟩

theorem family_certificate {α β : Type} (site : Fin 16)
    (prior : Store α) (residual : Value α) (normal first second : Result β) :
    ¬ diagnostic (condition (sourceState site prior residual) = true) ∧
      branch (condition (sourceState site prior residual) = true) normal first =
        branch (condition (sourceState site prior residual) = true) normal second :=
  source_assertion _ ⟨prior,residual,rfl⟩ normal first second
#print axioms family_guard
#print axioms family_certificate
end PV_B3P_ResidualFamily572227
