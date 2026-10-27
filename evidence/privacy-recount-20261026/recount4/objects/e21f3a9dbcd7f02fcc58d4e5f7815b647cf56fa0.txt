import R1Z.ProverRwDictionaryWideQM
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryDomain
open Aeneas Aeneas.Std Result ProverRwFull

-- Retained r17 domain extraction, rebound to the full caller's same Usize
-- carrier and error constructors. The native index_type macro uses this guard.
def fibreNew (i : Usize) : Result (core.result.Result aspis_core.r0.domain.FibreIndex aspis_core.r0.Error) := do
  if i < 262144#usize then .ok (.Ok i) else .ok (.Err .IndexOutOfRange)
def fibreGet (i : aspis_core.r0.domain.FibreIndex) : Result Usize := .ok i

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryWideQM.selected ops with op75 := fibreNew,op76 := fibreGet}

theorem new_source (ops : ExternalFuns) (i : Usize) :
    (selected ops).op75 i =
      (if i < 262144#usize then .ok (.Ok i) else .ok (.Err .IndexOutOfRange)) := rfl

theorem get_source (ops : ExternalFuns) (i : aspis_core.r0.domain.FibreIndex) :
    (selected ops).op76 i = .ok i := rfl

theorem accepted (ops : ExternalFuns) (i : Usize) (bound : i < 262144#usize) :
    (selected ops).op75 i = .ok (.Ok i) := by rw [new_source]; simp only [bound,if_true]

theorem rejected (ops : ExternalFuns) (i : Usize) (bound : ¬ i < 262144#usize) :
    (selected ops).op75 i = .ok (.Err .IndexOutOfRange) := by rw [new_source]; simp only [bound,if_false]

#print axioms new_source
#print axioms get_source
#print axioms accepted
#print axioms rejected
end R1Z.ProverRwDictionaryDomain
