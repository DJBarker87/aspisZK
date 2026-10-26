import R1Z.PV_CompressModelTotal
import R1Z.ProverRwP7CompressPrimitives
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressInstalledTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes]

theorem stateFold (ops : ExternalFuns) (values : List M) (lambda : Q) (state : Q × Q) :
    letI : ExternalFuns := ProverRwP6BodyStore.selected ops
    ∃ result, PV_CompressList.stateFold values lambda state = ok result := by
  letI : ExternalFuns := ProverRwP6BodyStore.selected ops
  exact PV_CompressModelTotal.stateFold values lambda state
    (ProverRwP7CompressPrimitives.scale ops) (ProverRwP7CompressPrimitives.add ops)
    (ProverRwP7CompressPrimitives.mul ops)

theorem fold (ops : ExternalFuns) (values : List M) (lambda out power : Q) :
    letI : ExternalFuns := ProverRwP6BodyStore.selected ops
    ∃ result, PV_CompressList.fold values lambda out power = ok result := by
  letI : ExternalFuns := ProverRwP6BodyStore.selected ops
  obtain ⟨r,hr⟩ := stateFold ops values lambda (out,power)
  exact ⟨r.1,by simp only [PV_CompressList.fold,hr,bind_tc_ok]⟩
#print axioms stateFold
#print axioms fold
end R1Z.PV_CompressInstalledTotal
