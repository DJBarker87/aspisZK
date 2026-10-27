import R1Z.PV_CBL_WrapperOutcomes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WrapperFailure
open PV_CBL_LibraryShapes
set_option autoImplicit false

theorem core_failure {T A : Type} (e : Error) (b : Result (Buffer A)) :
    PV_CBL_WrapperReference.makeDefault (.fail e : Result T) b=.fail e := by
  rw [PV_CBL_WrapperOutcomes.default_full_result]

theorem core_divergence {T A : Type} (b : Result (Buffer A)) :
    PV_CBL_WrapperReference.makeDefault (.div : Result T) b=.div := by
  rw [PV_CBL_WrapperOutcomes.default_full_result]

theorem buffer_failure {T A : Type} (c : T) (e : Error) :
    PV_CBL_WrapperReference.makeDefault (ok c) (.fail e : Result (Buffer A))=.fail e := by
  rw [PV_CBL_WrapperOutcomes.default_full_result]
#print axioms core_failure
#print axioms core_divergence
#print axioms buffer_failure
end R1Z.PV_CBL_WrapperFailure
