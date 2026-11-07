import NNG_ConcreteArithmetic136
import NNG_ProjectMaskDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteMaskDomain136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain

theorem occurrence (fallback : Value) (env : RSL.Env) (claims : Claims) (alpha : Alpha)
    (lowDom : DomainArray (NNG_FromFnValues136.low claims))
    (highDom : DomainArray (NNG_FromFnValues136.high claims))
    (blindDom : Domain (NNG_Array136.cell claims 27#usize (by decide))) (alphaDom : DomainArray alpha) :
    RSL.Spec.map (project fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "mask"
        (NNG_FromFnValues136.low claims,NNG_FromFnValues136.high claims,
          NNG_Array136.cell claims 27#usize (by decide),alpha)
        (NNG_ModelMask.call (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims)
          (NNG_Array136.cell claims 27#usize (by decide)) alpha)) env =
      (RSL.Spec.pure (LIB_VField.maskValue (projectClaims fallback claims) (projectArray fallback alpha))) env := by
  apply NNG_EnvCallGraph136.pure_at (project fallback) NNG_LIBEvents136.events "mask" _ _ env _ _
  · rw [NNG_ProjectMaskDomain.call_model fallback claims alpha lowDom highDom blindDom alphaDom]
    exact congrArg Result.ok (project_lower fallback _)
  · rfl
  · exact NNG_LIBEvents136.silent env "mask" _ _ (by decide) (by decide) (by decide)
#print axioms occurrence
end AspisR1.NNG_ConcreteMaskDomain136
