import NNG_ConcreteGraph136
import NNG_LIBField
import NNG_LIBMask
import NNG_LIBEvents136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteArithmetic136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays

theorem addMask (fallback : Value) (env : RSL.Env) (x y : Q) (hx : Domain x) (hy : Domain y) :
    RSL.Spec.map (project fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "addMask" (x,y) (NNG_InstallArithmetic.add x y)) env =
      (RSL.Spec.pure (LIB_VField.qadd (project fallback x) (project fallback y))) env := by
  apply NNG_EnvCallGraph136.pure_at (project fallback) NNG_LIBEvents136.events "addMask" (x,y) _ env _ _
  · rw [NNG_LIBField.add fallback x y hx hy]
    exact congrArg Result.ok (project_lower fallback _)
  · rfl
  · exact NNG_LIBEvents136.silent env "addMask" _ _ (by decide) (by decide) (by decide)
#print axioms addMask

theorem addExtra (fallback : Value) (env : RSL.Env) (x y : Q) (hx : Domain x) (hy : Domain y) :
    RSL.Spec.map (project fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "addExtra" (x,y) (NNG_InstallArithmetic.add x y)) env =
      (RSL.Spec.pure (LIB_VField.qadd (project fallback x) (project fallback y))) env := by
  apply NNG_EnvCallGraph136.pure_at (project fallback) NNG_LIBEvents136.events "addExtra" (x,y) _ env _ _
  · rw [NNG_LIBField.add fallback x y hx hy]
    exact congrArg Result.ok (project_lower fallback _)
  · rfl
  · exact NNG_LIBEvents136.silent env "addExtra" _ _ (by decide) (by decide) (by decide)
#print axioms addExtra

theorem multiply (fallback : Value) (env : RSL.Env) (x y : Q) (hx : Domain x) (hy : Domain y) :
    RSL.Spec.map (project fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "multiply" (x,y) (NNG_InstallArithmetic.mul x y)) env =
      (RSL.Spec.pure (LIB_VField.qmul (project fallback x) (project fallback y))) env := by
  apply NNG_EnvCallGraph136.pure_at (project fallback) NNG_LIBEvents136.events "multiply" (x,y) _ env _ _
  · rw [NNG_LIBField.mul fallback x y hx hy]
    exact congrArg Result.ok (project_lower fallback _)
  · rfl
  · exact NNG_LIBEvents136.silent env "multiply" _ _ (by decide) (by decide) (by decide)
#print axioms multiply

theorem mask (fallback : Value) (env : RSL.Env) (claims : LIB_VCarriers.Claims) (alpha : LIB_VCarriers.Alpha) :
    RSL.Spec.map (project fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "mask"
        (NNG_FromFnValues136.low (lowerClaims claims),NNG_FromFnValues136.high (lowerClaims claims),
          NNG_Array136.cell (lowerClaims claims) 27#usize (by decide),lowerArray alpha)
        (NNG_ModelMask.call (NNG_FromFnValues136.low (lowerClaims claims))
          (NNG_FromFnValues136.high (lowerClaims claims))
          (NNG_Array136.cell (lowerClaims claims) 27#usize (by decide)) (lowerArray alpha))) env =
      (RSL.Spec.pure (LIB_VField.maskValue claims alpha)) env := by
  exact NNG_EnvCallGraph136.pure_at (project fallback) NNG_LIBEvents136.events "mask" _ _ env _ _
    (NNG_LIBMask.projected fallback claims alpha) rfl
    (NNG_LIBEvents136.silent env "mask" _ _ (by decide) (by decide) (by decide))
#print axioms mask
end AspisR1.NNG_ConcreteArithmetic136
