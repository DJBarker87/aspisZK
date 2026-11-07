import NNG_LIBScalar
import NNG_InstallArithmetic
import LIB_VField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBField
open Aeneas Aeneas.Std Result NNG_Transport NNG_LIBScalar

theorem raw_project (fallback : Value) (x : Raw) (h : Domain x) :
    LIB_VScalarCarriers.toRaw (project fallback x) = toT1 x := by
  have same := congrArg toT1 (lower_project fallback x h)
  simpa only [lower,fromT1_inverse] using same
#print axioms raw_project

theorem add (fallback : Value) (x y : Raw) (hx : Domain x) (hy : Domain y) :
    NNG_InstallArithmetic.add x y =
      .ok (lower (LIB_VField.qadd (project fallback x) (project fallback y))) := by
  unfold NNG_InstallArithmetic.add
  rw [←raw_project fallback x hx,←raw_project fallback y hy,LIB_VField.qadd_exact]
  rfl
#print axioms add

theorem mul (fallback : Value) (x y : Raw) (hx : Domain x) (hy : Domain y) :
    NNG_InstallArithmetic.mul x y =
      .ok (lower (LIB_VField.qmul (project fallback x) (project fallback y))) := by
  unfold NNG_InstallArithmetic.mul
  rw [←raw_project fallback x hx,←raw_project fallback y hy,LIB_VField.qmul_exact]
  rfl
#print axioms mul

theorem add_returned (fallback : Value) (x y z : Raw) (hx : Domain x) (hy : Domain y)
    (success : NNG_InstallArithmetic.add x y = .ok z) : Domain z := by
  have same := Result.ok.inj ((add fallback x y hx hy).symm.trans success)
  rw [←same]
  exact lower_domain _
#print axioms add_returned

theorem mul_returned (fallback : Value) (x y z : Raw) (hx : Domain x) (hy : Domain y)
    (success : NNG_InstallArithmetic.mul x y = .ok z) : Domain z := by
  have same := Result.ok.inj ((mul fallback x y hx hy).symm.trans success)
  rw [←same]
  exact lower_domain _
#print axioms mul_returned
end AspisR1.NNG_LIBField
