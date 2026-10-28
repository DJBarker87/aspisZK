import R1Z.PV_Join_PublicCaller
import R1Z.PV_Join_ArithmeticCanonical5
import R1Z.PV_Join_ScaleCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_ProducerCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5

theorem p6_add [ExternalTypes] (ops : ExternalFuns)
    (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, (ProverRwP6BodyStore.selected ops).op67 x y = .ok z ∧ Q z := by
  change ∃ z, ProverRwDictionaryTower.qAdd x y = .ok z ∧ Q z
  exact PV_Join_ArithmeticCanonical5.add x y hx hy

theorem p6_mul [ExternalTypes] (ops : ExternalFuns)
    (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, (ProverRwP6BodyStore.selected ops).op69 x y = .ok z ∧ Q z := by
  change ∃ z, ProverRwDictionaryTower.qMul x y = .ok z ∧ Q z
  exact PV_Join_ArithmeticCanonical5.mul x y hx hy

theorem scale (base : ExternalTypes) (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (x : aspis_core.field.QM31) (s : U32) :
    ∃ z, (PV_Join_PublicCaller.selected base ops).op70 x s = .ok z ∧ Q z := by
  change ∃ z, PV_Join_ScaleCanonical5.scale x s = .ok z ∧ Q z
  exact PV_Join_ScaleCanonical5.canonical x s

theorem add (base : ExternalTypes) (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, (PV_Join_PublicCaller.selected base ops).op67 x y = .ok z ∧ Q z := by
  change ∃ z, PV_CurrentQuarticBridge.S.add x y = .ok z ∧ Q z
  rw [PV_CurrentQuarticBridge.add]
  exact PV_Join_ArithmeticCanonical5.add x y hx hy

theorem mul (base : ExternalTypes) (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, (PV_Join_PublicCaller.selected base ops).op69 x y = .ok z ∧ Q z := by
  change ∃ z, PV_CurrentQuarticBridge.S.mul x y = .ok z ∧ Q z
  rw [PV_CurrentQuarticBridge.mul]
  exact PV_Join_ArithmeticCanonical5.mul x y hx hy

#print axioms add
#print axioms mul

#print axioms p6_add
#print axioms p6_mul
#print axioms scale
end R1Z.PV_Join_ProducerCanonical5
