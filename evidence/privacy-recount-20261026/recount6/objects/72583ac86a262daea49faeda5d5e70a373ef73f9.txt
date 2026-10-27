import R1Z.PV_RW_CompressEmission
import R1Z.PV_CurrentScaleInstall
import R1Z.ProverRwP7CompressPrimitives
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressConcrete
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31

-- Closed current extracted field operations: no ExternalFuns callback here.
def step (out power : Q) (value : U32) (lambda : Q) : Result (Q × Q) := do
  let scaled ← PV_CurrentScale.T power value
  let nextOut ← PV_CurrentQuarticBridge.S.add out scaled
  let nextPower ← PV_CurrentQuarticBridge.S.mul power lambda
  ok (nextOut,nextPower)

def owned (out power : Q) (value : U32) (lambda : Q) : Result (Q × Q) := do
  let scaled ← mapResult fromQ
    (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ power) value)
  let nextOut ← qAdd out scaled
  let nextPower ← qMul power lambda
  ok (nextOut,nextPower)

theorem current_owned (out power : Q) (value : U32) (lambda : Q) :
    step out power value lambda = owned out power value lambda := by
  simp only [step,owned,PV_CurrentScale.quartic,PV_CurrentQuarticBridge.add,
    PV_CurrentQuarticBridge.mul]

theorem total (out power : Q) (value : U32) (lambda : Q) :
    ∃ next, step out power value lambda = ok next := by
  obtain ⟨scaled,hs⟩ := ProverRwP7CompressPrimitives.Native.q_scale (toQ power) value
  obtain ⟨nextOut,ho⟩ := ProverRwP6QuarticTotal.add (toQ out) (toQ (fromQ scaled))
  obtain ⟨nextPower,hp⟩ := ProverRwP6QuarticTotal.mul (toQ power) (toQ lambda)
  refine ⟨(fromQ nextOut,fromQ nextPower),?_⟩
  rw [current_owned]
  simp only [owned,hs,qAdd,qMul,ho,hp,mapResult,bind_tc_ok]

#print axioms current_owned
#print axioms total
end R1Z.PV_RW_CompressConcrete
