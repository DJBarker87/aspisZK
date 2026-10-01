import AspisV8R19.R165QuarticExecution
import AspisV8R17.MaskClosureWriteback

set_option autoImplicit false
namespace AspisV8R19.R174GammaBatchStep

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

def rawCallMut (c : freeze.closure_2.closure)
    (tupled_args : field.QM31 × field.QM31) :
    Result (field.QM31 × freeze.closure_2.closure ×
      (freeze.closure_2.closure → freeze.closure_2.closure)) := do
  let (q, q1) := c
  let (a, v) := tupled_args
  let q2 ← field.QM31.mul q v
  let r ← field.QM31.add a q2
  let q3 ← field.QM31.mul q q1
  let back := fun c1 => let (q4, _) := c1
                        (q4, q1)
  ok (r, (q3, q1), back)

theorem rawCallMut_closed (power gamma acc value : field.QM31) :
    AspisV8R17.MaskClosureWriteback.finishCall
      (rawCallMut (power, gamma) (acc, value)) = (do
      let weighted ← field.QM31.mul power value
      let total ← field.QM31.add acc weighted
      let next ← field.QM31.mul power gamma
      ok (total, (next, gamma))) := by
  unfold rawCallMut
  simp only [AspisV8R17.MaskClosureWriteback.finishCall]
  cases hMulValue : field.QM31.mul power value with
  | fail e => simp [hMulValue]
  | div => simp [hMulValue]
  | ok weighted =>
    cases hAdd : field.QM31.add acc weighted with
    | fail e => simp [hMulValue, hAdd]
    | div => simp [hMulValue, hAdd]
    | ok total =>
      cases hMulGamma : field.QM31.mul power gamma with
      | fail e => simp [hMulValue, hAdd, hMulGamma]
      | div => simp [hMulValue, hAdd, hMulGamma]
      | ok next => simp [hMulValue, hAdd, hMulGamma]

theorem encoded_closed
    (power gamma acc value : AspisV8R15.ExactTowerBase.QM31Exact) :
    AspisV8R17.MaskClosureWriteback.finishCall
      (rawCallMut (R164ProductExecution.encode power, R164ProductExecution.encode gamma)
        (R164ProductExecution.encode acc, R164ProductExecution.encode value)) =
      .ok (R164ProductExecution.encode (acc + power * value),
        (R164ProductExecution.encode (power * gamma), R164ProductExecution.encode gamma)) := by
  rw [rawCallMut_closed]
  simp only [R164ProductExecution.public_product, R165QuarticExecution.add,
    bind_tc_ok]

#print axioms rawCallMut_closed
#print axioms encoded_closed
end AspisV8R19.R174GammaBatchStep
