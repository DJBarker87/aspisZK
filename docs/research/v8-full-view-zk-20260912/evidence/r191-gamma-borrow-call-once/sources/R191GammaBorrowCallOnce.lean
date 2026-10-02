import AspisV8R19.R174GammaBatchStep

/-! Mechanical wrapper for the selected generated `call_once` body.
Raw body source: `.r21-scratch/r156-full-freeze/generated/AspisR156FullFreeze/Funs.lean`,
lines 1577–1588 (definition
`freeze.closure_2.closure.Insts.CoreOpsFunctionFnOncePairQM31SharedQM31QM31.call_once`).
The sole substitution is the generated `call_mut` function name with
`R174GammaBatchStep.rawCallMut`. -/
set_option autoImplicit false
namespace AspisV8R19.R191GammaBorrowCallOnce

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

def rawCallOnce (c : freeze.closure_2.closure)
    (args : field.QM31 × field.QM31) :
    Result (field.QM31 × freeze.closure_2.closure) := do
  let (_, q) := c
  let (q1, c1, call_mut_back) ←
    AspisV8R19.R174GammaBatchStep.rawCallMut c args
  let (q2, _) := call_mut_back c1
  ok (q1, (q2, q))

theorem rawCallOnce_finishCall (c : freeze.closure_2.closure)
    (args : field.QM31 × field.QM31) :
    rawCallOnce c args =
      AspisV8R17.MaskClosureWriteback.finishCall
        (AspisV8R19.R174GammaBatchStep.rawCallMut c args) := by
  rcases c with ⟨power, gamma⟩
  rcases args with ⟨acc, value⟩
  unfold rawCallOnce AspisV8R17.MaskClosureWriteback.finishCall
    AspisV8R19.R174GammaBatchStep.rawCallMut
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

theorem rawCallOnce_encoded
    (power gamma acc value : AspisV8R15.ExactTowerBase.QM31Exact) :
    rawCallOnce
        (R164ProductExecution.encode power, R164ProductExecution.encode gamma)
        (R164ProductExecution.encode acc, R164ProductExecution.encode value) =
      .ok (R164ProductExecution.encode (acc + power * value),
        (R164ProductExecution.encode (power * gamma),
          R164ProductExecution.encode gamma)) := by
  rw [rawCallOnce_finishCall]
  exact AspisV8R19.R174GammaBatchStep.encoded_closed power gamma acc value

#print axioms rawCallOnce_finishCall
#print axioms rawCallOnce_encoded

end AspisV8R19.R191GammaBorrowCallOnce
