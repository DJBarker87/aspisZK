import CompPoly.Univariate.DivisionCorrectness
import Lean.Elab.Tactic

namespace PrivateDivStepBridgeV2
open CompPoly Lean Elab Tactic Meta
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

elab "apply_hidden_div_step" : tactic => do
  let n0 := Name.str Name.anonymous "_private"
  let n1 := Name.str n0 "CompPoly"
  let n2 := Name.str n1 "Univariate"
  let n3 := Name.str n2 "DivisionCorrectness"
  let n4 := Name.num n3 0
  let n5 := Name.str n4 "CompPoly"
  let n6 := Name.str n5 "CPolynomial"
  let n := Name.str n6 "div_step_size_lt"
  let e ← Lean.Meta.mkConstWithFreshMVarLevels n
  let g ← getMainGoal
  let gs ← g.apply e
  replaceMainGoal gs

/-- Exact active-step size decrease used internally by pinned CompPoly long division. -/
theorem monic_division_step_size_lt (p q : CPolynomial.Raw F)
    (hp : p.trim = p) (hq : q.trim = q) (hm : q.leadingCoeff = 1)
    (hsize : ¬ p.size < q.size) (hqpos : 0 < q.size) :
    ((p - CPolynomial.Raw.C p.leadingCoeff *
      (q * CPolynomial.Raw.X ^ (p.size - q.size))).trim).size < p.size := by
  apply_hidden_div_step
  exact hp
  exact hq
  exact hm
  exact hsize
  exact hqpos

#print axioms monic_division_step_size_lt
end PrivateDivStepBridgeV2
