import Mathlib.Tactic.Ring

/-! Source-shaped helper dependence of the pair-forest terminal, including
its inactive-helper mu^2 term. Abstract field operations only; no claim
that a fixed C1 context stays fixed under a witness change. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [CommRing F]

def helperCopy (a b c p h : F) : F := a * (h * b + c) - b * p

def helperTerminal (mask eta eq thetaPower active a b c p rest mu h : F) : F :=
  mask + eta * (eq * (thetaPower * active * helperCopy a b c p h + rest) +
    mu * h + mu * mu * ((1 - active) * h))

theorem helperTerminal_difference
    (mask eta eq thetaPower active a b c p rest mu h delta : F) :
    helperTerminal mask eta eq thetaPower active a b c p rest mu (h + delta) -
      helperTerminal mask eta eq thetaPower active a b c p rest mu h =
    eta * (eq * thetaPower * active * a * b + mu + mu * mu * (1 - active)) * delta := by
  simp only [helperTerminal, helperCopy]
  ring

/-- The actual two Horner lane loops multiply a difference in the starting
copy residual by theta once per lane; lane contents are unchanged here. -/
theorem horner_start_difference (theta x delta : F) (lanes : List F) :
    lanes.foldl (fun acc lane => theta * acc + lane) (x + delta) -
      lanes.foldl (fun acc lane => theta * acc + lane) x =
    theta ^ lanes.length * delta := by
  induction lanes generalizing x delta with
  | nil => simp
  | cons lane lanes ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h := ih (theta * x + lane) (theta * delta)
    have he : theta * (x + delta) + lane = (theta * x + lane) + theta * delta := by ring
    rw [he, h]
    ring

#print axioms helperTerminal_difference
#print axioms horner_start_difference
end AspisV8R17
