import R1Z.PV_OptB_FixturePoleDifference
import R1Z.MaskImageVR1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_ChallengePair
open R0P R0Z.HonestView
variable {K : Type} [Field K]

def replace (base : Challenges K) (lam chi : K) : Challenges K :=
  {base with sem := fun i => if i = 0 then lam else if i = 1 then chi else base.sem i}

theorem first (base : Challenges K) (lam chi : K) : (replace base lam chi).sem 0 = lam := by
  simp [replace]

theorem second (base : Challenges K) (lam chi : K) : (replace base lam chi).sem 1 = chi := by
  simp [replace]

/-- Other observer-relevant challenge fields are retained exactly. -/
theorem retained (base : Challenges K) (lam chi : K) :
    (replace base lam chi).circle = base.circle ∧
    (replace base lam chi).opening = base.opening ∧
    (replace base lam chi).queries = base.queries := ⟨rfl,rfl,rfl⟩

#print axioms first
#print axioms second
#print axioms retained
end R1Z.PV_OptB_ChallengePair
