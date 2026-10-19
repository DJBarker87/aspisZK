import M31WideExactPacking

set_option autoImplicit false

namespace M31RetryOutputFiber

open M31AcceptFiber

/-- Equality is tested on the eight retained canonical M31 coordinates of a
wide field element.  This is executable over `Fin 8`; it never searches the
`P31^8` field carrier. -/
def wideExactOutputCoordinates (x : WideExactOutput) : EightValues :=
  outputToWideExact.symm x

def wideExactOutputEqb (x y : WideExactOutput) : Bool :=
  decide (wideExactOutputCoordinates x 0 = wideExactOutputCoordinates y 0) &&
  decide (wideExactOutputCoordinates x 1 = wideExactOutputCoordinates y 1) &&
  decide (wideExactOutputCoordinates x 2 = wideExactOutputCoordinates y 2) &&
  decide (wideExactOutputCoordinates x 3 = wideExactOutputCoordinates y 3) &&
  decide (wideExactOutputCoordinates x 4 = wideExactOutputCoordinates y 4) &&
  decide (wideExactOutputCoordinates x 5 = wideExactOutputCoordinates y 5) &&
  decide (wideExactOutputCoordinates x 6 = wideExactOutputCoordinates y 6) &&
  decide (wideExactOutputCoordinates x 7 = wideExactOutputCoordinates y 7)

theorem wideExactOutputEqb_eq_true_iff (x y : WideExactOutput) :
    wideExactOutputEqb x y = true ↔ x = y := by
  simp only [wideExactOutputEqb, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    have h0 := h.1.1.1.1.1.1.1
    have h1 := h.1.1.1.1.1.1.2
    have h2 := h.1.1.1.1.1.2
    have h3 := h.1.1.1.1.2
    have h4 := h.1.1.1.2
    have h5 := h.1.1.2
    have h6 := h.1.2
    have h7 := h.2
    have hcoords : wideExactOutputCoordinates x = wideExactOutputCoordinates y := by
      funext i
      fin_cases i <;> assumption
    exact outputToWideExact.symm.injective hcoords
  · intro h
    subst y
    simp

@[reducible]
def wideExactOutputDecidableEq : DecidableEq WideExactOutput := by
  intro x y
  by_cases h : wideExactOutputEqb x y = true
  · exact isTrue (wideExactOutputEqb_eq_true_iff x y |>.1 h)
  · exact isFalse (fun hxy => h (wideExactOutputEqb_eq_true_iff x y |>.2 hxy))

#print axioms wideExactOutputEqb_eq_true_iff

end M31RetryOutputFiber
