import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace AspisV8R10
variable {K : Type*} [CommRing K]

def copyResidual (d0 d1 d2 d3 w0 w1 w2 w3 h : K) : K :=
  (d0 * d1) * (h * (d2 * d3) + (w2 * d3 + w3 * d2)) -
    (d2 * d3) * (w0 * d1 + w1 * d0)

theorem copy_residual_slope (d0 d1 d2 d3 w0 w1 w2 w3 h delta : K) :
    copyResidual d0 d1 d2 d3 w0 w1 w2 w3 (h + delta) -
      copyResidual d0 d1 d2 d3 w0 w1 w2 w3 h =
        (d0 * d1 * d2 * d3) * delta := by
  unfold copyResidual
  ring

def selectedTerminal (mask rest eq theta active mu eta : K)
    (d0 d1 d2 d3 w0 w1 w2 w3 h : K) : K :=
  mask + eta *
    (eq * (rest + theta ^ 28 * active * copyResidual d0 d1 d2 d3 w0 w1 w2 w3 h) +
      mu * h + mu ^ 2 * (1 - active) * h)

def h1Multiplier (eq theta active mu eta d0 d1 d2 d3 : K) : K :=
  eta * (eq * theta ^ 28 * active * (d0 * d1 * d2 * d3) +
    mu + mu ^ 2 * (1 - active))

theorem selected_terminal_h1_slope (mask rest eq theta active mu eta : K)
    (d0 d1 d2 d3 w0 w1 w2 w3 h delta : K) :
    selectedTerminal mask rest eq theta active mu eta d0 d1 d2 d3 w0 w1 w2 w3 (h + delta) -
      selectedTerminal mask rest eq theta active mu eta d0 d1 d2 d3 w0 w1 w2 w3 h =
        h1Multiplier eq theta active mu eta d0 d1 d2 d3 * delta := by
  unfold selectedTerminal h1Multiplier copyResidual
  ring

theorem inactive_multiplier (eq theta mu eta d0 d1 d2 d3 : K) :
    h1Multiplier eq theta 0 mu eta d0 d1 d2 d3 = eta * (mu + mu ^ 2) := by
  simp [h1Multiplier]

#print axioms copy_residual_slope
#print axioms selected_terminal_h1_slope
#print axioms inactive_multiplier
end AspisV8R10
