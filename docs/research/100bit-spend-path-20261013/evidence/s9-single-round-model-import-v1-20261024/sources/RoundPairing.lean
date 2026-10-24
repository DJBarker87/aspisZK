/- Import-name adapter only. The historical caller already imports
R1RoundPairing. Load that same retained module for new callers of RoundPairing,
so there is one definition owner. No declaration or mathematical body is added.
The focused comparison records identical shared types/computational bodies and
separately records renamed compiler-generated theorem helpers. -/
import R1RoundPairing
#print axioms AspisR1.RoundPairing.round_boundary
#print axioms AspisR1.RoundPairing.dualFold_horner
