import RPz7_PhaseIso
set_option autoImplicit false
/-! Lead-owned S1 phase replacement. The original has no theorems: its only
export is the conflicting abbreviation. The retained S1 carrier now lives in
RPz7_PhaseIso.Phase, with explicit producer/callback/consumer transports. -/
#print axioms RPz7_PhaseIso.Phase
