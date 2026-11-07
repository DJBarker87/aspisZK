# Replaced proof attempts

49666/49667: F33 adapter elaboration failed in a combined simp on the root
entry projections and actual run equality.49666 retained opaque entry
projections;49667 unfolded start inside the run before reached could rewrite
it. Both exact failed inputs and logs are retained. Neither is accepted or
loaded by another proof. No memory failure or cap change occurred.

The combined-simplification shape is retired after two failures. Replacement:
derive the frame/event entry projections separately, then explicitly unfold
the eligibility predicate and rewrite the actual run equality before assembling
the witness. The model, theorem statement, domain and machine remain unchanged.
