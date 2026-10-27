# Stage 2: nonvacuous division obstruction

XRp_DivisionObstruction.division_commutation_false (L071) proves, for every
callback index, that the ACTUAL emitted low_base_p_digits closure's full
Result/state output differs from the ACTUAL indexed qm31_div_pass output,
using the SAME typed eight-word input [P,0,0,0,0,0,0,0]. No success hypothesis
is added: nonvacuity proves both executions succeed and exposes both outputs.
The emitted result is (digit0, original rank); indexed is (digit0,[1,0,...,0]).

Proof composition uses sparse body lemmas and an induction on ≤7 zero limbs,
then a restoration-chain law, then the concrete emitted caller prefix and
Array.from_slice's actual length fallback. It does not normalize a large
recurrence. XRp_IndexedTrace uses a finite certificate for the ACTUAL indexed
loop body, with a generic checked loop replay theorem. No emitted loop is
fabricated, no old proved source is edited, and no native bridge is added.

The first required reverse-division commutation law is FALSE in the selected
cohort, so that item is stopped. Whole low_base_p_digits equality remains
OPEN (no complete block-to-final-output counterexample yet). A2 callback,
serializer/query/powers/claim and whole scratch composition remain OPEN.
A3 arithmetic is split after L070's rejected definitional proof; P6 unchanged.
A0-A8 individually OPEN. Actual-top delta0; no new trust or weakened premise.
All accepted new theorem axioms are subsets of the three standard axioms.
No shipped/cfg(kani) file changed; no ELF rebuild or Kani trigger.
