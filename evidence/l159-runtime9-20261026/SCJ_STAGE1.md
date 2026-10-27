# Stage 1: implication checked, refuted

SCJ_Projection.event_implies_refuted refutes the proposed universal implication
for the exact release event and Q+2965, not merely equivalence. Both logs are
consistent with one oracle; smaller is a literal sublist; both first-read counts
are at most two. SCJ_001 passes, standard axioms only; exact capped host receipt
in SCJ_001/receipt.json. The collision predicate fires only at FIRST reads and
uses the table available THEN. A colliding pair of projected occurrences need
not be a colliding first read of the full log.

Counterexample (SCI definitions retained, imported read-only):
small = [(bytes one,two),([],one)]
full  = [([],one),(bytes one,two),([],one)].
The projected [] is fresh after bytes one, so one matches its leading parsed
target; the full [] is already cached when repeated. Earlier full [] was clean.
This refutes the claimed sublist justification, not every possible transport
for the particular accepted deployed account. No source attack is claimed.

No endpoint changed and no premise removal claimed. Need an actual-account
causal/first-occurrence preservation theorem, or charge F3X's event separately
with an explicitly revised bound (not authorized here).
