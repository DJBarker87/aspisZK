The exact NFB_NMFBHost.Remaining is OPEN: its S.env2 remains envOf c, while the
slot-bound producer consumes NFB_NMFBHost.env2 c. The existing M1_refuted
already refutes the old clock equality. No proof of equality of these signatures,
no falsehood of Remaining, and no deployed counterexample is claimed. Installing
the corrected signature in a final host/top is outside the permitted unchanged
top and is therefore a finding, not applied here. Delivered/Missing/Associated
and the final NNC_NMFPrimeB term at the exact old signature are NOT delivered.

M1a/M1b/M1c compile as exactly the draft's local obligation types.
M1d is OPEN: local reindexed S5 producer and original acceptance/game
equivalences compile, but the full corrected literal host signature/a0/Exec/
recorder integration does not. Required next result: define the lawful host
representation with S.env2 c = NFB_NMFBHost.env2 c and EnvRep at c.j.slot,
transport the existing interfaces without filtering Realizes, and produce
the concrete Delivered/Missing/Associated terms and Remaining there.
The original Remaining is deliberately unchanged; no coercion from it is proved. M2 (M2a-d including occurrence/native transport), M2e, and M3 compile
without Root0 as an input to the transports. Retained clauses are unchanged.

No Kani/extraction is needed by these remaining obligations: they are Lean host
signature/composition work. No Kani exhaustion or sibling dependency is asserted.

target not yet established
