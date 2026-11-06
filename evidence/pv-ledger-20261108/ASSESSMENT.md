# B-y assessment

CLOSED: none. This is an evidence classification, not withdrawal of the earlier
proofs. No new proofs or endpoint premise removals are claimed.

PARTIAL slice: f21 (to_vec), f31 (RawVec with_capacity_in), f35 (try_allocate_in).
PARTIAL thread: f124, f126, f216, f218, f222, f315 and f361.

The ledger records the exact local theorem signatures and individual reasons
for incomplete closure. For 124, WholeReturn retains resolver dispositions;
LocalReturn removes these for its fixed local table, but the complete branch
and frame contract, with CLOSED callee contract applications, is not present.
For 126, the entry root is a legitimate valid-Arc precondition, to be derived
from 124 at the caller. Its body222/child320 dispositions still need discharge.
No counterexample to source is asserted by either classification.

The to_vec call summary is parametric in caller suffix/arguments, but reaches
only source262. Copy, set_len, complete return and memory frame remain. The
QUniformReturn and QColumnViewReturn ownership results are preserved as Post
fragments, with their proof-view context restriction explicit. The cited
raw99109 receipt covers source262 and the f31/f35 fragments, but not those two
older return results; no audit credit for them is inferred from that receipt.

Packet construction and f361 local segments are reusable, not call contracts.
Their citation's exact-root audit coverage is recorded separately (false means
not in that particular receipt, not that no historical audit ever existed).
The earlier and later F0 whole-run results remain contextual evidence only.
OPEN rows do not inherit PARTIAL/CLOSED status merely by occurring on a proved
whole run, or by having generated syntax or a named-child boundary theorem.

All printed hypothesis inventories are currently absent. Source signatures
are explicitly labelled as such, never mislabelled #print output. Future
CLOSED entries must supply a verbatim printed-statement receipt and exhaustive
hypothesis inventory, together with the exact-root raw audit and the actual
callee contract instantiations. A summary-based #print axioms list alone is
insufficient.
