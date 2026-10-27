# Byte contracts and non-vacuity

K015 verifies CM31's exact eight bytes with a dynamic slice footprint. K016's
parent substitution hits a pinned compiler ICE. K017's individual-byte footprint
is rejected by the bulk memcpy assigns check. K018 verifies the sized-array
footprint instead; K019's parent composition times out. K020's32-byte return
contract also times out. None of these failures is a shipped-code bug, a verified
parent or an increase in permitted resource use. Their complete source patches
and receipts are retained; no failed callee is substituted into a credited caller.

L010 checks source witnesses for zero/max-u64 reduction and a nonzero product.
L009's broad scalar simplification hit recursion depth; it was replaced by the
explicit small residue computation without increasing maxRecDepth. The rejected
recovery report is retained. L011 proves checked u64 product cuts for full widened
u32 limbs and small-constant products, standard axioms only. These cuts do not
establish the four-coordinate Q.raw law or an actual-top joint witness.

The quiet-window admission refusals at14:30 are waits, never launches. K021's
reservation-only invocation was cancelled to leave exactly one serial pending
launch (L012). Source writing and receipt audits continue during the window.
