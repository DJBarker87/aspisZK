# Pre-coherence checkpoint (not the final ledger)

Unchanged NFK replay passes on its exact Git-pinned historical inputs (C3-BIN
is read through a committed byte-pinned overlay; newer rulings are applied
only by NFX). NFS passes through both additive predecessor chains; NFJ
reproduces all 97 checked S rows; NFQ regenerates its exact 21-row/16-function
certificate delta with no changed gate. Receipts: NFX_REPLAY_*.json.

Before the mandatory new combined coherence test, candidate counts are
256 CLOSED / 0 QUALIFIED / 331 OPEN of 587; S 97/97 with 7/7 roots, Q 142/149
with 2/2 roots (4 occurrences under ae), D 21/343 with its common function
root OPEN in both TX1 and TX2. The authoritative final result may only lower
these counts when coherence fails. This checkpoint is not release evidence.

Findings being isolated: S's original cache order passes its standalone import
(L007), but the SAME packet with RPx_Deployed fails on duplicate ownership of
PreparedFromQmSourceBridge.PrepQM (L008). Q alone (L009) and D helpers with the
headline (L010) pass. Earlier L003–006 also exposed own cache-order mistakes;
those diagnostics are not used to blame predecessor packets. L008 uses the
faithful privately copied NFJ view. Raw graph/module inventory will identify
exact packet dependencies before final qualification.

Own client repairs: create native/output dirs before upload; restore SInt2's
lookup precedence; copy missing pilot NCO objects; memoize profiler code objects
rather than inspecting every recursive certificate call. Interrupted Python
client probes earn no validation credit. No timed-out/memory-killed prover,
cap increase, shared-infrastructure change, Kani or extraction run occurred.
