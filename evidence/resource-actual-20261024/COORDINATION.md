# Coordination and reused source assessment

Immutable HEAD 74d67bcc99a749152ee0a400876b0e2169531bfd manager launchers
`tools/port18coherence-20261024/Port18COHERENCE_compile.py` and
`tools/port17release-20261024/Port17RELEASE_compile.py` use
`flock /tmp/aspis-r0-lean.lock sh -c '<admission> && systemd-run ...'`.
This is an advisory exclusive flock held through admission and child exit;
it does not establish that noncooperating workers serialize or replace
fresh complete hierarchy admission. The rehearsal uses the SAME lock with
LOCK_EX|LOCK_NB once, through prospective collection and any scope exit.
No second/nested lock or wait is introduced. Busy means terminal blocker.
No manager launcher or live cache is read or changed on the host. Immutable
repository manager sources supply these semantics. The metadata inspection
checks lock presence, own stage absence and parent ownership only.

Four inherited operational files (ResourceStat_go.py, ResourceStat_candidate.py,
baseline/reservation.py, baseline/reservation_base.py) execute byte-identically
in private read-only stage copies. No operational fixes to these are proposed.
Existing 57 historical + 64 candidate tests and 14,587-event independent replay
are reused as reviewed historical evidence for those bytes, not new host identity
or a fresh headroom result. New tests exercise only own runner and 3/4 binding.
Current packet's explicit limited adoption authorizes this one estimate rehearsal;
the source's `adopted=False`/unadopted labels are retained. It is not general gate
adoption or permission for a consumer. Historical unlimited-scope denial and raw
4096 counter discrepancy remain failures, not tolerance cases.
