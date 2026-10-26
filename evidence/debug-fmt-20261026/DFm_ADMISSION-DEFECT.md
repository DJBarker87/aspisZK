# Host admission defect — report only, no infrastructure repair

Observed after this job's final DFm_040 compile. Stop further compilation:
40/40 budget exhausted regardless; do not reuse the historical orchestration.

Host file:
`/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py`

Its quiet-window branch writes and prints an object with `allowed: false`,
`reason: quiet window until ...`, then executes `raise SystemExit(0)`.
Its aggregate-reservation refusal branch instead exits78. The existing caller
pattern tests process exit status. Thus quiet-window refusal is misclassified
as success. This job inherited that pattern from RPz2's recorded orchestration;
that explains the error, not a valid reservation.

DFm_007-barrier-0.log and DFm_007-reservation.json show the exact refusal:
quiet window until1793038500; bounded_reserved_bytes/requested_bytes null.
DFm_007.json records reservation_retries0. The existing systemd-run shim waited
outside any scope while the marker existed and proceeded when it was withdrawn.
DFm_007-launcher.log then records run-r8ee6c3a91b064178b543da4b45deb02d.scope.
Its compiler exit134 is a separate fixed -M7000 expression-rendering memory
failure, not an admission failure. Receipt:20.6304952299688s,7386260KiB,swap0.
No valid aggregate admission at that scope's launch is claimed.

All other 39 reservation receipts have allowed=true. All 37 passing compiler
attempts consequently have positive reservation receipts and verified scope
limits. The failed inspection supplied no accepted theorem result. No quiet
marker, shim, launcher, reservation scanner, shared object or foreign job was
edited/killed; no explicit quiet bypass flag was used.

Recommendation to the lead: make the quiet refusal return78, and/or make the
caller require parsed JSON allowed=true. Re-run admission after any shim delay
before opening a scope; a stale reservation should not authorize later work.
This recommendation is NOT implemented by this proof worker, per local-lean
rule5 (no infrastructure repair). No new compile is authorized here.
