# One-scope scheduling exception

While polling attempt 37740 (ProverRw21ProofOutput), the local wait returned
an active session rather than a terminal status. Attempt 37741 was then
started prematurely. Both returned exit 0 under the unchanged launcher
caps; 37740 used slot 1, 37741 slot 2. This dispatch failed the requirement
to keep at most one job-owned capped scope active at a time. It is retained
explicitly, not represented as a compliant sequential pair.

37740: 28.52 seconds, 6,640,448 KiB RSS, zero swaps.
37741: 2.73 seconds, 4,127,184 KiB RSS, zero swaps.
The per-attempt inputs, admission receipts, wrapper/time/output logs and
source snapshots are retained. No cap, launcher or reservation policy was
changed. Future launches must wait for a terminal `exit_code` result for
the prior tool session, not merely a successful wait call.

At 02:06:58.743616 UTC, ID 37764 performed an admission scan 157.968422 seconds
following refusal 37763, 22.031578 seconds short of the required three minutes.
The scan refused and no capped scope started. This was a scheduling error; the
next retry is gated on 02:09:58.744 UTC or later. Neither refusal is charged.
