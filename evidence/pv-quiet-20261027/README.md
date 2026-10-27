# D286 op223 timing gate

Both optimized binaries built successfully outside the quiet window. Preflight
proof-byte comparison passed for both fixtures (coin 99). Control c57a344726; integrated candidate 8873306db1.
No implementation changes. Five paired fresh processes per side (D216 count),
coins 100–104, alternating order, both fixtures in each process. Features:
optimized-terminal,r1p-check,ct-host-prover. Fixed CPU affinity will use all
host online CPUs, preserving the harness's 16-worker execution environment.
Candidate medians must be <15 seconds and candidate/control <=1.10 per fixture.
Pre-window proof-byte comparison is mandatory. Every measured pair compares
public.bin and proof.bin exactly. No Lean, Kani, dudect or V374.

D286 authorizes this job to create a one-hour quiet marker and remove it on
measurement exit; that overrides the older plan/common lifecycle prohibition.
No marker extension. Retain partial receipts on early stop. No premise is
removed by preparation or fixture timing; target not yet established.

Build receipts: control build-control-2 (exit 0, 27.840 s, peak RSS 515760 KiB,
swap 0); candidate build-candidate-2 (exit 0, 37.869 s, peak RSS 566044 KiB,
swap 0). Binary hashes and sizes are in pin-control.json and pin-candidate.json.
Initial admission refusals and the missing-export-input failure are retained.

Preflight public/proof bytes match exactly for both fixtures; both binaries
verified successfully through tx1/tx2. This preparation was outside the quiet
window and its timing is not qualified gate evidence. See preflight/comparison.json
and preflight-scope/receipt/receipt.json. The <=15-minute quiet wait follows.
