# D286 op223 timing gate

Preparation in progress. Control c57a344726; integrated candidate 8873306db1.
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
