# One delegated import-only exception: JHx_Joint

NDP_R006 failed before NDP_POST_IMPORT and before #print axioms with
`lean::memory_exception` (interpreter), exit 134, wall 49.613719334010966 s,
peak RSS 7169948 KiB, swaps 0, under MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 and Lean -M7000. No audit traversal or arithmetic
normalization had begun. The complete normal-cap receipt is retained.

The task instruction explicitly delegates ONE 16 GiB lead-owned agg16 runner
attempt per root when that root's import exceeds -M7000. This is the same
import-only failure previously recorded as NDJ_R003. NDP_R007 consumes that
exception for JHx_Joint, after checking the three unchanged lead-runner SHA256
pins against NDJ_AGG16_RUNNER_HASHES.json. It uses the lead runner's 14G/16G,
swap 0, TasksMax 64 and Lean -M15000 settings. No second raised-cap attempt is
authorized for this root. The deployed root required no exception.

This changes neither the proof, frozen implementation, axiom acceptance policy
nor release scope; it permits import assembly for the requested audit only.
