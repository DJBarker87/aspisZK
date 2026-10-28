# SHA453 proof preflight

Read `/Users/dominic/ZK/AGENTS.md` in full and local-lean.txt rules 1–15.
New JHx modules only; no native_decide, axioms, admitted facts, or old proof edits.

The SHA family contains 453 equations, 996 compression blocks. Each SHA round
uses exactly one concrete 16-word schedule and eight-word register state. The
certificate binds every single-round transition before folding constants; it
never reduces an entire compression or whole hash by reflexivity. Reflexivity
is confined to a single round, byte cast, bounded padding tail, or register
association. Symbolic hash_chunks and list fold rewrites chain those cuts.

The independent Python checker implements SHA256 using integer bit operations,
checks every block against its retained start/result, verifies interblock links,
padding, source head/chunk expressions, finite-family indices and expected
aliases, and cross-checks each complete message with hashlib. Its first complete
arithmetic check passed before compile001. Adding structural head/chunk checks
then exposed a parser omission for List (List Nat); that parser case was fixed
and the stronger --check passed while compile001 was pending.

Existing lead launchers and reservation barrier are reused unchanged. The task
orchestrator only supplies source/config and saves receipts. Normal admission
requires exit0 and allowed:true; MemoryHigh6G/Max8G/SwapMax0/TasksMax64,
Lean -j1 -M7000 -DElab.async=false; one scope at a time. Budget60 normal,
2 owner-authorized assembly-only16G attempts. No package rebuild.

Own cache seeded by copying only .olean companions from the two read-only
predecessors, with tx2fix copied after fixture using no-clobber. Existing cohort
paths remain pinned by the runner's direct-object fingerprints. Neither source
cache was modified. Own cache retained.

The three agg16 runner hashes were read and matched JHw_RUNNER_HASHES.json:
reservation_agg16.py d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f
S2W_lean_host_agg16.py 9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd
S2W_run_host_agg16.py 8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6

Next consumers: per-tree finite family assemblies, then JHx_Instance proving
JHe_SHARealization, then JHx_Joint supplying it to JHw_Joint.source.
