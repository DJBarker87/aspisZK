# Scan freshness — 2026-10-21

Branch `codex/cx-priv-history3-20261021`, base `55c62085d`.

## Stage 1: actual input trace

`QueryScanFreshInputs.real_scan_addresses` proves the exact real-side inputs,
not only an address grammar analogy. For block zero the state is the answer
of `absQ`. For block n+1 it is the answer of `qa n`. Squeeze reads append
byte 1; advance reads append byte 2. No separate prover secret, salt or block
counter occurs in either input. Both members of a pair share their state;
the second member has a different suffix, not a new independent state.

`FreshFailure` defines the scan-specific event operationally, at the partial
answer vector immediately before each query. It includes the initial public
digest and every earlier honest scheduled read, including previous attempts.
It excludes the post-proof observer. `off_fresh_failure` gives precisely the
freshness consequence, without asserting a probability law.

Focused env J 9832: exit 0; wall 2.14 s; peak RSS 4,051,128 KiB; swaps 0.
Four theorem audits use only subsets of propext, Classical.choice, Quot.sound.
9830/9831 retain local elaboration failures, followed by changed source.
Full source revision, SHA256, dependency fingerprint, errors, axioms and raw
launcher/time output are in `history-fresh-attempts-9800-9999.jsonl`.

Further stages and endpoint status will be recorded below. Existing modules
are unchanged. Build runner is the assigned env J run-joint.sh, -M7000,
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0; reservation 24 GiB + this 7 GiB.
