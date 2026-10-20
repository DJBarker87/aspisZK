# R16 focused packet

Base: 8ced75478ded9fbac42ab4551e011e537cebd0ef.
See ../../design/HCHECKS-20261020.md for the 26-field audit, partial theorem,
source route, missing deployed decoder/decision refinement, and counterexample.

Accepted final inputs/results are in accepted-summary.json; manifest.json
retains every attempt, including failures. No binary objects are committed.
Commands and direct resolved import object hashes are recorded per attempt.
Later attempts also retain source snapshots. Early attempts retain their exact
source hash and raw diagnostics; only final module sources are release candidates.
reader-v8 has exit=null because a lock-cleanup exception lost the exact Lean
process exit, as documented in its receipt. It is failed evidence only.

Run `python3 docs/research/100bit-spend-path-20261013/evidence/hchecks-20261020/verify.py`
from the worktree to verify receipts without compiling. The compile helper takes
`<Module> <unused-attempt-name>` and implements the prescribed local memory gate,
shared mkdir lock and private object directory. Do not replay unchanged accepted
inputs. Import cache provenance remains the focused-build limitation in LOG D63;
this packet is not a fresh coherent release build.
