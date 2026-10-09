# Whole-script alignment with the V7 oracle machine

Status: **deterministic interpreter refinement proved; deployed random-oracle
coupling still open**.

The new leaves `FSV8V7FreshAlignment.lean` and
`FSV8V7WholeScriptAlignment.lean` complete the previously partial recursive
state bridge.

`fresh_successor_aligned` reconstructs every field of `StateAligned` after a
cache miss: table/cache contents, ordered history, total and fresh counters,
the exact consumed tape prefix, absence of programmed entries, V7 fresh-history
coherence and the finite-tape bound.  Its V7 query result is derived from the
same controller tape cell as the current interpreter.

`run_compileScript_aligned` is a structural induction over an arbitrary bounded
`Script Bytes Block A n`.  Given explicit room for its static call bound in the
V7 total/fresh limits and the finite tape, it proves:

- a returned current result is the same V7 `MachineHalt.returned` result;
- a current `Script.abort` is the explicit V7 `controllerRefused` halt;
- every cache-hit and fresh-query continuation consumes the same answer; and
- the complete final V7/current states still satisfy `StateAligned`.

The theorem does not take output equality or successor alignment as a premise.
It does assume the stated initial alignment and excludes programmed entries.
It also intentionally maps the reasonless research `Script.abort` to one V7
refusal reason; it does not prove literal Rust error-reason fidelity.

## Focused NUC evidence

Both files were compiled in the pinned Lean 4.32.0 environment, one target at a
time, in a user systemd scope with `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0` and a 300-second runtime cap.

| Target | Source SHA-256 | Exit | Wall | Peak RSS | Swap | Printed axioms |
|---|---|---:|---:|---:|---:|---|
| `FSV8V7FreshAlignment.lean` | `bf8e21cbc94f201c1d4abaccd9391210623d32a2af2abbb9d1aedf58b2172d24` | 0 | 2.87 s | 6,532,704 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8V7WholeScriptAlignment.lean` | `8ccfc024be19312c0a845b67e30c9a96864178d5399666fd3d5cc823e65047bb` | 0 | 2.98 s | 6,537,768 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The whole-script artifact SHA-256 was
`687eeac2a6eb59f6f3d3367a278762b64b92eb96838392ae807a74c576dfc97f`.
A separate focused fresh-leaf invocation produced artifact SHA-256
`b1154baa23504afa14abf8dabb43c5ea76619bad4e99661a31eb72cdc5114b2d`.
Artifact-byte reproducibility is not inferred from these source/kernel checks.

An initial fresh-leaf invocation with an incomplete `LEAN_PATH` failed before
elaboration on the missing `FSV8V7CachedAlignment` import (exit 1, about 0.10 s,
512 KiB).  A later correctly configured attempt exposed ordinary proof goals
and failed (exit 1, 2.62 s, 6,500,628 KiB); the proof was then repaired before
the successful run above.  Neither failed run is counted as proof evidence.

## What remains

This closes the deterministic current-`Script`/V7-machine execution mismatch
for unprogrammed aligned states.  It does **not** yet show that the deployed
adversary plus verifier produces this `Script`, that its prequeries establish
the initial invariant, or that the real random-oracle law is the uniform tape
law.  Programmed extractor forks require a separate state relation.  Literal
Rust effect order and a global acceptance/extraction probability theorem also
remain open.

No protocol bytes or acceptance checks changed.  The proof-body cap remains
40,282 bytes and grinding contributes zero security bits.
