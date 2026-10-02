# R366 semantic normalization evidence

This formal milestone records the saved successful focused Lean compile for `AspisV8R19/R366SemanticNormalization.lean`, the byte-identical promoted source, the earlier missing-cache attempt, and the bounded replay of its 11 missing local dependency objects. The Lean target compiled successfully; the source-level obligations listed below remain open.

The production source is copied byte-for-byte from the source snapshot captured for the successful Lean invocation. `copygraph.json` records the draft, successful compiler input, evidence copies, and promoted target hashes. `verify_evidence.py` checks those identities, the saved compile receipts, the full target axiom report, the 11-object/57-report replay, and the complete checksum set. Run it with `python3 verify_evidence.py` from this directory; it does not invoke Lean.

## Result and theorem boundary

Lean 4.32.0 compiled the target with exit status 0 in 1.48 seconds, GNU-time peak RSS 2,064,980 KiB, and zero swap. The command used `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. All six public theorems have complete saved `#print axioms` output: `[propext, Classical.choice, Quot.sound]`.

The theorems formalize a universal normalization for polynomial walks whose per-round polynomial has degree at most 27 and satisfies the boundary-sum equation at the incoming carry. The normal form is valid at every field challenge, including 0 and 1. For ten rounds, if two such walks have equal terminal carries, the full 271-coordinate covector difference is zero; the initial carry difference is retained in that covector.

This does not prove that the actual selected source terminal has the required degree, interpolation equality, boundary equations, or equal endpoint values. The universal hypotheses remain caller obligations. It also does not close C1/H1 retained-view coverage, G compatible-image coverage, p0/p2/channel coefficients, legal-mask restrictions, posterior bijections, adaptive/shared-oracle or seed laws, commitments, retries/failures/publication, an explicit-loss simulator, or soundness.

## Attempts and dependency cache

Attempt 01 exited 1 after 0.10 seconds because the cached `AspisV8R17.StructuredCube.olean` was absent. It did not reach theorem checking. The initial read-only inventory identified a 23-module local transitive graph with 12 cached objects and 11 missing objects. The authorized replay compiled exactly those 11 missing dependencies serially; all 11 jobs exited 0 with zero swap and recorded all 57 named theorem axiom reports. Existing 12 local objects and external Mathlib objects were reused, not rebuilt. At the end of that replay, R366 itself remained uncompiled.

Attempt 02 then compiled R366 with exit status 0; complete source, receipt, and log are preserved separately from Attempt 01. The launch runner completed Lean successfully, but a later outer shell step returned status 1 when it attempted to `cat` a nonexistent `summary.json`. That shell follow-up was not the Lean process: the saved R366 receipt, Lean log, and systemd scope each record exit status 0. No shell transcript for the missing-file `cat` was available to archive, so this distinction is recorded from the lead’s run report rather than presented as an additional Lean log.

## Files

- `sources/` and `attempts/` preserve the draft, the exact successful compiler input, both attempt source snapshots, logs, and receipts.
- `dependency-cache-replay/` contains every missing-dependency source copy, receipt, log, and the 57-report replay summary.
- `lean-cache-inventory/` retains the initial read-only 23-module graph and the 12 existing object hashes.
- `proof-route/LEAD_PROOF_ROUTE.md` retains the lead’s intended use and explicit remaining source obligations.
- `runner/run_focus.py` is the exact saved focused runner used by the receipts.

No `.olean`, `.ilean`, or other Lean cache objects are included here. `SHA256SUMS` covers every regular file in this evidence directory except itself.
