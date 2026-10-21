# S8 accepted-run join continuation

Branch `codex/cx-s8-join-20261021`, base `6c520f134`.
No shipped source edits. New Lean modules only. No pushes.

## Stage 1 — exact finish target

`S8JoinFinishExact.reference_exact` identifies the complete emitted owned
finish with the canonical raw prefix list; `mutable_exact` identifies the
complete mutable traversal with its exact transported list. The only
precondition is destination length ≤ raw length. Terms, phase, raw bounds,
callee success and congruence are not required for these execution identities.
`prefix_length` supplies length preservation of the deferred writes.

Focused receipts and failed intermediate attempts are retained in
`proofs/` and `manifest.json`. Failed elaborations may print `sorryAx`;
those are explicitly unsuccessful attempts, not accepted proofs.

## Upstream handoff

The current S7 branch was read with `git show`, without editing or importing
its working tree. At base `6c520f134`, `S7Kani3CallerTrace.reached_invariant`
consumes `PushTrace`; `p6_route_certificate` does not supply actual frozen
query membership or source state provenance. The requested next interface is
an actual reached raw vector, destination, and raw-coordinate congruence with
`∑ j : Fin 22, rho^j * basis q j l` (including saved-ten/resumed-twelve).

`dV_frozen` itself uses `D0TypedChecks.verify` with a `ClosedSum` field
predicate. It has no raw U64 Vec, mutable iterator or physical checkpoint
state. Such source-state provenance cannot be projected out of that model
without a concrete representation/reached-source construction. A new model
representation is not silently labelled the reached Rust state.

The compact strict scan is being joined to the exact canonical predicate
of `OraclePortCompactDraft`. It scans full 16-byte chunks and ignores a
trailing suffix, so a multiple-of-16 length condition is essential when
comparing with the parser's four-byte canonical scan.

## Stage 2 — exact byte/word grouping

`S8JoinCompactChunks.chunk_iff` equates the extracted strict codec on a full
16-byte chunk with the frozen parser's canonicality of exactly those bytes.
`canonical_chunks` proves the whole list/grouping equivalence for lengths
that are multiples of 16. No parser or codec operations are abstract callbacks.
All six theorem audits use standard axioms; focused attempt chunks-06 passes.
The retained coalesced R1SemanticHit/R0P caches resolve a duplicate-declaration
import failure in chunks-02; no shared cache or old module was modified.

## Stage 3 — total compact scan result

`S8JoinCompactTotal.check_values_total` proves full Result equality for every
extracted byte slice, including inner NonCanonical rejection and any ignored
partial final chunk. The target is canonicality of precisely the consumed
prefix, not an all-storage successful-input restriction. `aligned_scan_total`
uses the same frozen canonical predicate on the entire input when its length
is a multiple of 16. All five audits use standard axioms (scan-01).

`preflight.py` validates inherited S8 frozen file/reference hashes and the
new-module lexical scan. The historical checkers' broad-base failures are
recorded in `legacy-validation.json`; their code/old receipts are unchanged.
