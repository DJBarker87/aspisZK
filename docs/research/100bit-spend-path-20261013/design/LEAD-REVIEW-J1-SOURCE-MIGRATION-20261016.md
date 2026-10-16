# Lead review: source-migration checkpoint 85ef4199b (2026-10-16)

Fast-forward from ae2410caf. The live session's commits are retained unchanged.
This checkpoint changes production source. The
29 changed non-research files are the Digest32 migration (A), the guard split
(B), and one extracted helper `semantic_public` (C).

## Source read by the lead

- `aspis-core/src/digest.rs`: the `Digest32` trait plus `LegacyHashFn`, a
  one-line delegation to the old function pointer. R0 `merkle.rs` and
  `state_only_private_merkle.rs` gain `_with_digest` generics; the old
  functions now route through `LegacyHashFn` and are byte-for-byte the same
  computation.
- `programs/r1-cost-probe/src/lib.rs`: the single backend `SolanaDigest`
  calls `hashv(parts).to_bytes()`, the same syscall as the replaced closure.
  stage1 (`tx1`) and stage2 (`tx2` and the pool adapter) use it. The R16
  wording is unchanged.
- `r1_pool_adapter.rs` and `v7_pair_forest_dispatch.rs`:
  `readonly_meta_ok` plus a one-line projection wrapper, as decided in
  ca137f5db.
- `aspis-statement` `semantic_public`: the inline two-arm match from stage1
  moved into a method. Same arms, same borrows. It falls outside Decisions 1
  and 2 but is behaviour-preserving, and it is needed for C's extraction.
  Accepted.

## Gate status (ca137f5db, Decision 1)

| Gate | Status |
|---|---|
| 1 single syscall backend | PASS (lead read the source) |
| 2 1,233-case differential | PASS, byte-identical (16,431,699 bytes) |
| 3 hash-counter regression | PASS: 583 ordered calls; counts 349/234; checkpoint identical |
| 4 CU replay | OPEN: lead, J1.R13 |
| 5 single SBF rebuild/pin | OPEN: lead, J1.R13 |
| 6 re-extraction/re-pin inventory | PARTIAL: 28 parser + 17 decoder declarations re-pinned; whole-cone inventory open |

The branch tip's production source is therefore the Digest32 candidate. It
is not certified release source. Evidence pinned to 0626294e3 remains valid
for that revision. Before release, every extracted declaration in a changed
file (verifier.rs, transcript.rs, r1_wire.rs, r1_semantic.rs and the others
listed in the checkpoint) must be re-pinned to the release revision or shown
unchanged. That re-pin inventory is a release gate. It does not block
ongoing proof work.

## Decisions taken here

1. **Second guard copy.** The admitted R1 artifact is `r1-cost-probe` with the
   `pool_route` guard. The `aspis-verifier` V7 copy is not in the admitted
   artifact set. For it, the helper proof plus the five native cases are
   sufficient, and no runtime fixture is required. If V7 is ever admitted,
   runtime coverage of that copy becomes a gate.
2. **`require_readonly_buffer`** reads the same three account flags and is
   called four times on the admitted route. It gets the same pure-helper
   split, and the R16ReadonlyMetadataProjection premise is extended to cover
   it. The premise is not split into two.
3. **The runtime metadata harness** runs against the J1.R13 candidate artifact
   (one artifact), not a separate build.

## CU note

The reused baseline is transfer1023: stage1 1,343,603 CU and stage2
1,229,578 CU, with setup excluded. Stage1 is above the 1.3M per-transaction
target. G_R1.1 stays open independently of this migration.

## Unchanged open items

C: old `.hs` from actual helper success, outer `.hd` from caller
reachability, supplied-input equality, custody. A: lift the row step through
begin/verify and the opening phase; all 33 rows and the state carry; actual
hbytes, hread, htyped/ha and C2 provenance. Then J5/J2, J1.c/d,
SourceSimulation.preservesPrefix with actual QV, and efficient extraction.
