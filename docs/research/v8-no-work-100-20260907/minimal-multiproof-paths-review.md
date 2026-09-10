# Minimal multiproof paths: focused proof result

Status: [MinimalMultiproofPaths.lean](experiments/MinimalMultiproofPaths.lean)
is **GREEN** on the focused Tailscale NUC v2 run. All seven audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The
coordinator's focused NUC v1 failed at the single-entry proof branch: `rcases ... with rfl`
removed the named `head`, making `head.position` and `head.digest` unavailable.
V2 instead names the equality and explicitly substitutes `child`. No theorem,
resource limit or execution model changed. V1 is retained; the coordinator
reported exit 1, 3.07 seconds, 6,655,676 KiB peak RSS and zero swaps. Later
`sorryAx` reports in that failed run are cascading errors, not checked proofs.
V2 exited 0 in 3.58 seconds with 6,684,904 KiB peak RSS and zero swaps. No
Rust run, cache mutation, or broad replay accompanied it. Research source parent:
`2a49280b70f17a4539927d7c6fd3121c417f2d7e`.

The v2 source SHA-256 is
`7d94c6ba5c954f1d88d30362e2fac4f8493770ca9cab2b034976a6ff593a618d`;
the green output is
`7d3d0021ec2e4d088ff6d8c798dabbc212a4c40bef53eb0c6760e75fcc360594`;
the manifest is
`36d356aa12aa30cbfc5db4aba6f2929d1e5d574c938b37761d0f248829c151db`;
and the log is
`9c1e9733ec3d987d49d68877c276130bb2d5b10e22898623992dd5d0d23e5975`.
The runner used Lean 4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`,
`-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and
CPUQuota 200%; it verified the registered overlay before and after the leaf.

## Narrow result

`accepted_q22_paths` is the proposed endpoint for a typed execution of the
literal binary minimal-multiproof merge. It constructs, for each original
query ordinal and both trees:

- an 18-element sibling list;
- the existing V7 `foldPathAux` equality to the corresponding supplied root;
- membership of the leaf call and every ordered parent call in the same
  generated execution log.

It does not assume supplied paths, path-call coverage, a collision exclusion,
an early-word projection, field canonicality, or a polynomial candidate.
It does not yet infer its typed execution premise from Rust `bool = true`.

The only direct import is the already registered
`AspisFormal.Pool.V7MerkleOpeningBinding`. This reuses the literal V7 byte
grammar, leaf widths/tags, `orderedNodeInput`, `foldPathAux_cons`,
`foldPathInputTrace`, and `TraceIncludedInLog` without a new hash abstraction
or a q16 opening-array restriction. Its source SHA256 is
`b7a368b8fddd62c46093258b10b50cdf98bede74a16e8955d166924d221b3fcb`.
Both source and output entries occur in the retained
`selected-early-c1-outputs-nuc-v2-manifest.json`; this read-only observation is
not a fresh remote preflight or complete closure audit.

## Exact control-flow model

`Pass` is an inductive successful-execution relation for one level. Its rules
consume exactly the source inputs and generate the source node calls:

| Source branch | Consumed entries/frontier | Constructed parent/log |
|---|---|---|
| Adjacent even/odd pair | Entries `(2k,left),(2k+1,right)`; no frontier | Position `k`; ordered left/right hash separately for C1 then C2 |
| Unpaired head | One entry and one aligned C1/C2 frontier pair | Position divided by two; child/sibling order from its low bit; C1 then C2 calls |
| End of level | No entry | Preserve unused frontier; no additional calls |

The unpaired rule explicitly requires that the adjacent-pair condition is
false. `canPair_iff` relates the source's modulo/adjacency guard to the
`2k,2k+1` form. `Levels` sequences precisely the requested number of passes.
`Accepted` retains strict initial key ordering, final singleton position zero,
both root digests, and exhausted frontier at depth 18. Nonemptiness and the
initial range follow from 22 requested entries and `Position = Fin (2^18)`.

`pass_parent` constructs a one-level sibling and log-membership witness for
every consumed entry. In the paired right-child case, the sibling order is
reversed while the actual hash input is proved identical to the left-child
input. `levels_paths` inductively prepends these siblings and concatenates
the actual per-level logs. Shared internal nodes are logged once per actual
merge, not once per reconstructed path. Trace membership does not assert
that the various requested paths execute disjoint hash calls.

## Original query/record correspondence

The typed record contains exactly `C1Value`, `C2Value`, and `Salt32`.
`recordEntry` hashes the record at the same original ordinal as its query.
`sortedOrdinals` sorts the natural packed descriptors
`query_position * 4294967296 + original_ordinal`, then maps those ordinals to
immutable records. `sorted_ordinals_perm` and `sorted_entries_perm` derive
the permutation from `List.mergeSort_perm`; it is not a supplied permutation
hypothesis. `leaf_call_covered` derives the original record's membership in
the sorted leaf-call log. The q22 endpoint is indexed by the original ordinal,
not the sorted rank. Duplicate query keys still fail `Accepted`'s strict-key
guard even though their descriptor ordinals are distinct.

The existing [AuthOrder](experiments/AuthOrder.lean) proves the uint64 range,
packed ordinal/key decoding and sorted-permutation authentication congruence.
Those source facts are reusable; the current path proof needs only the same
descriptor definition, so it avoids an unregistered `AuthOrder` cache import.

## Still missing before literal Rust acceptance

1. Translate or refine the Rust `Vec` level loop to `Pass`/`Levels`, including
   successful initial checks and the exact terminal checks. The model has no
   path premises, but this successful-execution connection is not yet proved.
2. Derive aligned typed frontier pairs from the two raw byte slices: lengths
   divisible by 26 and equal, with one shared cursor and no trailing bytes.
3. Connect fixed records and their slices to the source's 621-byte records:
   C1 `[0,403)`, C2 `[403,589)`, salt `[589,621)`. Connect actual descriptor
   shift/or, safe indexing and `sort_unstable` to the typed permutation.
4. Identify the generated log with the selected execution's actual hash calls
   and shared oracle log. A fixed function of concatenated input bytes is
   essential: the existing `auth_order.rs` stateful-callback negative test
   shows that arbitrary order-dependent `HashFn` values invalidate the sorting
   equivalence. Selected SHA/syscall semantics, not the Rust function type
   alone, justify this hypothesis.
5. Convert the resulting length-18 lists to V7 `SiblingPath` functions, carry
   strict packed-field parser success, then apply the existing
   `AuthenticatedEarlyC1Targets.accepted_opening_prefix_or_shared_failure`
   at the actual pre-lambda/chi cutoff. No support/recovery conclusion follows
   merely from these 22 authenticated openings.

The next allowed verification, after coordinator review and grant, is only
this changed leaf on the existing capped NUC workspace. The proof uses
symbolic list/level induction, two-element side case analysis, and small
linear natural-number arithmetic. It does not enumerate the `2^18` domain,
recompute a complete Merkle tree, or change the current depth/heartbeat caps.
