# Rust-shaped minimal-multiproof execution: checked typed refinement

Status: `RustShapedMinimalMultiproof.lean` is kernel-checked on the capped
Tailscale NUC, attempt v3. All nine audits use only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound` (each audit uses a subset).
No successful audit contains `sorryAx`. The source and all three attempt
receipts are frozen. This is a total functional typed model, not an Aeneas
translation or a theorem about execution of the compiled Rust binary.

## Checked endpoint and source correspondence

`AspisV8.RustShapedMinimalMultiproof.verify_selected_accepted` proves

```text
verify view roots 18 (sortedEntries view query records) left right = some trace
  -> MinimalMultiproofPaths.Accepted view roots query records
       (frontierPairs left right) trace
```

Here `query` and `records` have the same original `Fin 22` ordinal throughout.
`verify` does not take `Pass`, `Levels`, `Accepted`, an authentication path,
or an equality to any of those objects as an input. Its successful result
constructs the existing execution predicate. The existing
`MinimalMultiproofPaths.accepted_q22_paths` then constructs every requested
18-sibling path and its exact leaf/node hash-call coverage. The separately
checked `SelectedMultiproofPrefixProjection` can consume this `Accepted`
result under its explicit C1/C2 prefix-binder and log-inclusion premises;
this new leaf does not discharge those premises or remove its collision and
late-target alternatives.

The inspected Rust function is `verify_two_minimal_subtrees_v7_bytes`, in
`crates/aspis-core/src/v7_merkle208.rs:46`, source SHA256
`071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf`.
The following map records the source review, not an additional translation theorem.

| Rust operation | Total typed model / checked consequence |
| --- | --- |
| Reject empty entries, depth >=32, non-26-byte-aligned or unequal frontier lengths | `Guards`; both byte arrays are checked before decoding |
| Adjacent strict ordering and final position <2^depth | `adjacentCheck`, `rangeCheck`; `adjacent_sound` derives pairwise ordering |
| Shared 26-byte frontier cursor for both trees | `frontierPairs`; `frontier_length` and `frontier_in_bounds` prove exact count and in-bounds indexing |
| Even entry with adjacent odd sibling consumes two entries, no frontier | `runPass` pair branch; `pass_sound` constructs `Pass.pair` |
| Otherwise consume one entry and one frontier pair, reject exhaustion | `runPass` single branch; parity-sensitive `parent` and `nodeCalls` reuse the existing serialized-node definitions |
| Append parent at position >>1, C1 hash then C2 hash | `parent` uses Nat division by two; the trace is `nodeCalls ++ laterTrace` |
| Repeat the pass `depth` times | `runLevels`; `levels_sound` constructs `Levels` |
| Exhaust all frontier bytes; singleton at position zero; both roots match | `finish`; `finish_sound` derives all three equalities |

The recursion fuel is the input entry count. `pass_complete` proves that it
is sufficient for every successful `Pass`; fuel does not add a rejection to
the successful small-step semantics. V2 replaced Option `do` syntax by
explicit `none`/`some` matches without changing the algorithm. The model uses
a pure `RawHashInput -> Digest208` function and natural-number/list state.
It records C1 then C2 calls in source loop order but does not claim an
execution trace for an arbitrary stateful Rust `HashFn`.

## Focused checks and preserved failures

All tags have prefix `rust-shaped-minimal-multiproof-nuc-`. Every attempt has
an immutable `-source.txt`, `-manifest.json`, and `.log` in `experiments/`.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 2.98 | 6656804 | 0 | Option/do simplification, explicit contradiction, and symbolic list/equation proof errors; rejected audits retained |
| v2 | 1 | 3.06 | 6656348 | 0 | Only `pass_sound` outer pattern-match reduction remained; dependent rejected audits retained |
| v3 | 0 | 3.26 | 6691944 | 0 | Nine standard-only audits; one harmless unused `Nat.add_one` simp-argument warning retained |

The v3 fix was a single symbolic simplification step after `runPass.eq_def`;
the simp engine reduced the outer match without needing the named lemma.
The successful source was not subsequently cleaned up or rerun. No limits
were raised: source maxRecDepth=200 and maxHeartbeats=250000 throughout.

An initial direct invocation of the non-executable runner script returned
shell status 126 before any Lean invocation. Calling its identical bytes
through `bash` started v1. This shell-only failure is not counted as a Lean
attempt and no proof log was inferred from it.

All runs used the established task
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`, actual network endpoint
`dombarker@100.108.41.90`, with SSH BatchMode, ConnectTimeout=10,
StrictHostKeyChecking=yes, and `HostKeyAlias=nuc.local` for key reuse only.
Each immediate preflight found no Lean/lake process and approximately 46 GiB
available. Jobs were serialized with the coordinator.

Each scope enforced MemoryHigh=8589934592, MemoryMax=10737418240,
MemorySwapMax=0, CPUQuota=200%; Lean used `-j1 -M9500`. V1/v2 had manual
read-only postflight `OVERLAY_PROVENANCE_PASS=1105`; v3's automatic preflight
and postflight both reported 1105 with `PROVENANCE_UNCHANGED=true`.
This verifies registered entries, not a replay or independent completeness
audit of the entire native package cache. No dependency was installed or
replaced for this leaf.

Source-working parent is `531b50ed6cd06d5902417edf614daee137c19acb`.
The inherited runner creation parent remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, and the borrowed source pin remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Lean 4.32.0 commit is `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Runner SHA256 is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The sole direct import is `MinimalMultiproofPaths`: its registered source
SHA256 is `7d94c6ba5c954f1d88d30362e2fac4f8493770ca9cab2b034976a6ff593a618d`
and output SHA256 is
`7d3d0021ec2e4d088ff6d8c798dabbc212a4c40bef53eb0c6760e75fcc360594`.
Both local and remote source pins, and the remote compiled pin, were checked
before the first run; every immutable attempt manifest retains both entries.

## Exact retained SHA256

| Artifact | SHA256 |
| --- | --- |
| Current source and v3 source snapshot | `add4dd9529dabfdcb80151205898f767f9790d7771325da35f1b9bc343611c8b` |
| Green `.olean` (local ignored artifact) | `e83ada30954bc03e3dc27b053bdfa65150fb37a5a1ac53879e91a76ad7519993` |
| v1 source snapshot | `c16e3f7742d4246da897b95aa4f7e0ab4507fd8f56f9aa3bf172303aeecbc3a4` |
| v1 log | `e6fb2ba938b83ee20e60553e18d6b5d687690e65ed0c9fd65c3e96176ee3b096` |
| v1 manifest | `7502048e3f93976484daced07b46ac057885dcb27da722d6f37ed86b17f868bb` |
| v2 source snapshot | `145d98d575eb2805df589892a17092fc66b44b29ed0809d66d777995f4b0f98b` |
| v2 log | `02f297b7f5515dcd5e577f6f4ed7b34d7e5dd0c48c15a26258f999aedf1ea5c3` |
| v2 manifest | `f56e9b31dce76430d4886d9a476e1fdfd2affb5f47a8eab780e55350e6418dbd` |
| v3 log | `9ab23d5c4e3b0acd69162e937ee1e5ac236ece4a47956636ba0c60ffa1bf414a` |
| v3 manifest | `570b22b66676c37bfd5fcc236e4d0a165219efcb6523a6cbc83afe91d2005344` |

All three triplets and the green output were copied locally and SHA-verified.
Current source equals the v3 snapshot byte-for-byte. All nine printed audit
names were checked against the source declarations, and `git diff --check`
passed. Failed sources remain evidence only, not checked exports.

## Remaining boundary

The result replaces a supplied typed `Accepted` execution with success of an
independently defined total functional verifier. It does not yet prove that
the mutable Rust loop, parser/descriptor sort, hash implementation, and caller
actually compute this function on the same inputs. That requires a separate
source correspondence argument, including natural-number/u32/usize transport
and the precise caller's parsed records/frontier bytes. The q22 specialization
uses the existing deterministic descriptor sort; it does not formally relate
that sort to Rust `sort_unstable`.

No commitment binding, chronological prefix reconstruction, late-target or
collision probability, random-oracle freshness, or global soundness theorem
is claimed by this leaf.
