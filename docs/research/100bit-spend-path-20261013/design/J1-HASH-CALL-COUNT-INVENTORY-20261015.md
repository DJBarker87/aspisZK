# S2 verifier HashFn call-count inventory

This is a source-control-flow inventory for the cost-probe verifier, not a proof or release-gate result. It counts calls made through the supplied `HashFn` during verifier execution. It does not count distinct oracle addresses, and it assumes observer callbacks do not themselves hash. No build was run.

The inspected worktree revision was `764bf20a6fe0392951b670f73748a54f70c9f272`. Source pins:

| File | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/transport.rs` | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| `crates/aspis-core/src/r0/merkle.rs` | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `crates/aspis-core/src/r0_transcript.rs` | `2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1` |

## Call accounting

| Component | Calls | Source path |
|---|---:|---|
| Semantic transcript initialization | 1 | `r1_wire.rs:173-180` |
| Semantic rows 0 through 26 | 27 × 3 = 81 | `r1_wire.rs:189-202,215-240`; rows 0-14 in `begin` at `r1_wire.rs:344-357`, ten polynomial rows and two circle rows in `r1_semantic.rs:83-90,127-130` |
| **Semantic verifier maximum** | **82** | Initialization plus all 27 rows; semantic checks may reject before later rows |
| Opening transcript initialization | 1 | `transcript.rs:7-13` |
| Gamma, kappa, alpha0, alpha1 for S2 | 4 × 3 = 12 | `verifier.rs:87-95`; S2 has two folds (`transport.rs:5-9`) |
| Query sampler absorb and eight squeeze/advance pairs | 1 + 8 × 2 = 17 | `transcript.rs:35-43` |
| Rho challenge | 3 | `verifier.rs:96-98`, `transcript.rs:17-33` |
| **Opening preparation maximum** | **33** | Sum of the four rows above |
| One S2 query: C1/C2/folded leaves | 3 | `verifier.rs:242-260`; each `merkle::leaf` or `private_leaf_hash` invokes `HashFn` once (`r0/merkle.rs:17-19`; `state_only_private_merkle.rs:28-35`) |
| One S2 query: three six-level Merkle paths | 3 × 6 = 18 | `verifier.rs:120-128,252-262`; each `merkle::parent` invokes `HashFn` once (`r0/merkle.rs:20-31`) |
| **One successful S2 query maximum** | **21** | Three leaves plus 18 parents |
| Checkpoint serialization | 3 | `verifier.rs:302-316`: proof hash, public-bytes hash, checkpoint checksum |
| Checkpoint resume validation | at most 3 | `verifier.rs:325-339`, especially the short-circuit comparisons at line 328 |

For the selected paired route, `tx1(..., k=10, ...)` performs up to ten successful queries and writes a checkpoint; `tx2_authenticated` then validates that checkpoint and resumes at query index 10, performing up to twelve more queries (`verifier.rs:342-349,380-385`). The paired upper bound is therefore:

`82 + 33 + 22 × 21 + 3 + 3 = 583` raw `HashFn` invocations.

The pairing matters. A standalone `tx1(k=10)` has a maximum of `82 + 33 + 10 × 21 + 3 = 328`. A standalone low-level `tx2_authenticated` can resume from a syntactically valid checkpoint whose `next` is zero, so its maximum is `3 + 22 × 21 = 465`. Two arbitrary, unpaired calls can sum to 793. The 583 figure is only for one selected pair where tx2 consumes the authentic checkpoint produced by tx1 with `k=10`; the source comments state that checkpoint provenance and proof immutability are caller preconditions (`verifier.rs:351-378`). The code’s checksum is unkeyed, and the function alone does not establish that provenance.

## Rejection paths and count scope

The table gives maxima, not guaranteed counts. `tx1` checks `k` and parses before semantic hashing; semantic verification can reject after only a prefix; `Prepared::new` may fail after a prefix of its schedule; a Merkle check short-circuits subsequent paths; failed queries do not advance `a.next`; and a failed tx1 returns no checkpoint. On tx2, shape checks precede resume hashing, and the three hash comparisons short-circuit. No rejection path in the paired route exceeds the successful-path maximum. A query that reaches its final folded Merkle path uses all 21 calls even if a later query/algebra check rejects.

The `private-leaf-salts` feature chooses a different one-call leaf helper and wire offsets, but does not change the number of leaf hash calls. The S2 count includes the folded tree; S1 would not have that third leaf/path.

These are raw function invocations. An invocation can reuse an input previously hashed, so 583 is not a count of distinct first reads. The exact number of distinct oracle inputs is data-dependent and cannot be derived from this control-flow count alone.

The selected verifier route reaches `r1_semantic::verify_observed`, which uses `r1_wire::SemanticTranscript`; the separate `semantic_wire.rs` transcript implementation is not an additional call on this path. Other hash sites are outside the selected verifier call graph: `host_commitment.rs:194-211` builds commitment leaves, `prover.rs` contains prover/fixture hashes, and `dense.rs` is an alternate verifier implementation. They are not called by `tx1` or `tx2_authenticated` here.
