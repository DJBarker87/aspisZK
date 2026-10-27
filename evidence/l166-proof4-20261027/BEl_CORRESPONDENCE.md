# Source-to-reference correspondence (partial, not physical closure)

The exact original function bodies and hashes are in BEl_source_cuts.json.
BEl_generate.py --check validates each source cut before any gate. The safe
Rust reference is BEl_rust/src/BEl_reference.rs; generated source is
BEl_rust/src/BEl_frozen.rs. Both are isolated from release compilation.

| Shipped source | Owned Rust reference | Lean interface and status |
|---|---|---|
| candidate.rs:162-170, zero idx/val, three sequential ? calls | batch, one shared idx/val, for slot0..3 and ? | SdkC_BatchSource.code / Port9OR_Batch.values; whole Rust equivalence still required |
| :174-178, lo/n/slot and packed sorted keys | tree, lo/n/slot and same actual key/sort helpers | Existing Port4B/Op5 lowerings reused; no new sort theorem credit |
| :180-186, selected opening and leaf digest | tree per-position range and leaf | Exact one-step cut substitutes already selected832-byte slice; opening geometry not inferred from arbitrary slices |
| :117-131, three leaf grammars | leaf, explicit tag/value/salt ranges and raw digest call | Three arbitrary-byte coordinate gates; not yet whole physical instance |
| :187-197, hash before duplicate check and scratch update | tree duplicate comparison and append | leaf_step pair preserves complete scratch and one-call observation, including mismatch rejection |
| :198, actual node_count | same actual node_count | Existing source/P6 lowering; no stub |
| :199-203, slot/count and8-byte zero padding | same slot range, count check, word scan | Remaining loop split if whole probe fails; count max172, padding max688words |
| :205-208, actual verify_in_place and Merkle error | same actual verify_in_place | Existing P6 accepted scratch induction retained; actual body executes in Kani |
| Digest32::digest returns raw32 bytes | Recording pushes address/part bytes before entry and fills Some(Ok(reply)) on return | BEl_Recorder pending/completed; BEl_RawBackend stateful returned-call model |
| batch Result rejects after prior calls | reference returns with recorder outside Result | BEl_RawBackend.correspondence for arbitrary effect syntax; not a Rust extraction certificate |

A line correspondence table is not a proof that the copied/rewritten loop
semantics matches the actual reached native cut. The full Kani equality is
still required, followed by binding that observation to BEk's SAME proof,
Prepared/root arrays, ordinal, borrow geometry and initial runtime state.
No missing Kani result is encoded as an axiom or assumed whole BothSlots law.

The source's raw backend can fail to return. Recording stores the attempted
address before backend entry, but a complete nonreturn semantics must account
for that pending entry. BEl_RawBackend is explicitly the returned-call model;
it does not identify a pending native attempt with a returned source .div.
