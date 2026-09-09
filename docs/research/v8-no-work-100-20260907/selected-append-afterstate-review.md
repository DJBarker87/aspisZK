# Same-table append to the candidate afterstate

Source pin: `edb199c12fcc41f00330298b95b4736f60ac6f3a`. This continuation changes only new research proof/evidence files. Subsequent concurrent research files and main work are preserved.

## Deterministic endpoint

`SelectedAppendAfterstate.lean` connects the already proved output-pair compression to the selected twenty-block append tail. Its target is the **computed candidate root, all twenty candidate-frontier entries and exact integer cursor increment**, not an assumed successful compiler/append call.

The proof consumes one arbitrary recovered field table and two explicit prerequisite structures:

- `AppendResiduals`: the individual gated copy equations, complementary public sibling bindings, initial low-lane zeros and modeled two-round Poseidon residuals for blocks34–53.
- `AfterstateChecks`: the source's integer sequence/index guards, direct static frontier comparisons, dynamic carry-entry binding and final root binding. The source/live snapshot is independently supplied; nothing in the table manufactures its authority.

It constructs every block's ordered child pair, the actual node input including its tweak, and the eleven-pair round chain. Symbolic hash-chain induction then gives every intermediate boundary, not only the final root. The one dynamic frontier entry is thereby identified with the correct intermediate append hash; the other nineteen (or all twenty on terminal carry) follow from the direct comparisons.

`same_output_pair_afterstate` consumes `SelectedOutputPair` on the **same table**, replacing its row539 leaf with the node hash of that table's recipient/change commitments. `public_output_pair_afterstate` additionally consumes the literal public-commitment bindings and derives the field-stage `two_outputs` constructor's success, nonzero change sentinel and the complete candidate afterstate for that public pair. Existing output-note theorems can separately identify those commitments with decoded openings. No honest trace, expected leaf, decoder success or valid-witness predicate is assumed.

## Exact source/cell map

| Operation | Literal selected source/rows | New modeled derivation |
|---|---|---|
| Output-pair leaf | Block33 final row539 | Reuses `pair_digest_is_ordered_outputs` |
| Current at level `l` | Row`539+16*l`, lanes0–7 | All boundaries proved by induction |
| Append block | `34+l`, for `l<20` | Eleven compact pair residuals construct `RoundChain` |
| Left child | Row`556+16*l`, lanes0–7 | Current when index bit0; live frontier when bit1 |
| Right child | Row`544+16*l`, lanes8–15, with last-limb tweak removed | Empty root when bit0; current when bit1 |
| Current-copy families | Tags`1124073496+2*l` and `1124073497+2*l`, weight kinds3/4 | Exact `(1-bit)`/`bit` activation; no independent bit witness |
| Candidate root | Row859 = block53 final | Equals twenty-parent computation |
| Dynamic carry entry | Row`539+16*carry` = block`33+carry` final | Equals the computed prefix of length `carry` |
| Other candidate-frontier entries | `validate_transition`, direct array comparisons | Cleared/empty or preserved source entries, exactly |

Sources: `pair_forest_copy_terminal_constants.rs:52–91`; `pair_forest_copy_terminal.rs:362–375`; `pair_forest_semantic_terminal.rs:182–211,364–379,650–693`; `pair_trace.rs:560–596`; `incremental_merkle.rs:184–236`.

Pattern10's literal `1051521018` offset is the additive inverse of the maintained `NODE_TWEAK=1095962629` in M31. The new proof reuses the earlier symbolic cast identity and proves that this literal right-child copy expression is the untweaked digest. The complementary public right-child constraint uses the source expression `raw-(empty+tweak)`, not a silently assumed untweaked equality.

These are **individual digest-coordinate/copy equations**. The proof does not infer all eight coordinates from one scalar-packed equality at a sampled lambda. Accepted-proof enforcement and unbatching remain separate obligations. Initial low zeros are actual hash-input schedule constraints, not blanket zero-padding assumptions. All append reads are in rows539–860, within the selected table; no free mask cell is newly constrained by this proof.

## Carry, full capacity and source authority

`carryScan` is a bounded ascending scan of the actual index bits: continue while all preceding bits and the next bit are1, otherwise keep the first zero. `carry_scan_spec` proves its prefix/stop characterization and the bound by the scan depth. `carryIndex` scans twenty bits; the caller cannot choose it independently.

The source computes `min(index.trailing_ones(),20)`. The new mathematical scan has that intended operation and an explicit specification, but this leaf does not translate the Rust u64 intrinsic. The selected source guard is `index<2^20`, and the integer increment is `nextIndex=index+1`; the endpoint derives `nextIndex≤2^20`. It does **not** incorrectly require the result to stay strictly below capacity. When the carry reaches20, there is no dynamic frontier entry; the exact static rule clears all twenty entries and the node chain still supplies the terminal root.

The legacy `IncrementalMerkleV1` V7 formalization proves binary-carry/root reconstruction identities and chronological-tree invariants. It is relevant reusable mathematics, but its compiled leaf is absent from this cache. This continuation does not rebuild that unrelated closure or claim to apply it through an assumed successful `appendCarry`. The exact remaining connection is the dense twenty-entry frontier/bit scan to its `List (Option Digest)` carry representation, including terminal-full carry, plus equality of the pinned empty-root table with its recursive-empty-root model.

The source explicitly does not rehash the **old** live root in the selected semantic terminal. Consistency of the old root/index/frontier is a validated-Pool inductive invariant (`pair_constraint_residuals.rs:6–12`). `validate_transition` checks pool/deployment identifiers against public inputs but does not make those inputs authenticated by itself. Our afterstate theorem therefore names an independent live snapshot and does not conclude historical membership, freshness, spent-nullifier absence or atomic account mutation from an algebraic table.

`recovered_witness.rs:71–83` correctly compares the caller runtime binding, including the **outer forest root**, before invoking the compiler that temporarily substitutes the lane root. The new append endpoint neither removes that guard nor proves its authority. The full `compiled.public_statement == transition` comparison additionally needs the compiler's literal source/record correspondence and validated initial state. Those boundaries remain visible instead of assuming the whole compiler returns successfully.

## Scope and next deterministic step

The modeled amount, input owner/note/nullifier, occupancy, output notes/pair and decoded1+20+3 membership endpoints remain completed prerequisites. This continuation adds their append-tail/afterstate computation slice. Remaining deterministic work is not “all payment semantics”: it is their unified literal decoder/compiler/runtime interface, the concrete field/Poseidon/source translation and the validated account/frontier representation bridge described above.

The next focused bridge should connect the dense source frontier update to the existing V7 `appendCarry_reconstruct_more/full` identities **without assuming the append result**, including the `index=2^20-1` terminal case. That makes the row859 computation the same afterstate returned by the incremental-tree API, rather than merely a parallel mathematically specified hash path.

No new public message, proof value, nonce, query or verifier operation is introduced. The proof-body allowance remains **40,282 bytes**. No CU, Rust proving, replay or new privacy measurement is claimed. A deterministic endpoint is not an accepted-proof extraction theorem or a new probability term.

## Focused evidence

The full leaf is **kernel-checked for the stated deterministic modeled-source endpoint**. The first check failed only on a folded `appendStep` after a Boolean split and a misqualified `foldl_chain` name. Both are replaced by explicit unfolding with the saved bit equation and the already imported `HashMerkleModel` theorem. No theorem statement, source prerequisite or resource limit changed. Temporary `sorryAx` in the rejected diagnostic is absent from the green source/audit.

| Check | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| [v1](experiments/selected-append-afterstate-v1.log) | 1 | 22.08 s | 5,469,175,808 B | 0 |
| [v2](experiments/selected-append-afterstate-v2.log) | 0 | 27.87 s | 5,599,608,832 B | 0 |

All eleven final audits use only the standard `propext`, `Classical.choice`, `Quot.sound` subset; no added axiom or `sorry` occurs in retained source.

Source SHA-256: `6559324e4dd9e0535597e08a37e4d9cd8f9d67a277ef5d524e5320c540be7e33`.
Olean SHA-256: `01326e22ae41676f7f8a7507554f5deb48753c27f10bcd72fa8b855baa9907be`.

The runner reuses the existing pinned selected/V7 cache and verifies source/olean hashes against the research source pin. The existing source/olean closure was reused unchanged; no dirty main source or borrowed concurrent leaf was imported. Lean4.32.0 is pinned at `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, Mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997`. The log records the exact revision, target, command, exit, wall/RSS/swap and axiom audit, with a7,340,032-KiB aggregate child-process RSS guard and Lean `-M7000`. Both checks were serialized under explicit parent slot grants. No cold dependency, Rust/SBF build or broad replay was performed.

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_selected_append_afterstate.sh \
  docs/research/v8-no-work-100-20260907/experiments/selected-append-afterstate-v2.log
```

This is the archived exact command. The runner rejects an existing output filename; a future justified changed-source check must use fresh evidence. No witness/secret was evaluated or printed.
