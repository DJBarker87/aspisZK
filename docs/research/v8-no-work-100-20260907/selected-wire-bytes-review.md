# Exact selected Wire byte layout

Status: **GREEN**, focused `SelectedWireBytes` v3; 16 axiom audits, no `sorryAx`
or new axioms. [Source](experiments/SelectedWireBytes.lean) is frozen. No other
source was changed, no staging/commit occurred, and no package replay ran.

## Scope and source match

This pure Lean parser reuses `CanonicalRelationInput.parseFixed` and builds
all other Wire fields from the **same body**. It models the layout and guards
of [relation_callback.rs](experiments/relation_callback.rs), `Wire`/`parse`
at lines 85–91. That parser is also used by the selected performance verifier.
It is not a Rust/Aeneas translation theorem or proof that a deployed binary
returned success.

Offsets are half-open byte intervals:

| Wire component | Exact source layout |
| --- | --- |
| 697 canonical QM31 fields | `[0,11152)`; each field occupies 16 bytes |
| C1 / C2 roots | `[11152,11178)` / `[11178,11204)` |
| Nonces | `[11204,11228)`; gamma/fold/query slices begin at 11204/11212/11220 |
| 22 packed query records | `[11228,24890)`; original ordinal `q` begins at `11228+621*q` |
| First frontier | `[24890,24890+n)` |
| Second frontier | `[24890+n,body.length)` |

Here `n=(body.length-24890)/2`. Successful parsing implies that there is a
single integer `f≤296` with `body.length=24890+52*f` and `n=26*f`.
Consequently both frontiers have exactly `f` 26-byte digests and there are
no discarded remainder bytes. Minimum length 24890 (zero frontier entries)
and maximum length 40282 are permitted by this parser; actual multiproof
verification has its own further checks. A record's packed M31 limbs are
**not** decoded by this Wire parser, matching the Rust path that defers
that step to `opened_values_prepared`.

## Exported proof interfaces

Every source-shaped theorem takes only `SelectedWireBytes.parse body = some wire`:

- `parse_success` yields the existing fixed-parser success for `wire.values`
  and exact equality to `assemble body wire.values`.
- `fixed_fields` gives length 697 and the exact successful canonical decoder
  at every fixed-field byte interval. Thus existing decoded response/final
  theorems can be used directly.
- `roots_exact` gives both root bytes as in-bounds body reads. `nonce_byte`
  gives each of the three 8-byte nonce sections. No integer interpretation
  or grinding predicate is introduced.
- `record_eq_bodyRecord` identifies each original-ordinal record with the
  **existing** `PackedQueryRecord.bodyRecord`; `record_bytes_exact` reuses
  its proof that all 621 bytes are in bounds. No sort or relabelling occurs.
- `frontier_lengths` proves the equal 26-byte-multiple lengths and cap.
  `second_frontier_to_end` proves the bounded slice used by the Lean
  constructor equals Rust's open-ended second slice on success.
- `Wire.frontierPairs` constructs a literal `List (Fin 2 → Digest208)`
  aligned at one ordinal across the two halves. `frontier_pairs_length`
  proves its cap 296; `frontier_pair_byte` identifies every byte of every
  pair with its exact body offset. No supplied frontier correspondence
  premise replaces this construction.

The remaining audited helpers are `slice_length`, `slice_byte`,
`malformed_length`, `successful_length`, `fixed_slice_lengths`, and
`frontier_byte`. All indexing proofs are symbolic; no concrete body or
large field/domain enumeration was evaluated.

This closes byte slicing and typed input construction, not the mutable
Merkle-loop-to-`MinimalMultiproofPaths.Accepted` correspondence, hash-log
coverage, authentication exceptions, or transcript challenge scheduling.
It supplies neither a successful semantic/payment check nor ROM freshness.
The already checked paired-prefix-to-batch lemma still requires successful
packed-record decoding and authenticated projections of those same bytes.

## Attempts, limits and evidence

Source parent: `531b50ed6cd06d5902417edf614daee137c19acb`.
Rust source SHA-256:
`285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed`.
Only the focused target was compiled, serially on the existing pinned NUC
overlay, via Tailscale `100.108.41.90`. The host-key alias `nuc.local` is not
the transport endpoint. Initial guard found no active build/compiler and
50,124,541,952 bytes available RAM. Each cgroup logged MemoryHigh=8 GiB,
MemoryMax=10 GiB, MemorySwapMax=0, CPUQuota=200%; Lean 4.32.0 used `-j1 -M9500`.
Source limits stayed maxRecDepth=200 / maxHeartbeats=200000 throughout.

| Attempt | Exit | Lean wall | Peak RSS, KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.13 s | 6,681,976 | 0 | Local parser proof, dependent root rewrite, projection simplification and final theorem parser fixes needed |
| v2 | 1 | 3.11 s | 6,682,348 | 0 | 15 audits green; only rewriting a frontier length inside a dependent `Fin` coercion remained |
| v3 | 0 | 3.36 s | 6,715,892 | 0 | All 16 audits standard-only; separate Nat count equality removed the dependent rewrite |

V1/V2 failures and their source snapshots are retained, not counted as
checked releases. A pre-launch v3 SSH command mistyped `project-offloads`
as `project-offs` and exited 127 before the runner/compiler/snapshot; the
corrected command then started the fresh v3 tag. There was no unchanged
Lean retry or additional build.

Each attempted manifest preflight reported `OVERLAY_PROVENANCE_PASS=1103`.
V3 postflight also passed 1103 with `PROVENANCE_UNCHANGED=true`. Its
`slice_length` audit is `[propext, Quot.sound]`; the other 15 are
`[propext, Classical.choice, Quot.sound]`.

| Attempt | Source / frozen source SHA-256 | Manifest SHA-256 | Log SHA-256 |
| --- | --- | --- | --- |
| [v1 source](experiments/selected-wire-bytes-nuc-v1-source.txt) | `e27d4d4a6bd555b835188ef91ef25004dfa054b452cafb227b1dff512cfff76c` | [manifest](experiments/selected-wire-bytes-nuc-v1-manifest.json) `6be1e115dd99757dc722604f1ee4de596533d9629a53b376f28951e68aa3f4d8` | [log](experiments/selected-wire-bytes-nuc-v1.log) `c46b5413ad11b12a6e70d3306b1b28fccf0430059853c4f57d1bca5e038d034e` |
| [v2 source](experiments/selected-wire-bytes-nuc-v2-source.txt) | `32a739a36412612b45b5fd5626bba5811a0f60f2f7d73dad8ca8179918639ae2` | [manifest](experiments/selected-wire-bytes-nuc-v2-manifest.json) `b87d0ad7e465b76c0a0d0fef881da3f2a9d46188be2355456fd055ce38791da8` | [log](experiments/selected-wire-bytes-nuc-v2.log) `1560a22dd168cf761fc128ab5bc13b3f43d0bf111bfd48e6adb96c2b51fd0e3d` |
| [v3 source](experiments/selected-wire-bytes-nuc-v3-source.txt), identical to final source | `0ecea0d5af495c72bd2c116d63b030d124534e41737fe84c27f93792a142e273` | [manifest](experiments/selected-wire-bytes-nuc-v3-manifest.json) `e857daa2efce1ae061920e95ee9fc81d0f6c70b0bac85a9800248bcb6fb8ef61` | [log](experiments/selected-wire-bytes-nuc-v3.log) `f7a6fd0c745ca7e062261ad3d39398b9bda4f11dd32e55c3e9844f2ee4de5fa5` |

Remote `.olean` digest **recorded in the v3 log**, not copied or committed:
`a3cb5c1d37477096a65772beadf7b750d491b84556b58073792a949e3e674044`.
[Inherited capped runner](experiments/run_higher_y_nuc.sh) SHA-256:
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
Its cache/research pin remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`,
distinct from the source parent; borrowed V7 source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. Exact import pairs are frozen
in the manifests. No old cache variant was replaced or broadly rebuilt.
