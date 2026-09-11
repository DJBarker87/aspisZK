# Selected positive-transfer semantic rows and payment facts

Status: GREEN, two new leaves / 25 standard-only axioms audits. No verifier-acceptance,
extraction, probability, or complete checked-transfer-witness result is claimed.
Source parent: `2f92bdd5f08fa89060c85262a55c19545a002064`.
Borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

## Exact source and scope

`SelectedSemanticRowsV3.lean` models the Boolean-row semantic oracle of the
selected **positive transfer** profile. The ordinary crate has 94 base positions
0–93. The opt-in research profile adds inverse-product position 94; it therefore
has 95 base positions, packed into 24 QM31 lanes with slot 95 unused. The four
Poseidon lanes and the one extension-valued copy lane remain separate. This is
not a claim of 95 independent extension-field coordinates at off-domain points.

| Positions | Literal selected residuals retained |
| --- | --- |
| 0–15 | Initial states / node initial rate-half zeros, plus occupancy additions in 0–11 at rows 1017/1018 |
| 16–31 | Absorption padding zeros, including the actual moved output blocks |
| 32–48 | 24 direction bits and both gated child choices |
| 49–81 | Three current/successor/XOR12 ten-bit views, recomposition, and both auxiliary zeros |
| 82–83 | Both conservation equations, selected at row 1014 |
| 84–91 | Anchor, nullifier, both output commitments, all 20 append siblings, next root, and dynamic carry binding |
| 92–93 | Input asset and both output assets |
| 94 | Row-1014 recipient × change × reserved inverse − 1 |

The model includes the literal 21-by-8 generated empty-root word table; it does
not prove these constants by evaluating Poseidon. The public append cursor is
the existing bounded `SelectedAppendAfterstate.carryIndex` model. Its relation
to the Rust integer intrinsic and caller validation is not silently supplied.

Source hashes (SHA256):

- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`:
  `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.
- `pair_forest_semantic_terminal_constants.rs`:
  `68004ad1e56fba9947b8aa6f52b7eec6f3b8e9c1cfea671338945f7aa1f28111`.
- `experiments/positive_transfer.rs`:
  `f5031b80ff2d9f40689f2bd6d18323be330664bedd0aec24b34bd67aeeea12a8`.

The parent-reported devnet checkpoint `9e432896` is executed evidence for this
opt-in transfer profile, not a universal residual-to-witness theorem and not a
withdrawal result. No runtime suite was repeated for this Lean change.

## Deterministic proof surface

The first leaf constructs a 95-coordinate index type and proves exact injective
placement in 24-by-4 slots. Its cardinality proof uses a constructor equivalence
to a finite sum, not normalization of a generated 95-value enumeration.
`rows_at_coordinate` and `coordinate_zero` recover each actual residual from
the finite sum. `packedRows_zero_iff` uses the literal QM31 packer and the
already-green base-coordinate theorem, deriving coordinate separation rather
than assuming it. `copyResidual` retains the existing 136-link source row
constructor, public weights, active mask, and all four denominator slots.

The green dependent leaf `SelectedSemanticTransferV2.lean` derives, on the
**same** `semanticTable candidate`:

- `AmountSemanticChecks` and the source-94 inverse-product equation;
- actual initial states and note tail padding, including output rows 432/480;
- input pair direction/occupancy/spend checks from reused positions 0–11;
- asset, nullifier, and output commitment bindings. The append terms are not
  deleted to prove these: their support is shown disjoint from the earlier
  binding rows by `append_digest_below`;
- `TransferFacts` from these equations, explicit selected Poseidon block gates,
  and one weighted-copy alias result. Strict amount positivity is derived from
  position 94 and conservation, not from successful decoding or an assumed
  `tablePositivePack` result.

`member_transfer_or_copy_collision` additionally keeps the actual pre-lambda
`EarlyC1Family` member, base-word projection, sequential lambda/chi collision
alternative, and `CopyConditions` (local rows, helper boundaries, and poles).
It does not identify an adaptive reconstructed tuple with that member.

## V7 reuse and remaining implications

The coordinate finite-sum/projection proof narrowly reuses the pattern of
`V7AtomicSemanticRowsFromTrace`; its old fixed 20-group layout is not imported as
the selected 24-group layout. Packing uses `PositivePackBinding` and the pinned
V7 arithmetic equivalences. Amount recovery reuses the selected port of V7
range/no-wrap lemmas. Notes, owner/key/salt, nullifier, outputs, and pair fields
consume the existing selected early-C1 endpoints and their reused V7 residual
algebra. The earlier 62-row V7 projection is not treated as coverage of the
remaining amount, occupancy, moved-public, or Poseidon rows.

The first missing upstream implication is still actual accepted transcript /
authenticated masked terminal → all these same-table Boolean residuals and
the explicit Poseidon/copy conditions. No H/G/mask, inactive-helper, or source
zero-padding residual has been removed to define acceptance. Integer parsing,
selector evaluation, round-constant/source correspondence, early-family/own
support and reconstruction correspondence remain separate. Downstream full
membership/path authentication, output-pair append/settlement, caller/account
authority, and the complete checked witness remain separate too.

## Frozen focused check record

The parent runs only the smallest changed leaf through the existing capped
Tailscale NUC runner: MemoryHigh 8 GiB, MemoryMax 10 GiB, swap 0, CPU 200%,
Lean 4.32, `-j1 -M9500`. No laptop compilation or broad replay was performed.

All nine source/log/manifest triplets are local under the exact tags below;
all attempts recorded zero swaps. Failed proof audits containing `sorryAx`
are retained diagnostics, never members of a green proof closure.

| Tag | Exit | Wall s | Peak RSS KiB | Result |
| --- | ---: | ---: | ---: | --- |
| selected-semantic-rows-nuc-v1 | 1 | 0.92 | 2100568 | Missing AppendAfterstate artifact |
| selected-append-afterstate-nuc-v1 | 1 | 0.08 | 184492 | Missing OutputPair artifact |
| selected-output-pair-nuc-v1 | 0 | 3.10 | 6683356 | Unchanged dependency, 12 standard audits |
| selected-append-afterstate-nuc-v2 | 0 | 3.23 | 6690848 | Unchanged dependency, 11 standard audits |
| selected-semantic-rows-nuc-v2 | 1 | 6.03 | 6710524 | Reserved binder / concrete census reduction |
| selected-semantic-rows-v2-nuc-v1 | 1 | 6.48 | 6719372 | Deep concrete row projection |
| selected-semantic-rows-v3-nuc-v1 | 0 | 6.69 | 6773052 | New oracle, 11 standard audits; provenance 1045 |
| selected-semantic-transfer-nuc-v1 | 1 | 3.93 | 6704800 | Ambiguous residual / branch and index glue |
| selected-semantic-transfer-v2-nuc-v1 | 0 | 4.46 | 6744796 | New consumer, 14 standard audits; provenance 1047 |

V3 uses an abstract-vector projection lemma; TransferV2 qualifies residual
names and uses explicit finite support/index branches. No cap, depth, or
heartbeat increase occurred. All four green logs finish with unchanged
provenance, and every audited axiom belongs to
`{propext, Classical.choice, Quot.sound}`.

Green oracle SHA256 values:

- Source and snapshot: `e5c198980356442cd4337c3a20f21f18d8f7f0b865598f41cbb9ca63d376849e`.
- Olean: `c5064c6d7c9948cfc208551cbd6dec81242a607e20cc25aed1481c340450ea35`.
- Log: `6b9d1b1519cfe6aeb5a1fbb0656414065a06743618ec98dc8f83c5d6cf6d515b`.
- Manifest: `b35313e1d3d2b40e49d7242d980583c32940915c8efe4773379d17379b8bf1f7`.

Green consumer SHA256 values:

- Source and snapshot: `21020c07493be8d6cd247d05d67348a9d6f0bc5830f6f040e475e6f82a97d1d4`.
- Olean: `8a2a79c69e9af90d2b9c5d55ddb9f57b2ec5ca3361dc18d30be6efdbf885526c`.
- Log: `da99aaa9442afb133a2a7ba5aa7f2d83b891eb2d4b0759240b5d5ffa15f25cec`.
- Manifest: `5b164dcf884604dee49480ca1f3562c0f7cedf7387ec99e1beb7ae24b5ea354c`.

The clone-portable receipt `experiments/selected-semantic-transfer-evidence.json`
records all nine attempts, commands, hashes, resources, and individual audits.
Run from the worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_semantic_transfer.py --check-recorded
git diff --check
```

Logs/manifests/source snapshots and JSON are mandatory. Ignored local oleans
are hash-checked only when present; clone verification does not require the
build host or ignored payloads. The two newly checked dependency outputs are
stored under their run-tag names, preserving prior local cached variants.

The runner's original higher-Y bootstrap parent remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from this source parent.
Every failed source/log/manifest and exact green output hash is retained.
Imported cache artifacts are not claimed to have been rebuilt merely because
their hashes are pinned. No frozen source, unrelated untracked artifact, or
production source was edited.
