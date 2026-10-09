# Selected append residuals from the same table

Status: **V2 GREEN and frozen**. Import
`experiments/SelectedSemanticAppendResidualsV2.lean`, whose namespace is
`AspisV8.SelectedSemanticAppendResiduals`. V1 remains a retained failed
diagnostic, not an import dependency or successful proof.

Source parent: `d879105131a34a4bd087409bced83778d3ea8a96`.
V2 source SHA256:
`a175259706c5773d3af57b1c6d7b6ab66d0d288085fadf6b131b3ceae248d5dd`.
The single direct import is the frozen green
`SelectedSemanticOutputTransition`:
source `9661416d3c81a21518c1837b08e1fc8a3cf807b991864817b1b6594d48294633`,
olean `f67b39ac8785e9062ad71462cc2f41af6449d787d06719d3d89108567e8634b7`.
No new V7 import or cold dependency closure is requested.

V1 (`selected-semantic-append-residuals-nuc-v1`) reached the proof and
exited1: wall4.70s, peak6,736,084KiB, zero swaps. The only failed proof
components were the finite-sum isolation lemmas. Broad simplification
changed the sum's guards before the named `single` equality could rewrite;
one live-row side condition likewise simplified a row inequality to the
opposite orientation of a Fin-value inequality. V2 unfolds only the outer
residual and rewrites `single` first, and uses `simp only` with the already
proved exact row inequalities in each off-diagonal summand. No statement,
resource cap, static certificate or field-depth bound changes.

V1 source and local retained triplet:

- source `SelectedSemanticAppendResiduals.lean` and
  `selected-semantic-append-residuals-nuc-v1-source.txt`:
  `91593ffa7e6b3e770f501a1b6a3cac4edb4d6ad146e5c90ebe31151750effffe`;
- log `selected-semantic-append-residuals-nuc-v1.log`:
  `cf126b7eb7bbb3b1cab0b2ac166ea6a1fd2405a62be612ffb81ec7fc1b777431`;
- manifest `selected-semantic-append-residuals-nuc-v1-manifest.json`:
  `47501d4855b49702f0e1036ead425bc874cb17894398d0d376d0bb50acacfc44`.

The failed attempt is not green evidence, including all downstream axioms
reports that transitively contain `sorryAx`.

V2 (`selected-semantic-append-residuals-v2-nuc-v1`) exited0: wall4.44s,
peak6,752,552KiB, zero swaps. All ten declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Both provenance checks passed1055
entries and `PROVENANCE_UNCHANGED=true` was retained. The runner was Lean
4.32.0 with `-j1 -M9500`, High8GiB/Max10GiB/Swap0/CPU200%, reached over the
verified Tailscale address. No further proof run occurred during closeout.

Exact V2 artifact hashes:

- source and `selected-semantic-append-residuals-v2-nuc-v1-source.txt`:
  `a175259706c5773d3af57b1c6d7b6ab66d0d288085fadf6b131b3ceae248d5dd`;
- log: `63b142f003ba0d069fad274e94f069b9387a083cdde6ba3ebf516621ab15fdb3`;
- manifest: `92e38f7e77a54ae46ffcb25e00e982686553e8afaf04332d1e160206388c5b51`;
- olean: `50773ac7785e3ca55db49e17f8299d0b30bb6bf7c4b40a139030b5aa911c2230`.

The inherited runner bootstrap remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from this leaf's source
parent above. Borrowed V7 source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; runner SHA256 is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
Imported artifacts/native package revisions are a pinned-cache boundary,
not an assertion of a new cold compilation replay.

## Deterministic endpoint

`append_residuals` derives all six fields of the existing
`SelectedAppendAfterstate.AppendResiduals` from the complete selected
95-position `RowsVanish`, actual selected `WeightedAliases`, and modeled
`PoseidonChecks`, all on `semanticTable candidate`. The empty-root array is
the literal `SelectedSemanticRows.emptyRoot`, not a new supplied array.

| Append field | Actual source used |
| --- | --- |
| `currentLeft` | link `24+2*l`, active exactly when public index bit `l` is false; row `539+16*l` to `556+16*l`, pattern1 to pattern1 |
| `currentRight` | link `25+2*l`, active exactly when bit `l` is true; row `539+16*l` to `544+16*l`, pattern1 to pattern10 |
| `emptyRight` | digest coordinate84–91 at row `16*(34+l)` when bit is false; literal empty root plus last-limb node tweak |
| `liveLeft` | the same digest coordinates at row `16*(34+l)+12` when bit is true; public frontier entry |
| `initialLow` | initial coordinate0–7 at row `16*(34+l)`, block34–53 |
| `pairs` | actual same-table `BlockResiduals` for each of blocks34–53 |

`semantic_transfer_transition` consumes this constructed record and the
previous green transition theorem, removing its supplied `AppendResiduals`
premise. `member_transition_or_copy_collision` keeps the same fixed early-C1
family member, base-word embedding and one existing sequential copy
collision alternative. It preserves every pole/helper condition inside
`CopyConditions`; it does not multiply collision charges or substitute a
late table fixed before its challenges.

## Layout falsification and source correspondence

The potential failure was cancellation between additive public-digest
selectors. The checked proofs isolate each chosen summand, not merely
assume it vanishes because their sum vanishes:

- Empty sibling rows are 0 modulo16 and live sibling rows are 12 modulo16.
  Different levels in either family are distinct, and the families do not
  intersect.
- Anchor907, nullifier427, outputs475/523, root859 and dynamic carry
  `16*(33+carryIndex)+11` are all 11 modulo16, so none can cancel a sibling
  term. This remains true without assuming an index bound or a carry value.
- Initialization blocks34–53 lie in the selected node family, outside the
  first-hash block set0/1/25/27/30. Occupancy rows1017/1018 are disjoint.
- Pattern10 has width8, columns8–15 and offset1051521018 on its last limb.
  The offset is retained literally. The existing append theorem proves that
  this is the untweaked right input; no sign change is silently inserted.
- An inactive copy weight yields only the zero gated equation. Projection
  to the base field occurs only after the active weight is proved one and
  an actual QM31 equality is obtained.

The forty metadata entries are the literal selected136 registry entries,
tags1124073496–1124073535. The static certificate alone uses scoped
`maxRecDepth 1000`, matching the previously green metadata certificates;
all field/row/decoder/family proofs retain depth200. The sibling sums are
handled symbolically by `Finset.sum_eq_single`, not by expanding twenty
field terms or enumerating public indices.

Inspected Rust source, with unchanged hashes:

- `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs`,
  COPY_PATTERNS1/10 and COPY_LINKS24–63:
  `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50`.
- `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`,
  `public_digest_lanes` and its twenty append sibling bindings:
  `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58`.

This reuses the existing exact selected Boolean-row/source-shaped oracle,
not an old one-output V7 append interface. It remains a mathematical source
model, not a Rust execution/refinement theorem.

## Remaining explicit boundary

`AfterstateChecks` is still supplied: sequence/index equality, non-full
index, increment, static frontier checks, and dynamic carry/root bindings.
The latter two can be separate next projections from digest rows11 mod16;
they are not removed or claimed proved here. Caller/account authentication,
authority of the live snapshot, historical input membership, deployed
Poseidon/round-constant faithfulness, and actual verifier acceptance remain
open. A recovered tuple's early-family membership or exact semantic rows
are not inferred from high support or from acceptance in this leaf.

## Reproducible evidence and publication

Read-only command, from this research worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_semantic_append_residuals.py --check-recorded
```

The auditor validates the prior output-transition receipt, both current
source/log/manifest triplets, exact resources and axioms, and all five
imported retained green source/olean pairs. It additionally checks all forty
literal Rust append links and the small public-row disjointness metadata.
That static check is not finite-field elimination or probability evidence.
The JSON binds this report and the audit script by hash. Retained sources,
logs, manifests and JSON are mandatory; ignored local oleans are verified
only when present, keeping the receipt clone-portable. The local green
olean was copied and hash-verified, but is not a publication file.

Scoped publication: the two Lean source versions, this report, the new
audit script and its `selected-semantic-append-residuals-evidence.json`,
plus each attempt's log/manifest/source snapshot (eleven files total).
No existing green source, unrelated untracked file, ignored cache payload,
commit or Git index was modified by this task.
