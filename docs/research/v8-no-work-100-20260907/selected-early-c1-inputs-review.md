# Same early-C1 table: input owner, note and nullifier

Status: **GREEN**, focused NUC v2; all eight audited theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. Source and report are frozen.
Working parent `2a49280b70f17a4539927d7c6fd3121c417f2d7e`. Parent ran NUC v1;
the seven predecessor audits passed with standard axioms, but the final
endpoint failed solely because `liftBase` was not in scope. Its failed
`sorryAx` diagnostic is not a retained green theorem. V2 adds only
`open AspisV8.PositivePackBinding`, as in the green output leaf.
The one-line fix changed no theorem statement or resource limit. Parent ran
the focused v2 check; no further build or source change accompanies this
review update. The historical draft source-header text remains frozen.

## Exact new implication

The leaf discharges the seven copy fields of the existing
`SelectedNoteRecovery.NoteResiduals` from the actual selected 136-link
`WeightedAliases` predicate on `memberTable candidate`. Their source
weight kind is literally `.one`, independently of the append index.

| Link | Actual source tuple equality | Active scalar count |
| --- | --- | ---: |
| 0 | row27 columns0–15 = row32 columns0–15 | 16 |
| 1 | row43 columns0–15 = row48 columns0–15 | 16 |
| 2 | row411 columns0–15 = row416 columns0–15 | 16 |
| 7 | row11 columns0–7 = row28 columns0–7 | 8 |
| 8 | row12 columns0–7 = row412 columns0–7 | 8 |
| 9 | row44 columns2–7 = row428 columns0–5 | 6 |
| 10 | row60 columns0–1 = row428 columns6–7 | 2 |

`input_link_shape` checks those seven literal entries and the actual tuple
patterns, all with zero additive offset. `input_alias_count` checks the
sum72; neither enumerates a field/table. `weighted_aliases_supply_input_limb`
specializes the weighted equality and projects only the resulting equality
to `.re.re`, using the existing `semanticTable_read` theorem. It does not
claim that arbitrary QM31 multiplication commutes with this projection.

`input_copy_aliases` exposes the 72 concrete scalar equations;
`input_residuals_from_selected_copy` fills the genuine `NoteResiduals`
record. Its only non-copy semantic inputs are `InputSemanticChecks`:

- Eleven paired gate steps for each of blocks0,1,2,3,25,26.
- Owner/note/nullifier initial-state constraints at rows0/16/400 with the
  existing domain and message-length constants.
- The six unused note-tail entries at row60 columns2–7 equal zero.

`input_hashes_of_aliases` consumes the already-proved
`decoded_hash_endpoint`: row11's owner is the hash of the same row12 key;
row59's input note uses that owner, row44 amount/asset and split salt;
row427's nullifier uses that same key/salt. `public_input_facts_of_aliases`
additionally consumes the literal asset44:1 and public-nullifier427 bindings.
No expected trace, honest hash, decoder success or valid witness is assumed.

`member_inputs_or_copy_collision` retains the exact early C1 family member,
base-valued received word, `CopyConditions`, lambda/chi memberships and
independent public parameters. It concludes the same-table embedding and
`InputFacts OR collisionPairs`, reusing the existing collision set once.
All four active-row slot poles and both helper-sum boundaries remain inside
`CopyConditions`; no late helper is moved before lambda or chi. The input
hash facts may be composed with the green amount/output and path theorems
only on the same member/table and the same public asset.

## Exact imports and cache requirements

Only two direct imports are added to this new leaf; both were already loaded
by the green `SelectedEarlyC1Outputs` check:

| Import | Source SHA-256 | Retained output SHA-256 |
| --- | --- | --- |
| `SelectedEarlyC1Amounts` | `146ad131832ffe3a16ee34f6b3ff5491627d52bb9a22c547bfb3cc3920a05318` | `4ec479af027b9eaf68a938b2feb6d6f8d4b05ceaa9a334a80f41cadcc25085a1` (NUC v4 log; local output is absent) |
| `SelectedNoteRecovery` | `0c281c1e59a538bc80c9aa88cf8d92f321b140050e9b5e410436696bc7f5a5d3` | `5fbfa077b05a1d961995621bb763973946ade7b8a10eecaed07b70013c5df33a` (existing local cached output) |

No additional cache modules were requested by this leaf. The earlier copy-only repair for
the output leaf already supplied missing V7 occupancy/forest/note closure;
no cold NativePayment endpoint, new Mathlib import or generic router is
needed. The actual v2 runner verifies 957 registered per-run artifacts before
and after compilation and reports `PROVENANCE_UNCHANGED=true`. This is an
artifact-registration check, not a new native-package compilation replay.
Reuse stays pinned to V7 `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

NUC v1 exited1 in3.24 s with peak6,693,876 KiB RSS and zero swaps. Its exact
`selected-early-c1-inputs-nuc-v1-source.txt`, `.log` and `-manifest.json`
are preserved locally. No cap increase or broad replay is proposed.

NUC v2 exited0 in3.64 s with peak6,724,788 KiB RSS, zero swaps and all eight
standard-only audits. Its exact `selected-early-c1-inputs-nuc-v2-source.txt`,
`.log`, `-manifest.json` and ignored green `.olean` are local. The retained
v1 diagnostic remains unchanged; no failed attempt is discarded.

Both focused checks used the inherited `run_higher_y_nuc.sh` over Tailscale,
Lean4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, `-j1 -M9500`,
and cgroup MemoryHigh8 GiB / MemoryMax10 GiB / MemorySwapMax0 / CPU200%.
The runner's original overlay parent remains
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the working parent.
Runner SHA-256:
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

Failed v1 source SHA-256:
`4ca5593f3c81fa2fd3851f1cd8f6b6d014d982877e291ec2a4b667bb129325db`.
Frozen v2 source SHA-256:
`d7736c3eb78fb25ce6776c5e10d055aa036a8bf16c25d6d63572f9dd1c629c4e`.
Green output SHA-256:
`ce579fff0ad056b6f86f522fe05ca742c06d1a802e6f8420f79bcb8fea98f473`.
V2 manifest SHA-256:
`7fac24990acfa6e1acf61b6cfc5a8784b209f398f9dc5b03878e9b60e616fa35`.
V2 log SHA-256:
`52043528a23c46b66d4d595f0b0cd8e7e781d6786c6e9ebb2fc4002ca6c379f3`.

Input-pair occupancy/parser, path/public anchor, strict amounts, output pair,
afterstate, runtime authority, freshness, actual Rust/Poseidon refinement and
acceptance-to-residual enforcement are deliberately not claimed here.
