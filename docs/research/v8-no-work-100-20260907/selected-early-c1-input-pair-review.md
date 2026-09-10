# Same-table early-C1 input-pair decoding

Source parent: `b2557a4b77212c77e44d29eea1b94e820bf939f8`. Research only;
no protocol, production source, wire, or verifier change.

Status: **green v6**, ten standard-only axiom audits, 3.35s,
6,725,856KiB peak RSS, zero swaps. Source and evidence are frozen; failed
v1–v5 source snapshots/logs/manifests remain retained.

## Endpoint and exact source map

[`SelectedEarlyC1InputPair.lean`](experiments/SelectedEarlyC1InputPair.lean)
derives the seventeen copy equalities previously assumed by
`SelectedPairDecoder.InputPairResiduals`, on the same `semanticTable candidate`
as the existing early-C1 amounts, input notes and output openings.

| Selected index / tag | Producer | Consumer | Meaning |
|---|---|---|---|
| 18 / 1124073490 | row64, slot0, pattern10 | row1017, slot0, pattern11 | adjusted right child = occupancy digest (8 limbs) |
| 19 / 1124073491 | row913, slot0, pattern6 | row1017, slot1, pattern7 | decoded side = occupancy selected side (1 limb) |
| 66 / 1124073538 | row914, slot1, pattern13 | row64, slot0, pattern10 | decoder right digest = adjusted right child (8 limbs) |

These are the actual selected 136-link registry entries in
`pair_forest_copy_terminal_constants.rs:46,47,94`; all have constant weight
one. No old 183-link inventory is substituted. Pattern10 reads columns8..15
and adds `1051521018` only to the final limb. The symbolic identity
`1051521018 + NODE_TWEAK = 0` in M31 identifies this with the selected
decoder's negative node tweak. The public offset is not erased before the
alias proof. Only equality and addition of a public integer are projected
from QM31; arbitrary products are not projected to their base coordinate.

The source table's first/second commitments are row914 columns0..7/8..15;
occupancy and inverse are row1017 columns0/1; its certified second digest is
row1017 columns2..9. The last limb, column9, is the sentinel. The actual side
is row913 column0. Direction rows are
`913 + 16*(level/4) + 4*(level%4)` for all24 levels.

`input_pair_residuals_from_selected_copy` combines the derived copies with
`InputPairSemanticChecks`. These are precisely the remaining36 equations:
24 direction Boolean checks, the occupancy Boolean, sentinel inverse, empty
inverse, eight empty-digest checks, and selected-spend check. They match
`pair_forest_semantic_terminal.rs:557–577` at the input-occupancy selector,
plus its path direction gate. The theorem does not derive these equations
from a single packed scalar relation.

`input_pair_facts_of_aliases` consumes the existing
`SelectedPairDecoder.residuals_imply_checked_input_decode`. It proves that
the field-stage decoder returns the literal pair and side, that this pair
is valid, that its selected slot is spendable, and that all24 directions
parse. In particular the defensive occupied-sentinel rejection is discharged
using V7 occupancy algebra, not an honest salt/nonzero-digest premise.

The final `member_input_pair_or_copy_collision` retains the actual fixed
`EarlyC1Family.family c1`, the same member's base-field embedding, and the
existing `collisionPairs` alternative. `CopyConditions` still requires local
weighted residuals, the total and inactive helper boundaries, and all four
active-row slot denominators, including zero-weight slots. Public weights
are independent parameters. A late C2 table is not frozen before lambda;
no new probabilistic collision or freshness claim is made.

## Reuse and remaining source implication

Direct imports are the existing `SelectedEarlyC1Outputs` and
`SelectedPairDecoder`. The latter imports pinned
`AspisFormal.Pool.V7PairLeafOccupancy`, whose sentinel/empty-slot lemmas match
these exact pair semantics. Borrowed source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The offset lemma is a narrow port of
`SelectedOutputPair.literal_right_offset_cancels` (source SHA256
`cdce2ed893d0d1e87ad1e838df2ea9dd9c1d19409e5053d0be6d93749616e4e1`),
which itself ports the V7 symbolic cast argument. `SelectedOutputPair` was
not imported because its cached pair was absent; no cold dependency build
or additional cache closure was started.

For Gamma29 reconstruction, choose this candidate to be the SAME reconstructed
tuple's C1 projection and separately establish its membership in the fixed
early family. Exact87 claim equalities do not establish that membership,
common own support, these36 semantic residuals, or the helper/pole conditions.
The first missing source implication is still authentic selected semantic
constraint enforcement on that same tuple (with its actual masks and causal
failure exclusions), not another interpolation identity. No unused87-claim
premise is added to disguise that gap.

This endpoint is field-stage input-pair decoding, not whole `extract_checked`
success. Canonical byte parsing/source refinement, selected input-note/child
binding, hash-path/public anchor, caller context, and append/settlement
composition remain separate endpoints/obligations. Existing modeled
note/path/output results are not claimed wholly open, but their assembly
into one checked transfer witness is not supplied here.

## Focused evidence

Only this new leaf is compiled on the Tailscale NUC. The inherited runner
records research bootstrap `289d7356c78a4cd493fe61a54f9548f2a0c11298`, not
the new source parent above. Runner SHA256:
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
Lean4.32.0, `-j1 -M9500`, MemoryHigh8GiB / MemoryMax10GiB / SwapMax0,
CPU200%. Native packages are pinned cached artifacts, not a package replay.

| Attempt | Result | Wall | Peak RSS KiB | Swaps | Disposition |
|---|---:|---:|---:|---:|---|
| v1 | exit1 | 3.69s | 6,684,608 | 0 | failed static `rfl` depth and conditional rewrite; not accepted evidence |
| v2 | exit1 | 3.13s | 6,692,676 | 0 | combined metadata certificate lacks `DecidableEq WeightKind` |
| v3 | exit1 | 3.19s | 6,691,792 | 0 | remaining literal vector lookup exceeds depth200 |
| v4 | exit1 | 3.29s | 6,693,668 | 0 | explicit vector selector simplification still exceeds depth200 |
| v5 | exit1 | 3.21s | 6,692,908 | 0 | ten standard-only declarations, but comment/option placement syntax error |
| v6 | exit0 | 3.35s | 6,725,856 | 0 | all ten audits standard-only; complete999-entry before/after provenance |

All six triplets are retained under
`experiments/selected-early-c1-input-pair-nuc-v{1..6}*`. Failed declarations'
downstream `sorryAx` reports in v1–v4 are not accepted axioms. V5's static
lookup fix proved all declarations, but its syntax error still excluded that
run from release. V6 changes only the comment placement.

After direct lookup, decidable lookup, and explicit vector-selector rewrites
all exposed the same finite metadata depth, the parent authorized
`maxRecDepth1000` around **only `pair_link_shape`**, matching the existing
`SelectedCopyLayout` static certificate. There is no field/table/challenge
in this three-entry certificate. Every field, decoder and family proof stays
at depth200; all memory and heartbeat caps are unchanged. No generated
recurrence or concrete finite field is enumerated.

The v1 manifest checked991 entries but omitted the present direct
`SelectedPairDecoder` pair. This was found before retry and reported to the
coordinator. The authorized mechanical append registered exactly that
already-present source/output pair, without copying or replacing artifacts
or compiling a dependency; its sole V7 import was already pinned. Base
manifest entries grew818→820, and the green-output state was unchanged.
The v2–v6 manifests include the pair. V1 is not described as a complete
imported-closure receipt. Intervening unrelated V7 jobs caused preflight-only
holds; no runner or unchanged Lean retry was launched during those holds.

Final v6 SHA256:

- source/snapshot: `b57f991ab6429b1eab0ac0db56f899efbc4b0c3fdf8385819342badb0d7f945c`
- output: `bc8b6191167021fa02f74fec067d7402ea419119528e64b8651457d3e468efa4`
- log: `33546903f865f750c70d41aee891ae71b6ad6fb4ed48a73acc50a6e7bcf7aee9`
- manifest: `8042a4f120b72a0366a3ec339a0a49ba9ac74c7bb8165d20f01aa2d39b74324b`
- append receipt: `fd6927f83763dc9829b0b8260c95ed7817b02782de1747786a508da32e0fdb79`

The [evidence ledger](selected-early-c1-input-pair-evidence.json) records all
attempt hashes and the append receipt. The green output was copied locally
and hash-checked, but that ignored compiled copy is optional for publication;
the retained logs/manifests/snapshots and receipt are not optional. A read-only
artifact check verified all six source-to-manifest hashes, statuses, ten-audit
census, caps, and final standard-only999-entry postflight, plus the exact
two-entry before/after append. No full manifest compilation was replayed.
