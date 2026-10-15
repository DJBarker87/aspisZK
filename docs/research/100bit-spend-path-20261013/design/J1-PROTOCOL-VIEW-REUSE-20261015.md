# J1 protocol-view reuse inventory

Read-only inventory of the merged J1 design and the current semantic/opening
Lean interfaces. This records reusable statements and the smallest proposed
view adapter; it does not claim a source-to-model refinement or close J1.

## Existing interfaces

`R1SemanticPayloadView` already turns a *typed, caller-supplied* 25-element
payload vector and C2-word callback into the old masked semantic rows. In
[`SemanticPayloadView.lean`](../lean/SemanticPayloadView.lean),
`SemanticPayloadView.toMessage`
(lines 19–24) maps the four payload constructors to the old `.base`, `.h1`,
`.maskSum`, and `.roundPoly` messages. `rounds` (31–35) pairs those messages
with caller-supplied challenges. The checked parser facts are
`semChalsZ_rounds`, `c2OfZ_rounds`, `claimOf_rounds`, and `semPolysZ_rounds`
(154–201), and `polynomial_degree` gives the bound 27 (203–205). The validity
indexed accessors `rootAt2`, `claimAt14`, `coeffAt` and their payload equalities
(37–110) establish the constructor layout. These are model-view equalities;
the module comment explicitly says the C2 callback is supplied and makes no
extraction/source claim.

The payload byte model is [`SemanticRecordCodec.lean`](../lean/SemanticRecordCodec.lean):
`Payload`, `validRow`, `RowPayload`, `encode`, and `decode` specify strict
frames and the row-specific payload codecs. `decode_encode` and
`encode_of_decode` prove codec round trips. They do not identify a current
unified-protocol `Message M` or `RawRoundDecode.Rec M` with these bytes.

The old prefix-to-opening adapter is already present in the v8 tree:
[`R0P/MaskView.lean`](../../v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean),
`openingViewZ_of_parsed` (lines 195–224). Given a 25-row semantic list, its
length, parsed challenges, parsed C2 words, `c2Base`, and the two circle rows
with `z₀ ≠ z₁` and both non-rationality facts, it proves `openingViewZ` returns
an `R0FS.Prefix` containing the opening rounds. `openingViewZ_some_structure`
(227 onward) is the converse shape theorem. `openingViewZ` itself parses the
25 semantic rows, two circle rows, and opening tail (180–192). Thus the
semantic payload view can feed this old parser without reproving its layout;
the required C2 base and circle predicates remain explicit.

For accepted old masked verification, [`R0P/MaskD3Glue.lean`](../../v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean),
`accepted_no_hit_extractedZ` (17–27) assumes `decisionZ = true`, no
`sourceDataWithFallbackZ` hit, and the first opening challenge nonzero for
every successful opening view; it returns an existential
`InputNoteExtracted` trace. `decisionZ` (in `MaskView.lean`, around 376)
requires the old opening view, parsed semantic challenges/polynomials/claim,
all masked sumcheck checks, the R0FS terminal decision, and `cardOK`. This is
not an acceptance theorem for the unified message type or its committed
protocol.

`R1SemanticPrefix.large_matching_extracts_of_prefix` in
[`SemanticPrefix.lean`](../lean/SemanticPrefix.lean) (69–145) is the current
bridge from parsed old semantic rows to a spend candidate. Its explicit inputs
include typed context and `rowEquiv` transport, public typing, typed candidate
words, parsed 25-row challenges/claim/polynomials/C2 words, degree bounds,
candidate semantic-prefix exclusions, `MatchingSupport.Good`,
`AcceptedPairing`, at least 9558 matching positions, and accepted sumcheck
checks. It returns a candidate with `ProductionHolds`, `CopyLinkBalance`, and
`InputNoteExtracted`. `outsideBad_of_prefix` (32–67) reuses the older
`MaskEarly` exclusions for that candidate. This theorem starts after the
old-row parsers and the opening/terminal facts have already been supplied.

The terminal composition is also available. `SpendSemantics.of_production`
([`SpendSemantics.lean`](../lean/SpendSemantics.lean), lines 28–48) derives
bounded values, input-note extraction, change commitment, and recipient or
withdrawal facts from `ProductionHolds ∧ CopyLinkBalance`. Then
`SpendRelationExtraction.of_production`
([`SpendRelationExtraction.lean`](../lean/SpendRelationExtraction.lean),
16–47) constructs an explicit `SpendRelation.Witness` satisfying `Rspend`,
provided `PublicOptionShape.canonical` and the production/copy-link premises.
`SpendRelation.check_eq_true_iff` in
[`SpendRelation.lean`](../lean/SpendRelation.lean), 84–89, identifies its
decidable checker with that relation. This is a production-witness bridge,
not a protocol acceptance or Rust-refinement theorem.

## C2 callback and current unified schedule

[`RecoveredC2Semantic.lean`](../lean/RecoveredC2Semantic.lean) defines
`pair eK c2Packed` (27–30), `pair_c2Words` (44–54), and the trace-backed
`pairAt` callback (69–71). `pairAt_fst_of_decode` and
`pairAt_snd_of_decode` (73–87) identify one opened leaf's two coordinates.
[`CanonicalC2SemanticOpening.lean`](../lean/CanonicalC2SemanticOpening.lean),
`c2_pair_at_of_no_events` (27–74), lifts an accepted canonical C2 Merkle
opening to those coordinates under full-trace consistency, commitment read,
opening-read inclusion, query bound, and exclusions for collision, child
target, and root target. It is per queried leaf and does not establish an
unconditional equality between a payload callback and all words.

The current unified model has separate representation facts:
`UnifiedSemanticActualView.actual_output` gives a semantic-row transcript
view for rows `1..25`; `UnifiedOpeningView.actual_output` gives the ordinary
view for rows `27..30`; and `UnifiedSemanticRecovery.typed_before_row` parses
records before a row under explicit trace/read conditions. The corresponding
`UnifiedSemanticCase.decodes_and_follows` and
`UnifiedOpeningCase.decodes_and_follows` establish decoder-follow behavior
for the actual experiment. These modules use generic `Message M`, while
`SemanticPayloadView` uses row-indexed `SemanticRecordCodec.RowPayload` and
the old `SemMsgZ` constructors. No theorem currently connects the raw
`UnifiedRecords.records` or a generic `Message M` to `RowPayload` and then to
the old `openingViewZ` input. The current schedule's row numbering is the
design's unshifted map: semantic rows 0–24, circle rows 25–26, opening
challenges rows 27–30, query row 31, rho row 32.

## Smallest reusable adapter to propose

The next model-only lemma should package the existing semantic parser facts
with the existing `openingViewZ_of_parsed` call. Its inputs should be exactly:

- a typed `R0P.TypedContext E Sfield`;
- `payloads : (row : Fin 25) → SemanticRecordCodec.RowPayload row`;
- `challenges : Fin 25 → E` and an explicit
  `recoverC2 : State → InitialWord E × InitialWord E` callback;
- `c2Base Sfield (recoverC2 (rootAt2 payloads)).1
  (recoverC2 (rootAt2 payloads)).2`;
- the two circle messages and points, with distinct/non-rational point
  premises;
- an opening-message list in `List (R0FS.Msg E × R0FS.Chal E)`.

Proposed output:

```lean
MaskView.openingViewZ
  ⟨x, SemanticPayloadView.rounds recoverC2 payloads challenges ++
    ((Msg.beforeZ0 y, Chal.circle z0) ::
     (Msg.beforeZ1 y0, Chal.circle z1) :: MaskView.openingPairsZ opening)⟩
  = some ⟨openingStmt x (recoverC2 (rootAt2 payloads)).1
      (recoverC2 (rootAt2 payloads)).2
      hb (fun j => (List.ofFn challenges)[15 + j.val]'(by omega))
      y z0 z1 hne h0 h1, opening⟩
```

The exact proof route is only `SemanticPayloadView.rounds_length`,
`semChalsZ_rounds`, `c2OfZ_rounds`, and
`R0P.MaskView.openingViewZ_of_parsed`. A named wrapper adds useful API
packaging, but no mathematical step beyond those existing facts. It exposes
the exact object that the old verifier consumes; it does **not** prove the
payloads/callback/challenges came from unified verification, that the old
terminal checks follow from current acceptance, or that the output witness
has `Rspend`.

The next boundary after that view is still explicit. To use
`MaskD3Glue.accepted_no_hit_extractedZ`, a separate adapter must provide
`decisionZ = true`, no-hit for the old source classifier, and its `hfirst`
condition from the idealized protocol's opening acceptance. To reach the
existing candidate extraction, it must instead or additionally supply the
`SemanticPrefix.large_matching_extracts_of_prefix` inputs listed above. Only
that extraction result composes into the J1 witness through production facts
and `PublicOptionShape.canonical`. Neither route currently derives the needed
old-view premises from current source bytes or unified acceptance.

## Source pins

Hashes below pin the files inspected in this inventory; they are not claims
that every statement is tracked in the same source revision.

| File | SHA-256 |
|---|---|
| `design/LEAD-DECISIONS-20261015.md` | `46a6502de8deafae774a62a589c91dcfbe0791e186e8db36651078b80c81c8e4` |
| `design/CLASSIFIER.txt` | `1ac2a44bb779d19d456e22c5c228c73c573a5e602bb50184aa3f742134489392` |
| `design/TERMINAL-D3.txt` | `2adda8b83244ecb13bf90ae1b232dc1049aa632ed62bc52a55aec72583a8d2ff` |
| `lean/SemanticPayloadView.lean` | `63d8ee366a6ca1beb5c4de26110419ddcaf83f87efb8de9d3151e24c0ef6506b` |
| `lean/SemanticRecordCodec.lean` | `5cf8fb6510c397d5d3c505b72bc24a5b2f4079ccb5a9e74e0c2eed14229bcbd3` |
| `lean/RecoveredC2Semantic.lean` | `62ed647c1a6a8ec667b77d59f7ce5f0ed82afa26c5dbc0a49f35210759328fa0` |
| `lean/CanonicalC2SemanticOpening.lean` | `1edd0299dc9914dd2e862441ab0ad744f5ce6734623c70e8e88732550be11fac` |
| `lean/SemanticPrefix.lean` | `a0e75d2bddea2f3d72b7102b29b099e3f552dd50114b255843685c75e8f23245` |
| `lean/SpendRelation.lean` | `ef80726d48b31e834a1fe040e304b1efe40eabf4681acbcae3cf36154765a9ae` |
| `lean/SpendSemantics.lean` | `a81f79a0401980cf22b448988eb1ddf0a2d5ae571d38bb85fc45908919a7774d` |
| `lean/SpendRelationExtraction.lean` | `02125315e3db3fad9a05b63f69a8e9ab41e1fadc220d3716ec5df9de9854acd2` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean` | `f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab` |
| `v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |

Worktree base observed during inspection: `57edab99fe104f23b3d3c881d1e87c1abb0975c0`.
