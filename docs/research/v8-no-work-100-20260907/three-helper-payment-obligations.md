# Dense three-helper tuple to the same-table payment endpoint

Source-only audit at `2a49280b70f17a4539927d7c6fd3121c417f2d7e`.
No compiler, arithmetic gate, remote mutation or changes to existing leaves.

## Conclusion and support boundary

`ThreeHelperClaimCover.quotient_cover_dichotomy` composes with
`SelectedEarlyC1Amounts` and `SelectedEarlyC1Outputs` only as a conditional
deterministic semantic endpoint. It supplies no semantic/copy residuals.

One premise is genuinely derivable in this branch: the theorem already
assumes `earlyC1 c1 = some p`. `EarlyC1Support.some_early_has_support` gives
at least 245,609 complete C1 componentwise matching fibres. Their four-slot
injective embedding supplies at least 982,436 `c1JointAgreementSet` symbols,
hence the 38,228-symbol condition of `EarlyC1Family.mem_family`. The finite
embedding/cardinality proof is the same shape as `OwnFibreGeometry.common_card`;
a named `early_found_mem_family` adapter is not yet present. This is a small
composition, not a remaining own-support assumption for this found branch.
Base-valued received C1 then yields the exact semantic table through
`member_is_base` and `semanticTable_embeds`.

Dense P satisfies `c1Projection P = p`. It is fixed after C2 but before all
subsequently supplied OOD data, gamma, Q and claims. Coverage requires
image-valid Q with at most `4*15334 = 61336` bad quotient fibres (at least
200,808 matching fibres), not just the 9,558-fibre literal-family threshold.
Reconstruction retains up to two pole fibres. The fewer-than-three good
gamma branch and the early-C1 `none` branch remain separate. No equally
large full 29-component support is asserted; helpers are not fixed before C2.

Countercheck: exact encoded zero C1 and zero C2 have maximal agreement. A
checked zero-answer chord has zero interpolant, so Q=0 is image-valid and
exactly close and the dense tuple is zero. Its zero amounts fail the strict
transfer checks. Thus maximal geometric agreement cannot supply semantics.
This is symbolic reasoning, not a new executable/exhaustive experiment.

## Exact obligations

Lean paths are under `experiments/`. Every row below must use the same
`t := SelectedEarlyC1Amounts.semanticTable p` and constructed canonical
`raw := SelectedEarlyC1Outputs.rawSemanticTable p`.

| Stage | Strongest existing endpoint | Still required |
| --- | --- | --- |
| Copy | `EarlyC1CopyCollision.source_member_covered` | Family membership as above; bound transfer/append context; `CopyConditions`: all local row residuals, total helper sum zero, inactive helper sum zero and all four active-row denominator guards, including empty/zero-weight slots. Conclusion is aliases OR the existing lambda/chi collision. Dense helpers alone establish none of these. |
| Amounts/output openings | `SelectedEarlyC1Amounts.member_amounts_or_copy_collision`; `SelectedEarlyC1Outputs.member_outputs_or_copy_collision` | Amount bits/recomposition, six auxiliary zeros, rows1014/1015 balances and literal positive-pack check; six output sponge blocks with initial/tail constraints; asset bindings at460/508 and public commitments at475/523. Copy aliases and canonical raw decoding are derived already. Reuse the same collision branch once. |
| Input owner/note/nullifier | `SelectedNoteRecovery.decoded_hash_endpoint`; `exact_public_asset_nullifier` | `NoteResiduals`: paired gates for blocks0,1,2,3,25,26; initial rows0/16/400; note/nullifier carries; owner/key/split-salt aliases; six row60 tail zeros. Bind asset44:1 and public nullifier row427. No honest trace or valid-witness premise. |
| Exact pair/membership | `SelectedMembershipDecode.same_decoded_note_nullifier_and_anchor`, PLUS `same_raw_input_pair_checked` and `decoded_lane_index_contract` | `PathResiduals`: 24 bits, gated selected children, current/left/right aliases, initial low zeros and pair gates. `InputPairResiduals`: row1017 occupancy/inverse/empty/selected-spend checks and actual digest/side aliases. Bind outer root row907. This yields the same 1+20+3 split and index below2^20. The note/nullifier/anchor theorem alone is not pair-parser success. |
| Output pair | `SelectedOutputPair.decoded_outputs_feed_checked_pair` | Row1018 occupied=1/inverse, change/recipient/right aliases, block33 low zeros/gates. Derives nonzero change limb7, field-stage `two_outputs` success and ordered row539 pair hash; output openings alone do not imply the sentinel. |
| Afterstate | `SelectedAppendAfterstate.public_output_pair_afterstate` | Same output pair; `AppendResiduals` for blocks34–53 with exact gated current copies and complementary empty/frontier bindings; `AfterstateChecks` integer sequence/index/increment, static frontier, dynamic carry and row859 root. Independent snapshot/commitments remain inputs. It proves computed components, not the actual returned Rust record. |
| Checked caller/settlement | `recovered_witness.rs:extract_checked` is executable, not a universal Lean theorem | Authenticated nonzero pool/deployment IDs, legal sequence, canonical public fields; entire runtime equality including OUTER root before lane substitution; unspent nullifier; snapshot identity and valid old tree state; literal field/Poseidon/parser/compiler/record refinement and `compiled.public_statement = transition`. |

Old-state validation is substantive: `incremental_merkle.rs` requires
zero-bit frontier entries equal pinned empty roots and the explicit root
equal the empty root at index0 or the reconstructed non-full root otherwise.
The selected semantic terminal does not rehash/authenticate this old state.
The remaining append adapter is its dense20-slot frontier/bit recurrence to
V7 `IncrementalMerkleV1.appendCarry_reconstruct_more/full`, including terminal
carry and recursive empty roots. Account/root-history authority and atomic
settlement/nullifier writes are separate program invariants.

V7 `V7RestoredSemanticWitness.accepted_restored_trace_implies_decoded_witness_valid`
is the strongest older full-looking theorem, but concerns old Tag73 and
assumes faithful hashes, coherent decoder extraction, exact point/inactive/
terminal interfaces and excluded fixed-family failures. It is not a selected
pair-forest acceptance theorem. Reuse its proof decomposition, not its old
registry/profile or successful-extraction assumptions.

## Smallest substantive next bridge

Add `SelectedEarlyC1Inputs`: derive the following 72 actual scalar aliases
from `WeightedAliases (memberTable p) .transfer appendIndex`, using the exact
current registry. All seven links have constant weight one.

| Links | Literal aliases | `NoteResiduals` fields |
| --- | --- | --- |
| 0,1,2 | rows27→32,43→48,411→416, all16 columns | Three full-state carries |
| 7,8 | rows11→28 and12→412, columns0–7 | Owner and nullifier-key copies |
| 9,10 | row44 columns2–7→row428 columns0–5; row60 columns0–1→row428 columns6–7 | Split-salt copies |

Only non-copy block/initial/tail residuals then remain to construct
`NoteResiduals` and invoke `decoded_hash_endpoint` for the exact same decoded
key, amount and salt. Public bindings give the actual public nullifier.
This removes real caller-supplied equalities; wrapping all residual predicates
into an assumed payment-valid predicate would not advance extraction.

Upstream, dense P fixes the component-error polynomial before gamma, but
wrong claims still have full degree28 (`ClaimTransport`), not degree2.
Causal relation/semantic enforcement, actual helper linkage and local/helper
boundary premises remain open. No probability, acceptance, efficient
extraction or FS claim is made by this audit.

Inspected hashes: `ThreeHelperClaimCover.lean`
`0449aedbb283b715340d8d99d5d5d0669cdc08b4f8c7789fe1a9943eb3a9c3c2`;
`SelectedEarlyC1Outputs.lean`
`6da1be45f88967fa924d2fbd523193b6791610407b0c4b2149c6ce0b724f36ae`;
`recovered_witness.rs`
`56760c46ed56ace2756949efabc09f1a2b8880087c1b4dbb7da394a1cc54132f`.
V7 reuse stays pinned to `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
