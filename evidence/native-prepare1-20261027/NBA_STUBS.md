# NBA callee return abstractions and arithmetic pairings

No NBA gate proves a field multiplication in Kani. All return abstractions
below are universal over raw returned bit patterns, with no correctness assume.
They prove routing/control/value preservation, and must be instantiated using
the separately checked concrete callee theorem. A missing association stays OPEN.

| Native replacement | Return/domain | Concrete Lean pairing | Current credit |
|---|---|---|---|
| NBA_verifier::scalar | every raw E and next-state; input typed transcript, rows27..30, reached payloads | NBA_Scalars.gamma/ordinary derive canonicality; NBA_Transcript.block accounts for three linked oracle replies; NBA_SamplerValues pending totality | K004 prefix routing only; complete scalar association pending |
| NBA_verifier::queries | both Transcript rejection and arbitrary22 words/next-state | actual installed QueriesModel; native QueryScan step/driver/finish association in progress | no whole queries closure yet |
| NBA_verifier::scalar_k | every raw QM and next-state | actual installed scalar_k/fromQm; pairing in progress | route to powers gate pending |
| NBA_verifier::powers29 | every returned array's raw928 bits; asserts N=29 and actual gamma argument | NBA_PowersCallee.source (L012), canonical gamma; native powers/ClaimPowers full array and canonical result; inherited LPq/LPi one-step and induction | no multiplied value proved in Kani; native scratch transfer gate pending |
| NBA_verifier::claim | both Parse rejection and every raw E; exact semantic/y1/inactive/g/kappa routing | NBA_ClaimCallee.source (L002); NBA_ClaimTotal.construct (L010), CLOSED LPt producer-domain bridge | canonical domain and exact installed full Result proved; native caller cut pending |
| QueryScan step membership Bool | every Bool, no assume; arbitrary valid counter pre-state | Query31ExplicitScanBody.stdOps.contains, actual pure Std contains on SAME accepted prefix; existing TrustedStd boundary retained | native one-iteration gate pending |

NBA_Carriers.roundtrip/canonical (L009) identify all eight native/cohort words.
NBA_Inactive.bytes (L017) derives canonicality from SAME successful emitted
inactive decoding, without assuming canonical input words or decoded output.
LPo's CLOSED actual decoder supplies the native association at wide_view.

Inherited multiplication pairings, unchanged: LPh_STUBS.md and LPq_STUBS.md;
LPm_emul replacement pairs LPi_TowerValues.wide_mul on canonical inputs,
private Dot pairs LPm_PublicState.private_source/LPi_RawValues.source with
arbitrary u64 pre-state and canonical packed operands. No new field-op stub
is installed by this job. LPb passing-stage frozen replay is LPi_REUSE.md's
LPe_K001/K004-K007 mapping, not a new LPb run.
