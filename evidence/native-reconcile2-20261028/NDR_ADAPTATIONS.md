# Observer reconciliation

NDR_L001 validates the first adaptation with standard axioms only (3.800 s,
3,841,008 KiB RSS, swap 0). No cryptographic or adaptive execution premise is
discharged.

## NDO_JGi_FinishFields.source

Before: `(obs : Option (verifier.Phase → Result Unit))`, with premise
`FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)`.
After: `(obs : Option (RPz7_PhaseIso.Phase → Result Unit))`, with the identical
premise and conclusion. `NDO_PhaseIdentity.retainedCarrier` identifies this
carrier with the historical FirstCaller.Phase; the imported producer's nominal
verifier.Phase is distinct. All other quantifiers and proof bytes are unchanged.
This restores the historical quantification; it does not transport an execution
from the producer carrier. New direct import: NDO_PhaseIdentity.

The remaining adaptations and the 23 upstream differences are tracked below
as validation advances. Non-None producer observers require a proved execution
transport at producer/model comparison boundaries; callback round trips alone
are not that transport. No such new adaptive execution result is claimed.

## The 23 upstream body differences

These selected replay modules are reused unchanged, rather than copied or patched.
The carrier change is `verifier.Phase` (historical alias) → `RPz7_PhaseIso.Phase`
(retained FirstCaller carrier), except the two special cases stated below.
No theorem conclusion or non-observer quantifier is deliberately changed.

- `AuS1_Semantic3` → `RPz7_AuS1_Semantic3`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `ClaimsUnrolledFinish` → `RPz7_ClaimsUnrolledFinish`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3U_VerifyHead` → `RPz8_F3U_VerifyHead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3V_SemanticFinish` → `RPz7_F3V_SemanticFinish`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `F3V_SemanticVerify` → `RPz7_F3V_SemanticVerify`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `FIr_FinishComparison` → `RPx_FIr_FinishComparison`: FinishModel calls/proof applications change `obs` → `RPz7_PhaseIso.observerToFirst obs`. A callback map is explicit; this is not a new adaptive execution proof.
- `GExp_FinishAssociation` → `RPz7_GExp_FinishAssociation`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `GExp_VerifyAssociation` → `RPz7_GExp_VerifyAssociation`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `RawJ_VerifyRead` → `RPz8_RawJ_VerifyRead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `RawK_VerifyHead` → `RPz8_RawK_VerifyHead`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1AcceptedChallengesNumericV1` → `RPz7_S1AcceptedChallengesNumericV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1AcceptedSemanticNumericV1` → `RPz7_S1AcceptedSemanticNumericV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticBudgetV1` → `RPz7_S1SemanticBudgetV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeFinishExactV1` → `RPz7_S1SemanticCodeFinishExactV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeFinishV1` → `RPz7_S1SemanticCodeFinishV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeVerifyExactV1` → `RPz7_S1SemanticCodeVerifyExactV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticCodeVerifyV1` → `RPz7_S1SemanticCodeVerifyV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishBoundsV1` → `RPz7_S1SemanticFinishBoundsV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishModelV1` → `RPz7_S1SemanticFinishModelV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticFinishRootsV1` → `RPz7_S1SemanticFinishRootsV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticPhaseV1` → `RPz7_S1SemanticPhaseV1`: Historical alias `verifier.Phase := FirstCaller.Phase` moves to retained `RPz7_PhaseIso.Phase`; no producer carrier equality.
- `S1SemanticPrefixModelV1` → `RPz7_S1SemanticPrefixModelV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.
- `S1SemanticVerifyReachabilityV1` → `RPz7_S1SemanticVerifyReachabilityV1`: Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.

## NDO_JGi_ClaimArrays.source and NDO_JHm_SemanticOperands.source

Both theorem statements remain byte-identical. In each proof's application of
JGi_FinishFields.source, the inferred/explicit `none` observer becomes
`RPz7_PhaseIso.observerToFirst none`; the existing finish premise is supplied by
`by simpa only [NDO_PhaseIdentity.noneToFirst] using finish` (respectively
`finished`). This is the release None specialization, without a producer
execution transport assumption. These edits await dependency-ordered compilation.

NDO_JHk_QueryPowerStep's observer remains the emitted producer carrier: its
query-values theorem calls the producer API directly. NDO_JGy_QueryFrontier and
NDO_JHc_WriterContinuation use producer marks and None directly; no semantic
FinishModel boundary occurs there and their statements/bodies remain unchanged.
