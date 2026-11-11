# Destination / pool / deployment-domain binding at the PIN2 pin: headline check (2026-11-11)

This was a read-only source reading. Nothing was compiled.
- Worktree: fix/pin2-lean-20261110 @ c8b641cae0e. Rust pin: c7593d23fdc.
- `git diff 271869c946d c7593d23fdc` is empty for pair_forest_semantic_terminal.rs and payment_relation.rs. 271869c946d is the W1 source of the PIN2_NEWGATE_r0 emission.
- Headline source: the l187 copy in scratchpad, l187src/src/TAS_FinalB.lean, sha256 ed99757c…. Its statements were not changed by PIN2.
- E = docs/research/100bit-spend-path-20261013/evidence

## (a) The headline statements and their public object

**TAS_FinalB.lean:94-113, `deployed_splitB`.** Conclusion, for `c := ctxB (NNH8_Exec.exec L0 copy std) fx w H`:

    S_host.Bound c (model1 c) (model2 c) ∧ NNH8_Split.rest L0 copy c (model1 c) (model2 c) ∧
    ((NNH8_HeadlineB.headlineB L0 borrow copy std).OutcomeRec c (model1 c) (model2 c) ∨
     (NNH8_Exec.exec L0 copy std).ERec fx H)

**TAS_FinalB.lean:153, `deployed_charge`.** For every H:

    max 0 (ind (Runs … ∧ ¬ headlineB.OutcomeRec c …)) ≤ ind (BinRawByteCollisionTargets.event … (eval H fixedProgram))

It also bounds `lazyMean … ≤ F3T_Numeric.total (Q0+Q1)` and `failureModel runtime ≤ total`. The full elaborated text is in E/pin2-public-binding-20261110/impact-scan/Top.out.

**Unfolding.**
1. `headlineB.OutcomeRec := outcomeRec` (NNH8_Exec.lean:336-337) unfolds to `FJv_DResult.Outcome … ((recSig …).EventRec ctx)` (NNH8_Exec.lean:293-333).
2. `FJv_DResult.Outcome` (RPx_FJv_DBoundCaller.lean:111-151) is existential over `f : FirstCut` and `s : SecondCut`, a TX1 run and a TX2 witness. It contains:
   - `run : Tx1Q_Execution.Run … (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved` (l.125-127)
   - `PoolV1PairForestTerminalStatementV1.semantic_public f.statement = ok f.semantic` (l.135-136)
   - `P2P_Acceptance.Facts … f.pub …`, whose `i.statement.pubBytes = bytesOf pub.val ∧ … pubBytes.length = 1880` is at RPz7_P2P_Acceptance.lean:13-14
   - `bad ∨ (… FJv_DBoundCaller.Outcome …)` (l.147-151)
3. Further down:
   - FJv_DLiteral.Outcome (RPx_FJv_DLiteral.lean:56-62) has `model.physical.bytes = bytesOf f.pub.val` and `input parsed q tr = some i`.
   - FJv_DFinish.Outcome (RPv_FJv_DFinish.lean:47-52) ends in `Collision … ∨ (finish_relation … = OraclePortFrozen2.finish … i … ∧ … D0TypedChecks.verify … i = true)`.
   - `i : SourceInputs` has `decoded : R0P.Public SemanticPublicWire.M31` (R1FinalSoundness.lean:141-142).

**Where the three values appear.** They appear as fields and as bytes, never as a constrained conjunct:
- **Field of the Rust carrier.** `f.semantic : AdapterRw.LeadInputs.Public = AdapterRw…r0.Public` (S2W_NativeConsolidation.lean:20; AdapterRwLeadInputs.lean:13). Its `Withdrawal` arm carries `PoolV1WithdrawalPublicV1.{pool, deployment_domain, destination_token_account}`. These fields existed before PIN2. `toPublic` copies them: RPz7_S6CurrentVerifierCarrierV1.lean:95-121.
- **Bytes.** `f.pub` is the 1880-byte uploaded statement account. The payment statement sits at offset 1880-216 (E/pin2-w4-20261111/PIN2W4_inputs.py:31,40).
- **Field of the model public, PIN2 only.**
  - `R0P.Public` gained `pool`, `deploymentDomain` and `destination : Option (List (Fin 256))` (E/pin2-public-binding-20261110/sources/R0P/Core.lean:70-76).
  - The docstring at l.55-57 says: "the three binding fields … mirror the bytes appended to `r0::Public::public_bytes`; **no residual family reads them**".
  - The impact scan (Top.out) confirms that both headline statements reach `R0P.Public` and `SemanticPublicWire.parsePublic`/`toPublic`/`Wire.withdrawal` by unfolding definitions. So the unchanged headline text now refers to the PIN2 model public.

**Result for (a).** The spend relation never reads destination, pool or domain. `Family.Holds` is the R0P residual families, and W11 records that `R0P.digestKeys/Row/Start/Target/publicDigestLanes` read none of the three (PIN2-W11-REPORT.md:156-157). The values are public inputs bound by transcript absorption only. This is the approved absorb-only design.

## (b) How the PIN2 fields reach that public object

1. **Serializer.** PIN2_NEWGATE_r0.lean:688-778 (overlay-PIN2) shows `public_bytes` calling `semantic self`. After `next_frontier` it appends `p.pool`, `p.deployment_domain`, a has-destination byte and, if present, `destination`. `withdrawal_public` sets `destination := some «public».destination_token_account`; `private_public` sets `none` (l.245-289).
2. **W3c bridges.**
   - `PIN2Whole.source_success` (E/pin2-w3c-20261111/sources/PIN2_PublicSerializerWhole.lean:68-79): success fixes all bytes and canonicality.
   - `RawBridge431.project` copies `pool`, `deploymentDomain` and the withdrawal `rawBytes32 p.destination_token_account` (PublicExtractedRawBridge431.lean:49-71). `source_success_raw` gives `PublicRawCore.serialize (project p) = some (out.val.map rawByte)` (l.185-198).
   - WithdrawalCarrier431 copies all nine fields (WithdrawalCarrierBridge431.lean:24-66). Its own docstring says: "its caller/account binding remains a separate question".
   - `PreparationBinding.toPIN2` is a field copy that keeps destination (ExtractedPublicPreparationBinding.lean:88-121).
3. **W9, F3T_ByteCarrier.semantic.** This is a definition change. The model's semantic transcript input is now `PIN2 public_bytes (toPIN2 (toRetainedPublic (toPublic v)))` of the decoded statement (E/pin2-w7-20261111/sources/RPz7_F3T_ByteCarrier.lean:22-31; CHANGES.tsv row RPz7_F3T_ByteCarrier). All three fields therefore enter the transcript seed.
4. **Model parse.**
   - `parsePublic` reads pool, domain and destination through `decodeAfter` and rejects trailing bytes (R1SemanticPublicWire.lean:105-117, 147-150).
   - `PublicOptionShape.check` requires `destination.isSome` for a withdrawal and `none` for a transfer, with 32-byte lengths (PublicOptionShape.lean:28-40).
   - `SpendDataMap.mapPublic` copies the three fields (E/pin2-w3a-20261111/sources/R1SpendDataMap.lean:48-51).
5. **W11.**
   - `nativePIN2 q := {embed (native q) with destination := destination q}` (PIN2W11_PublicCopy.lean:22-28).
   - `FIw_PublicModel.ofPublic` copies `pool`, `deploymentDomain` and `destination` into `R0P.Public` (E/pin2-w3c-20261111/sources/RPv_FIw_PublicModel.lean:29-32).
   - The terminal chain is stated on `nativePIN2`. `FJt_PublicJoin.value` concludes `mapPublic embed (ofPublic (nativePIN2 pub)) = …` against `parsePublic literal.pubBytes = some literalPub` (RPv_FJt_PublicJoin.lean:33-35).
   - `FJt_Endpoint.value` takes this as its premise `publicSame` and concludes only the terminal-value equation `(polys 9).eval … = R3SemanticRemainingJoins.terminal literalPub v data` (RPx_FJt_Endpoint.lean:33-38). The terminal reads none of the binding fields.
   - Provenance caveat (W11 report): `nativePIN2` is a named value. No extraction of the PIN2 `SemanticPublic` constructor exists (probe-crate struct only, HM-D at best).
6. **Pool-side consumer.** The headline does not reach it.
   - The only program the headline executes is `CPH_Program.verifier`, through TX1 and TX2.
   - The Pool settlement models are not among the constants reached by the headline. These are NGP_L159 (marked "Specification only … realization is an OPEN producer obligation", NGP_L159.lean:4-5), NGK_NFO_ReadModel, NGK_NFR_CSettlement and NIB_ReadToSettlement. The count is 0 in scratchpad reach_split.txt, which is the pre-PIN2 release reach list.
   - Only `R9PoolRuntimeBinding.Inputs{pub,proof}` and `digestMatches` occur. These are verifier-side.

| Field | In public_bytes / transcript at PIN2 | Field of headline public object | Constrained by relation | Ties headline to the Pool's paid account |
|---|---|---|---|---|
| destination | yes (steps 1-4) | yes: f.semantic (Rust); i.decoded / literalPub (R0P, PIN2) | no (absorb-only) | no |
| pool | yes | yes | no | no |
| deployment domain | yes | yes | no | no |

**What the Lean statement says, and what it does not.** An accepted run's model outcome names the transcript-bound destination of the uploaded statement. The Lean statement does not say that the Pool pays that account.

**What ties the payment to the proof.** The Pool's payment of `statement.destination` is tied to the proof only outside Lean:
- The TX1 checkpoint stores `hash.digest(&[public])` (crates/aspis-r1-cost-probe/src/verifier.rs:329 at c7593d23fdc).
- TX2 `resume` rejects unless `bytes[48..80] == hash.digest(&[public])` (verifier.rs:396).
- The Pool then reads the same statement account (Pool b936275, unchanged; that is the earlier reading and was not re-read here).

## (c) Status

**Verifier side: restated at the model level but not closed.**
- The transcript binding of the three fields is stated through W3a-W11, all on local compiles against host objects.
- PIN2-W11-REPORT.md "What remains provisional" lists:
  - no coherent replay;
  - about 1,060 upstream modules not rebuilt, including RPx_Deployed, RPx_FJv_D* and the COMBINED_IMPORT modules;
  - the two top theorems not yet built on the host;
  - no final axioms audit;
  - nativePIN2 provenance.
- So TAS_FinalB.deployed_splitB and TAS_FinalB.deployed_charge are not yet re-established at PIN2.

**Pool payment of destination, pool and domain: an open gate.** It is outside the headline. This is L159 (Pool in the game or conditional), a pending owner decision. It is spec-only in NGP_L159.

**Making destination a conjunct of the headline relation.** These conclusions would have to change:
- `AspisR1.FJv_DResult.Outcome`, through `NNH8_Exec.outcomeRec`, so `NNH8_HeadlineB.headlineB.OutcomeRec`. It would need a conjunct equating `i.decoded.destination` (or `f.semantic`'s `destination_token_account`) with the Pool-paid token account of the settled TX.
- Therefore `TAS_FinalB.deployed_splitB` (its OutcomeRec disjunct) and `TAS_FinalB.deployed_charge` (its `¬OutcomeRec` event).
- `RSL.EVB.top_splitB_full`, so that the run includes the Pool settlement transaction.
- On the Pool side, a realized `NGP_L159.L159_statement` (with `poolRead`) linking the Pool's read of the statement to the same `f.pub`.
- Internally, `FJt_Endpoint.value` would have to export `literalPub.destination = destination (pub)`, which today is only its `publicSame` premise. Or `FJv_DFinish.Outcome` would have to carry that equality.

None of these were changed by PIN2.

target not yet established
