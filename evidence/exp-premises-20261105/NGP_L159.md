# L159: checkpoint, byte carriers and Pool consumer

`NGP_L159.lean` defines exact propositions, not certificates. `Cuts` is a
law-free snapshot record; giving it arbitrary values earns nothing. A producer
must construct all its fields from ONE execution and the SAME external inputs.
`History_statement` and `Carrier_statement` separate cross-transaction data
retention from the byte and emitted-result associations. `L159_statement`
retains History AND (Carrier OR the existing charged collision event).

The collision view argument MUST be the actual evaluation, in the same H, of:

```
Hiq_RecordedJoint.program
  (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)
  ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
```

where cfg is FIp_Install.configuration indexError
(IDa_Deployed.deployedConfiguration missing indexError reservation) reservation,
and Q=Q0+Q1. The fixed event is BinRawByteCollisionTargets.event
SelectedTranscriptParams.params.iv (Q+2965), as in ARX_Join.accepted and the
headline's charged recorder. Passing an unrelated view is NOT this premise.
The definition is a per-run target; its universal physical realization and
admitted-support construction remain OPEN. The uncharged byte-equality form
would be stronger than frozen3 and is NOT proposed.

| Step | Exact carrier / identity | Law and status |
|---|---|---|
| Original caller bytes | proof1 is the 57607-byte verifier suffix of proof account [688,58295); public1 is physical ASF8 (1880), not ASQ8 request (320) | S scanner/codec packets CLOSED; enclosing native source cuts OPEN |
| TX1 writer | SAME CheckpointBytes5Writer.Prepared/Accumulator, NGC_KNE_Caller.WriterDomain; sourceProgram p a domain proof1 public1 = writer p a proof1 public1 | NGC_KNE_Writer.cohort_program_eq proved (116 emissions); NGP_WriterReuse.writer_model merely reuses it |
| Writer domain | S2 variant, weights length64, all22 queries <262144, canonical gamma/kappa/alpha/rho/semanticAlpha/coordinates/claim/rhs/power/weights, next10 | NGC_WriterDomain.from_query_loop / PrestateBridge use SAME returned states; NFW preparation/native initializers remain OPEN |
| Saved checkpoint | c.saved (Vec U8) length1768; p.copied t=c.saved; TX1 adapter account2 CP-only payload update | Local writer packet not TX1:186 closure; wrapper copy/Drop/reference-validity association still needed |
| Physical history | key=((p.layout t).handles 2).1 = ((p.layout u).handles 6).1; actual public-key equality CPS_PhysicalKey.key e1 2 = … e2 6 | Game b; global bank-key index and public key are distinct obligations, never numerical index alone |
| Parent / ordering | CPG_Projection.adjacent p t u; success p t=true; no intervening CP touch, source actions equal physical actions | Game a–d (CPH_Game), not attacker promise. CPH_Protection/Trace/Recorder derive source history given extraction/game |
| Next load | loaded p u key = some(bytesOf c.saved.val) | RuntimePersistence plus ordinary CP, nonzero final lamports, source protection. NGP_L159.persisted_bytes proves precisely this DATA-only step |
| Resume read | bytesOf checkpointRead = bytesOf saved; TX2 account6 in verifier admission | Actual borrowed range/account/length association, not hash equality; ordinary-account/non-system/nonsigner facts from native admission |
| Bound proof/public | bytesOf proof2=bytesOf proof1; bytesOf public2=bytesOf public1 | Carrier branch only, otherwise charged collision. Checkpoint digests alone do not imply bytes |
| Pool result read | poolRead.bytes = (S2K.ResultPayload.bytes emittedStatement).val; poolRead.value = S2K.ResultAdmission.value emittedStatement | RuntimeReturnData nonempty, same instruction context and selected program, no intervening CPI; NGK_NFR_PoolReturnData.association, decoded inverse and result encoder cuts proved |
| Settlement | SAME authenticated value validated, lane advanced, result reencoded | NGK_NFR_ModelJoin.same_emitted_settlement conditional checked/advanced hypotheses and NGK_NFR_CSettlement cuts; production Pool B/D OPEN |

Bank-lineage order is NOT strictly increasing slots: consecutive executions
can share a slot. CPG_Projection.Observations has NO slot/epoch fields.
`slot : S2W_ExtractionBoundary.Slot` is an explicit input of second;
RuntimePersistence covers neither Clock::get nor rentEpoch, owner, balance or
privileges. Registry activation/retirement at current_slot and lane epochs are
separate native predicates in Pool B, not inferred from data persistence or
an invented epoch monotonicity rule. Proof/public accounts are not protected
by game b; their identities require source checkpoint checks/collision analysis.

Consumed CLOSED packets: S7 roots, Q2 roots with ae domains, D helpers, KNE
writer local certificate, NGC finish/value/query-poststate domain laws;
NGK retargeted Pool A/C proofs. "A reclassified" retains std/allocator transport;
"C cuts" is not the production settlement caller. OPEN blockers: TX1:186,
prepare/Prepared producers and source prefix; Pool B complete prefix/account
admission; Pool D same-execution read/settlement association; final source/ELF
realization. No unsupported private reconstruction or ownership equality is
added. Pending runtime candidates are in NGP_CANDIDATE_ROWS.md; none assumed.
