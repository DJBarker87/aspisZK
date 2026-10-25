# Conditional continuation plan — no adoption

Proceed only after the inhabited same-native-pair complete-verifier gate in
F3_JOIN-GATE.md. Sizes below are engineering estimates of small new modules,
not measured proof counts, worker commitments or security results.

| Area | Reuse as mathematical infrastructure/template | Exact new obligations | Size |
|---|---|---|---:|
| Decision / byte carrier | Frozen2 batch/finish, arbitrary-public checkpoint serializer and writeResume laws | F3 counterparts of acceptance_eq, accepted_details, accepted_trace, admitted; source semantic-Input and checkpoint body identity | 2–3 model modules, plus source joins below |
| Annotated carrier | StoredExperimentC4 original_eval, verifier_enrich, compiled_eval, recorded_eval, stored_and_public_and_acceptance, first_reads; StoredProjectionC4 project_eval/original_view/recorded_view/frame_eq | Rebuild for Input carrying BOTH P and U; enrichment/canonicalization preserve P, U, S and exact sampler; second-pass log duplicates first; no extra first reads | 2–3 |
| Q+34 charged prefix | Frozen2StartChargePrefix charged_eval, prover_eval, fibre_prover, same_transcript, chronological_prefix, first_start_before_terminal, starts, transcript_start_read, transcript_start_prover_or_followed, recovered_eval; Completion decodes/chains_read/prefix_chain_read/protocol_rounds/hit_in_prefix | Instantiate new F3 prover projection/charged experiment; prove actual sampler is prefix, preserve first-read indices, bound starts by Q+34; reprove checkpoint no_new_start and clean accepted facts for P-address cross-reads | 2–3 |
| Q+1161 distinct reads / Q+2322 issued log | Frozen2Bounds distinct_bound/log_length; StoredAccountingC4 distinct_bound; StoredExperimentC4 recorded_length/first_reads | F3_Counts already checks all-input terminal<=1046 and verifier<=1161, and SINGLE-PASS prover+verifier firstReads<=Q+1161. Reprove F3 ANNOTATED distinct_bound and log_length, then Frozen2Probability first_reads/log_length/mass_projection on F3 | 1–2 |
| Failure bound | Frozen2StartChargeProbability hit_mass/restricted_union_bound/failure_bound; Frozen2StartChargeClean accepted_facts/clean | Rebuild on F3's exact memoized experiment with F3 charged-prefix and distinct bounds; classify physical P and checksum address coincidences with arbitrary prior queries. Constants alone do not give probability equality | 1–2 |
| Recovered inputs | OraclePortFrozen2Transport accepted_original_eq/accepted_built_words_eq/accepted_recovered_inputs/accepted_extractor_eq; generic OraclePortRefineJoin.RecoveredInputAgreement and extractor_eq_of_recovered_inputs | Prove SAME decoded public, 29 initial words and folded final word from SAME first-read cuts on native/F3 logs; build annotated accepted-run equality; then apply generic extractor equality for every coin tape | 1–2 after join |
| Cost and runtime | ActualCostedExtractorM10 value, RawExtractorCostComposedBin.accepted_attempt_cost, ClosedAllocationLedgerM10.ledger, CostedAllocationLedgerM10.params, returned_relation | F3 counterpart of Frozen2Headline.Claims/final_soundness cost component using actual F3 annotated log<=Q+2322 and ledger parameter Q+1161; rebuild StoredCarrierBinding and runtime_transport before any deployed statement | 1–2 |

Model/probability/extractor continuation: approximately 10–17 focused modules,
with overlaps between rows. No inherited theorem is attributed to the F3
experiment solely because names or constants match.

Independent source-join gate, approximately 6–10 focused modules before broad
rollout: (1) same-cut semantic serializer and literal row construction (1–2),
(2) all115 sampler entries including eight pairs/rho state (1–2), (3) batch0
same-q ordered log and ten-step state (1–2), (4) exact saved body and resumed
state through retained history/P2Prime (1–2), (5) batch1/finish and complete
native-pair composition (1–2). These estimates exclude child-cone repairs,
source-to-ELF mapping, arbitrary rejected runtime prefixes and full runtime
admission. Do not touch other workers' prefixes to obtain them.

## Checked counts and limits

F3_Checkpoint.schedule proves precisely six issued checkpoint reads with
repeated S/P/checksum inputs. F3_CountInvariant.complete_count proves exact
ALL-INPUT complete-verifier log-length equality with frozen2 at fixed semantic
public/proof/stored bytes and arbitrary physical P, including rejection.
F3_Counts proves the actual 1046/1161 envelopes using existing477/563 batch
bounds. Thus replacing U by P adds zero issued calls in this model; this is
checked, not an architectural expectation. It does not prove equal log
addresses or equal numbers of distinct cells between F3 and frozen2.

The source-inventory formula187+N0+N1 and the exact115 valid-row count are not
new native-source count theorems here. Exact model count equality transfers
any independently established frozen2 count premise; it does not supply the
missing native alignment premise. Q+34 and the F3 annotated Q+1161/2322 bounds
remain continuation obligations. There is no universal fixed parent count.
