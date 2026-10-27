# Batch 1 resume: source, ELF, fixture and audit gates passed

Branch `codex/pv-batch1-20261027`; runtime base `c57a344726745387efb38d1571d885c69ce829ee`; resumed head `a964ac5c61`. Applied runtime revision `ccf87ccecd8e0463a53bbedd0fc995837937dac9`. Target not yet established. No endpoint premise has been removed. `REPORT-INITIAL-STOP.md` preserves the original ELF-mismatch report; `RESUME.md` and `LIVE.md` are chronological checkpoints, not final status.

## Revised runtime diff and release gates

`weights.rs` is byte-identical to c57a344726 (SHA256 `ab55509e54218a2bfe7dd2d5e1b14216e3303961c16c181ce2e03d40f6b7678b`). Op254 lives in new `prover_powers.rs`, gated by `prover`; only prover.rs/sim.rs direct calls are redirected. Original calls inside shared weights.rs remain unchanged. `revised-applied.diff` contains the seven-file runtime diff. `MODULE-GATES.md` records every edited file and release dependency feature: prover_helper_sum, prover_powers, host_semantic and prover require prover; sim requires r1p-check (implies prover); ct_pole requires ct-host-prover, explicitly incompatible with program-build; lib adds only prover-gated modules. The default release program enables optimized-terminal/program-build, without these host features. No other shipped-code edit was made.

All three ELF rebuilds passed exact pinned SHA256 equality (`gate-a-resume.json`):

| ELF | SHA256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 0 | 41.435 | 686356 | 0 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 0 | 50.679 | 685640 | 0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 0 | 39.930 | 678204 | 0 |

All at ccf87ccecd; #print axioms N/A. Full targets, commands and environment are under candidate/build-*prover-local*/. Each ran alone under MemoryHigh6G/MemoryMax8G/swap0/Tasks64.

## Checked source statements

All inputs include arbitrary raw limbs; no canonical-field precondition was introduced. Equalities cover the full extracted Result, including fail/div constructors, not only successful outputs.

| Row | Source theorem | Original statement bridge |
|---|---|---|
| V247 / op230 | PV_B1_SumOriginal.op230_source | PV_B1_HostSumSource.op230_source: original literal1024 length guard and ordered native CT-add fold, complete Option result |
| V261 / op254 | PV_B1_PowersControl.op254_source | PV_B1_PowersBridge.op254_copy_equal_original: every Usize N and raw WideExact input, including N=0 and final-iteration behavior |
| V264 / op258 | PV_B1_PoleControl.op258_source | PV_B1_PoleBridge.op258_source: indexed CT scan equals the original flat verdict for every slice/mask/chi, preserving oversized failure |

PV_B1_Shift31, MaskShift and MaskCast prove literal-port equality and nonfailure, including mask count/index bounds. PV_B1_Orig258_Op258RowLaw retains the original row predicate and quantifiers. PV_B1_PoleOutcome/FalseLaw prove true/false/failure classification; typed HostPoleTruth/HostSumOption preserve it through raw carrier bijections. PV_B1_PowersTotal proves modeled all-N totality using checked field primitive totality, without evaluating a concrete large recurrence. PV_B1_SelectedContract.source_contract and ReferenceInstall.source_eq assemble only230/254/258 in the pinned callback signature cohort; all other foreign callbacks remain unchanged obligations. CarrierResultRecovery proves full-Result transport is reversible.

`extraction-resume.json` records fresh extraction of each applied function with unchanged pinned Charon/Aeneas (preflight/default on, strict joins and abort-on-error). Raw generated output is preserved. `backend-ports.json` records every naming/literal/masked-cast adaptation. Original powers and pole representations use structurally bound predecessor controls, **not fresh extraction of those unsupported original iterator/early-return functions**; their precise source associations/adaptations are in powers-original-binding.json and pole-original-binding.json. Compiler/native executable adequacy remains a P obligation. Private callback signature cohort and original classification port checks passed; no shared env-J source was written.

## Native client and fixture-byte gate

The recommended optimized, offline, locked devnet_spend build with r1p-check,aspis-r1-cost-probe/ct-host-prover passed at ccf87ccecd: exit0,112.857s,642240KiB peakRSS,swap0. The optimized fixture example build passed (43.186s,565996KiB); transfer0 and withdrawal0 generation passed (37.580s,666428KiB), both transaction verifier stages successful. `candidate/build-native-devnet-prover-local/command.json` and receipt preserve compiler/environment and binary pins.

`fixture-comparison.json` passed: raw public.bin, proof.bin and ledger burn-record bytes match for both saved fixtures; complete result metadata matches except diagnostic seconds. Existing baseline source37794d7bff is runtime/configuration byte-identical to c57a344726 across all compared relevant paths (`fixture-baseline-binding.json`), and saved public/proof digests also match predecessor pinned evidence. Comparison exit0,.024s,15840KiB,swap0. Both fixtures have statusOk; no separate negative failure fixture was claimed. This is two deterministic fixture pairs, not the lead's1000-run differential/quiet timing gate. No chain transaction or key cleanup was performed; task keys and ledgers are retained securely.

## Audit, receipts and stopping condition

Budget exhausted: **100/100 Lean,0/0 Kani**;85 successful compiles and15 failed attempts, all failed-source issues subsequently repaired. All82 final source modules have successful receipts matching their frozen SHA256. TALLY.json is authoritative. The single final frozen-manifest check passed. Final audits at proof revision8723f12e8bb13a21e9dd03741f18b69256df3187 (runtimeccf87ccecd) were:

| Target | ID | Exit | Outer wall s | GNU wall | Peak RSS KiB | Swap | Axiom queries |
|---|---:|---:|---:|---|---:|---:|---:|
| PV_B1_AuditSource | 53701 | 0 | 1.193 | 0:01.13 | 2621000 | 0 | 26 |
| PV_B1_AuditTyped | 53702 | 0 | 1.231 | 0:01.15 | 2627972 | 0 | 10 |
| PV_B1_AuditManifest | 53703 | 0 | 1.992 | 0:01.90 | 2636040 | 0 | 728 |

All accepted axiom-query results use only propext,Classical.choice,Quot.sound (or no axioms). No prohibited proof declaration is present. Peak across all100 charged compiles was2842276KiB; every charged compile recorded swap0. `FINAL-AUDIT.json` indexes source coverage and failures; `receipts.csv` gives every host target, exit, wall, peakRSS,swap,exact source revision and axiom result; the raw per-run receipts retain commands, imported object/source hashes, scope caps and output. Failed compiler outputs can mention sorryAx for rejected unresolved goals; **no accepted final declaration depends on it**. There was no complete-manifest rerun after the passing final check. Failed proof attempts, admission refusals and pre-launch audit sequencing failures are retained rather than hidden. RESUME.md records the fresh-ID recovery for reserved53897–53899 (no Lean scope, charged0), the initial private import-priority repair and the four-second-early admission retry. Admission now requires allowed:true and exit0; quiet markers are honored. No unchanged failed build was rerun and no memory cap was raised. No checked ROW counterexample was found.

## Premise ledger and next deliverable

Before/after `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` and its deployment conditions are unchanged: removed0,added0,weakened0,changed0. The new source lemmas discharge local source/model subobligations for V247/V261/V264; they do not alone discharge the endpoint's native integration assumptions. T remains exactly entropy_law,entropy_kernel,observation. Retained P includes source/executable and actual callback installation adequacy, E1/E2, actual RunJoin, entropy/kernel bridge, witness-independent native OS failure, client proof-account route, inversion boundary, L1/L2/L3 byte/side-channel observation, and the deployment closure. No missing fact was transferred to T or the observer/simulator weakened.

Next concrete deliverable: connect the checked selected callback dictionary/source identities to the real native RunJoin and endpoint premises, with the lead's combined differential/timing gates and native failure independence evidence. Target remains unestablished until the lead says otherwise. Full branch log is git-log.txt. No push.
