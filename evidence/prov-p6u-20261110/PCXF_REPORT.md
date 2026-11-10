# PCXF_ report: provenance, P6 refresh 3 (recount after P3m to P3r and P1k, source_revision audit)

Provenance only. Frozen source 4bb3b3f, ledger30 gate, evidence on research at b0d2832be47 (P3m, P3n, P3o, P3p, P3q, P3r, P1k on top of the PCXE_ inputs). No ledger row, trust row, RSL, security contract or shipped source was changed, no trust row was entered, nothing was pushed or merged.

## 1. Headline: AspisR1.TAS_FinalB.deployed_splitB

The status counts for the 146370-constant cone are unchanged from PCXE_, because P3m to P3r prove statements about top bodies that were already CONDITIONAL_ON_BINDING records, and P1k's result is recorded separately by rule. Of 1707 reached definitions: EQUALITY_PROVED 920, RECEIPTED 256, EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 43, DEPENDS_ON_LIBRARY_TRUST 7, HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 4, OPEN 466 (263 with no overflow-correct fresh emission, 146 failed or other, 40 with no record, 17 wrong-basis, all counted OPEN). Module rollups over 209 modules: 115 OPEN, 40 RECEIPTED, 38 EQUALITY_PROVED, 5 CONDITIONAL, 2 DEPENDS_ON_LIBRARY_TRUST, 9 reach no annotated definition. The 599-row ledger30 view: 180 clean at definition level, 405 conditional, 12 reach no emitted module, 2 rootless; 554 rows rely on a module whose rollup is OPEN.

RECEIPTED is no longer read as pin-equal. Of the 256 RECEIPTED cone definitions, 35 are definitions of a frozen-tree crate that a pin naming 4bb3b3f covers and whose text is identical to a fresh 4bb3b3f emission. A further 38 (AspisR1SelectedMaskProbe) are RECEIPTED from a probe crate but now have a separate fresh = gate proof (section 3). The other 183 have no evidence that their emission is the frozen source. Their statuses did not change; the claim attached to them did.

The deployed top bodies are all CONDITIONAL_ON_BINDING (PCXF_DEPLOYED_SLOTS.json). In every one, the Bound record is satisfied by construction from the deployed fields, so any slot not listed as related below is organisation, not discharge.

* tx2_common and tx2_authenticated (PCVS_Tx2Deployed deployed_tx2_common_s, _authenticated_s and the _m forms; chain PCVM m1, PCVN n1, PCVQ q6, PCVS s1/s2). No h18 and no hE hypothesis remains; the free parameters are the deployed stage dictionaries. Proved related to a frozen emission: op2 (WideExact::from_le_bytes, with E32 discharged against the checkpoint decoder on all 32-byte windows), op13 (verifier::mark), op17 (weights::powers, with frozen WideExact mul, ZERO and ONE now bound by PCVS_E001), op18 (resume, by the simulation theorem under 13 leaf equalities, all leaves proved), tag, final_len, checkpoint_size, CHECKPOINT_FIXED and QM31 ZERO (PCVS_E002), and the constants op14 to op16, op20 to op23. Only instantiated by deployed fields: op3 (a wrapper of Op3I_Source, itself a probe-crate emission), op5, op6, op9, op10, op11, op19, read_checkpoint_semantic_alpha, read_checkpoint_weights, QM31::from_le_bytes and heap::filled. Library or reviewed items: HM-B (Iter::any), HM-C (map_err), HM-D (slice eq/ne), and ReviewedTranscription-FieldDerives for the QM31 clone slot, which this body depends on and which is counted apart from plain equalities.
* stage1_owned, stage2_owned, prepare, tx1 at the corrected seed NOC_HostCtx.sdk c / NOC_HostSeed.m0 (PCVP_ noc_model1, noc_model2, noc_prepare, noc_tx1, seed_prepare). The fresh frozen body equals the gate body at the installed Ops for every host context, but no callee slot is related to the frozen emission of its callee; 18 slots have an installed-op = library-model theorem, which is a relation to a library model, not to the frozen source. Non-vacuity is shown (installed op1 returns Ok on a granted reservation). P3o's deployed_prepare and deployed_tx1 at NNH_HostSeed.m0 are near-vacuous (op1 diverges there) and are not credited; P3o's stage1 and stage2 at the NNH seeds are superseded by the P3p statements and not audited separately.
* VTop tx1, NMP_prepare and NMT_tx1 stay OPEN.

## 2. source_revision audit (PCXF_SOURCE_REVISION_AUDIT.json)

How the field was filled. PCXA_PROVENANCE, and the status files that copied it forward, set source_revision to the fixed string "frozen 4bb3b3f" for every record that had no record from a proof phase (535 records). It was a default. Nothing derived the crate or revision; and the status RECEIPTED means only that a candidate source hash occurs in some pin file or Aeneas receipt of any revision and any crate (PCO_partition cand_status).

What was re-derived: the crate from each gate module's header, the pins that name 4bb3b3f from the pin files over the research tree, and the per-definition coverage (IDENTICAL, COVERED_DIFFERS, UNCOVERED) from the PCO comparison with fresh frozen emissions. Result: of 535 records, 393 claimed frozen 4bb3b3f wrongly or without support (318 RECEIPTED, 47 OPEN, 28 EQUALITY_PROVED, in 79 modules). 54 are supported (frozen-tree crate, pin names 4bb3b3f, text identical to a fresh emission). 88 were correct but underspecified (they carry a fresh 4bb3b3f emission, P2h or P3f) and now use the standard label. By verdict: 157 reference copies of REFERENCE-kind modules and 108 probe or cut crates (the 38 of AspisR1SelectedMaskProbe are crate aspis_r1_mask_extraction_probe), 29 frozen-tree-crate emissions whose revision no pin confirms, 8 frozen-tree-crate definitions that differ from the fresh emission, 16 with no crate header (transformed copies), and 28 EQUALITY_PROVED plus 47 OPEN records of reference crates. Inside the deployed_splitB cone: 221 of the 256 RECEIPTED plus 57 OPEN or EQUALITY_PROVED records. Each record now has source_revision_previous, source_crate, pin_equal and source_revision_verdict. Limit: the revision of the receipted extractions themselves, and their overflow configuration, are not re-derived.

## 3. Delta from PCXE_

| quantity | PCXE_ | PCXF_ | why |
|---|---|---|---|
| EQUALITY_PROVED, CONDITIONAL, DEPENDS, OPEN (cone defs) | 920, 43, 7, 466 | 920, 43, 7, 466 | no status moved |
| RECEIPTED cone defs with pin-equal evidence | not separated | 35 by coverage, 38 by fresh = gate | new fields |
| RECEIPTED cone defs without such evidence | not separated | 183 | source audit |
| wrong "frozen 4bb3b3f" labels | not found | 393 of 535 | source audit |
| clean rows / conditional rows | 180 / 405 | 180 / 405 | same row rule |
| combined import | 21 bundles, 292 files, 4812 theorems, 13099 constants | 22 bundles, 293 files, 4867 theorems, 13205 constants, plus 227 theorems in four by-reference audits | C22 (P1k, 46 theorems); deployed files |
| Lean scopes in the job | 8 | 6 with a receipt, all exit 0 | see section 4 |

P1k. PCVR_L002 proves 46 fresh = gate theorems for AspisR1SelectedMaskProbe.Funs (emission PCVR_E005, crate aspis-core, features r0, overflow ON). The 38 gate definitions that have a record stay RECEIPTED and carry the separate field fresh_gate_equality; eight of the 46 theorems (constants and closure bodies) have no record. I did not upgrade them to EQUALITY_PROVED.

## 4. Combined import and audit

PRVCmb_ROOT imports PRVH_WrapAdd and bundles C01 to C22. C01 to C21 were reused by reference; I compiled C22 (PCXF_L001, 45 s, 2.56 GiB) and the root (PCXF_L002, 40 s, 5.93 GiB). The audit covers 13205 constants and 4867 theorems one by one: each depends only on propext, Classical.choice and Quot.sound, no local axiom, no theorem skipped by the time guard, and all 1058 credited theorem records are found by name. No sorry, native_decide or axiom in a credited file.

This is not one import. The deployed-top-body files compile in a different module universe: NHT_Constants and CurrentCompactCallerModelV1 are different objects under the same name in the ledger30 chain and the L187 closure, NNH_HostSeed and the NOC modules exist only in L187, and the three PRVEq base modules clash when imported together (PCXF_UNIVERSES.json). A single root would silently mix versions, so I audited those files by reference with four small audit modules (PCXF_AUD_L1, L2A, L2B, L2C; PCXF_L004 to L007, 6 to 21 s, at most 6.82 GiB, swap 0): 227 theorems, standard axioms only, and all 70 credited deployed-body names found. These import objects built by the earlier jobs' exit-0 scopes; they check existence and axioms, they do not rebuild. PCXF_L003 failed in the client pre-check (import Lean not resolvable from a nine-entry chain); nothing ran on the host, and the shape was changed, not rerun.

## 5. Provenance, R22, hand models, externals, non-frozen, L187

Unchanged from PCXE_: the R22 split (51 wrapping, 217 checked, 8 partly wrapping, 1431 without arithmetic); 245 hand-written gate models; externals without a gate definition (502 resolve elsewhere, none covered by an existing trust row, 99 unresolved: 68 aspis-frozen, 31 library or SDK entries naming a proposed row); all 26 non-frozen cone modules OPEN under the owner decision (4 meet the condition at definition level); the L187 reconciliation. PublicPreparation counts: 20 EQUALITY_PROVED, 6 depend on HM-C, 3 of those also on ReviewedTranscription-PublicPreparation.public_bytes (counted apart; the headline cone reaches one constant of the module).

## 6. Not established

466 OPEN cone definitions (263 need an extraction), 17 wrong-basis, 43 binding results and every deployed top body (tx2: op3, op5, op6, op9, op10, op11, op19 and four reader helpers; every callee slot of stage1, stage2, prepare, tx1), 13 trust-class records, 183 RECEIPTED cone definitions with no pin-equal evidence, 5 HAND_ADAPTED, 4 NO_FROZEN_COUNTERPART, 19 of 24 no-source modules, 22 of 26 non-frozen modules, 68 aspis-frozen externals, the 23 array_from_fn dependants, a single-universe combined import, release replay, L187/L188, R22, source-to-ELF.

Target not yet established.
