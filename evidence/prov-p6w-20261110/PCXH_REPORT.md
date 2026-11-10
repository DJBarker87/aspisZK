# PCXH_ report: single release-universe root, fresh declaration comparison, recount

Provenance only. No ledger row, trust row, RSL, security contract or shipped source changed; nothing pushed or merged. Branch codex/pc-prov-p6w-20261110 (base research 17700d32155). Frozen source 4bb3b3f. 14 Lean scopes of 16 (all exit 0 except three that are recorded below), 0 extraction, 0 Kani, one at a time, 6G/8G, swap 0, peak RSS at most 7.1 GiB (PCXH_ATTEMPTS.jsonl, PCXH_Lnnn/receipt.json).

## 1. Single root

The earlier failure was PCVH.dec_qm. A constant-name scan of the 54 credited modules' objects (PCXH_L001, no import, so clashes cannot stop it) found more than that one name. Real clashes: PRVEq_PCVH_R1CandidateWideParserSource_k1 against PRVCmb_C19 (21 names in namespace PCVH); PRVEq_AdapterStage1_o1, AdapterStage2_o1 and CallerPrepTx1_o1 against PRVCmb_C20 (namespaces PCVK_S1, PCVK_S2, PCVK_C, 104 to 148 names each); the three helper names PRVEq_after_ex, PRVEq_usize_add_wrap, PRVEq_partialEq_ne_default shared by Stage1 and Stage2; and the tactic keyword delta_matchers. Identical auxiliary constants (match_N, eq_N, congr_simp, fixpoint_induct) are tolerated by import and were left alone.

One token rule with identifier boundaries, applied only to ten PRVEq evidence files: PCVH to PCVH_k1, PCVK_S1/S2/C to PCVK_S1_o1/S2_o1/C_o1, the helpers and delta_matchers with a per-file suffix. Every rename (old, new, file, occurrences, sha256 before and after) is in PCXH_RENAMES.json. The renamed files and their dependents (12 + 8 modules) recompiled with exit 0 (L002 to L004). PRVCmb_L187_ROOT then compiled exit 0 (L009) importing PRVH_WrapAdd, all 22 bundles, the 28 deployed-body modules and the four P3s modules: one root, no clash. A first version of the root with the audit in the same process also exited 0 (L005: 5,445 theorems audited one by one, union propext, Quot.sound, Classical.choice, 0 local axioms, 1058 of 1058 credited names found) but that version excluded P3s.

What did not work, stated plainly: with P3s added, the in-process audit hit the Lean -M7000 interpreter limit (L008, exit 134); the imported environment alone is about 6.9 GiB RSS. A separate audit module importing the root failed the same way twice (L010, L011); that shape is retired. The axiom audit therefore runs in sub-environment modules built from the same objects: bundles (L012: 4,867 theorems, union standard, 0 local axioms), deployed modules and P3s (L013: 304 theorems, standard, 0 local axioms). All 1,058 credited bundle names and all 80 credited deployed and P3s names (70 plus 10) are found, axioms standard (PCXH_AUDIT.json). So: coexistence is shown by the single root; the audit is by sub-environment. Bundle objects are the PCXG ones, pinned by sha256 in the L009 receipt, not recompiled.

## 2. Fresh declaration comparison

L006 compared NHT_Constants and CurrentCompactCallerModelV1 between the ledger30-chain objects (NII_flat, pool-retarget-cache) and the L187 objects, both directions, with L187_Compare. The tool hash on the host is a758dd57, not c5f43e8e: the committed binary.sha256 file records c5f43e8e as the first build and a758dd57 as the 2026-11-09 rebuild that every runner batch used; I used it read-only and recorded the difference. Result: imports, constant names and every declaration identical, all_differing empty (44 and 83 constants), in both directions. The earlier DECL_IDENTICAL label is now backed by a fresh comparison for these two modules. The tool's ability to report a difference is documented only by L187's own run, not re-run (PCXH_DECL_COMPARE.json). The other 200 imported modules keep L187's labels.

## 3. Recount, headline-first on AspisR1.TAS_FinalB.deployed_splitB (1,707 definitions)

SETTLED = EQUALITY_PROVED + pin-equal RECEIPTED + SelectedMaskProbe; NOT SETTLED = RECEIPTED without pin-equal + OPEN.

* PCXG_: 993 settled, 649 not settled, 65 other.
* With P6y (PCXI_): PIN_EQUAL 64 settled, TEXT_DIFFERS 79 and NOT_REDERIVABLE 40 not settled: 1,057 settled, 585 not settled, 65 other. This matches the lead's figure.
* With P1n (PCQK_), a separate step: its five n3b modules (13 theorems) replayed exit 0 in L187 (L014); all 13 definitions were OPEN in the cone. Result: 1,070 settled, 572 not settled, 65 other. Not settled = OPEN 453 + TEXT_DIFFERS 79 + NOT_REDERIVABLE 40 (that is, 572). Settled = EQUALITY_PROVED 920 + P1n 13 + RECEIPTED pin-equal 99 + SelectedMaskProbe 38.
* Listed separately, unchanged, 65: EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 43 (all deployed top bodies), DEPENDS_ON_LIBRARY_TRUST 7 (heap::filled names HM-C, not D.5), HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 4.

P3s (replayed L007, audited L013) and P3t change no definition count: the deployed top bodies stay conditional; P3s relates three tx2 slots to frozen emissions, with reserved, query, geo, base and finish still parameters. P3t per-slot results (op47 to op52, hashv) carry hypotheses, op21/op24 are model-fidelity notes, op50 and op45 pending owner rows; P3t was not replayed in L187 because its modules import PRVEq modules outside the closure and the renamed o1 chain. P1o: the 28 emissions at non-pinned jobs/threads are tagged; identity is NOT_ESTABLISHED. A text match of those run ids against each record's fresh_emission and receipt fields found no definition, so no demotion is applied, but the match covers two fields only and may under-count; the Stream A lead should decide whether that check is enough.

599-row view (PCXH_ROW_TABLES.json): 114 rows reach only settled definitions, 18 touch an other class with nothing not settled, 453 reach at least one not-settled definition, 12 reach no emitted module, 2 are rootless. Row verdicts are identical to PCXG_ although the not-settled counts changed in 211 rows; no row crossed the line.

## Delta from PCXG_

Single root achieved with recorded renames; fresh comparison done; split 993/649 to 1,057/585 (P6y) and 1,070/572 (P1n added); audit by sub-environment because the full root exceeds the memory cap.

## Not established

572 not-settled definitions, 43 binding results and every deployed top body, trust-class items, jobs identity, receipted extractions' overflow configuration, release replay, R22 and source-to-ELF. Provenance equality is not a security claim.

Target not yet established.
