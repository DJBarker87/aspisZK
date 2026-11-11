# PCXV_ PIN2 cold replay (S4), band summary

Run on the host in /home/dombarker/project-offloads/codex-pc-pin2-replay-20261111 with pcxv_runner.py (PCXR runner plus an --excluded-file flag, PCXV_runner.py). Overlay 731/731 sha256 verified, no symlinks. Source revision: research d341c6e744c, L187 plan 18a98720, one module per capped scope (6G/8G, swap 0, TasksMax 64, -M7000, 180 s).

Handover semantics: 682 overlay modules in the set count as BUILT. Excluded roots (7): PublicExtractedRawBridge431, WithdrawalCarrierBridge431, RPv_FIz_CoefficientsOnRun, RPv_FIz_WideCoefficientsOnRun, NDO_JFs_SerializerSize, NDO_JFz_Row17, NDO_JFz_Row18. Their transitive importers: 9,775 BLOCKED_BY_EXCLUDED (includes TAS_FinalB, NNH_Run6Top, NNH_Run6Charge, NNH8_Top, ExtractedPublicCheckedBridge432). 6 handover inputs not in the overlay compiled unedited from L187. 220 modules were to be compiled.

Result: 211 PASS, 1 FAIL, 8 BLOCKED_DEP (importers of the failure). Wall 664 s. Peak RSS max 4.52 GiB, swaps 0, no sorry warnings, per-scope overhead median 0.24 s, max 3.1 s. Tripwire (full sha256 of the 300 sample and all 10,684 L187 rebuild-set objects, file count 14,101): no change.

FAIL: CostedExtractorStagesM10 (exit 1, 2.2 s): at src line 80:53, ExtractorStagesM10.public_work expects (PublicParserWork.parsePublic run.2.1.1.pubBytes).2 <= 110260 but PublicParserWork.parsePublic_work now gives <= 110542. The unedited L187 source carries the old constant; the W3b PublicParserWork bound changed. Declaration AspisR1.CostedExtractorStagesM10.work then depends on sorryAx. Not rerun unchanged. Blocked by it: CostedAllocationLedgerM10, ActualExtractorStagesM10, ActualAllocationExtractorM10, ActualResourceEvalM10, ActualCostedExtractorM10, ActualResourceBoundsM10, ActualLedgerSideBoundsM10, ClosedAllocationLedgerM10.

Headline roots (TAS_FinalB, deployed_splitB, deployed_charge): not compiled, BLOCKED_BY_EXCLUDED; no axioms result. Diagnostic of the 7 excluded roots (credits nothing): all FAIL, see diag/ (4 import-time unknown module prefix on excluded modules, 2 FIz on_run Public type mismatch with sorryAx, WithdrawalCarrierBridge431 on the missing 431 bridge).

Runner parked: no driver running, resumable (receipts with unchanged keys skipped; the failed receipt is never rerun unchanged).

Target not yet established
