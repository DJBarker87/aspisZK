# Retained input failures; no Aeneas body failure

| Attempt | Exact failure | Classification and replacement |
|---|---|---|
| local exporter, before P001 | `[lib].path = src/lib.rs` treated as package path | OWN script error; traverse dependency/patch/replace tables only. No host compile/extraction launched. |
| E001 after Charon exit0 | NHR_stage.py inventory `source_text:null` caused AttributeError on `.encode()` | OWN collector error, before Aeneas. Collector treats null as empty. Inspection of saved LLBC also found Prepared::new transparent. |
| E001 boundary inspection | explicit inherent impl selector did not make verifier.rs72–89 opaque | OWN input limitation; wildcard impl-element selector with matched LLBC span check. E002 succeeds. Read-only matcher source has inherent Ty match TODO/false; actual saved LLBC is authoritative. |
| E003 after Charon exit0 | asserted opacity for `candidate::checkpoint` had no LLBC match | OWN path error: checkpoint is imported from verifier. E004 corrects selector and succeeds. Pending resume selector was corrected by the same frozen-source inspection. |

None timed out or was memory-killed. No cap or timeout was raised. Neither E001
nor E003 reached Aeneas, and neither establishes a tool-body limit. All four
correctly staged/opaque driver shapes emit successfully (E002/E004/E005/E006).
The failed LLBC and receipts are retained, not renamed into passing evidence.
