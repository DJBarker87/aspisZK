# Callback mid-row work

Branch codex/pv-cbmid-20261027, candidate base 237e13556180d2ce0320a2760f89b35b5f4f02bb (unmerged). Target not yet established. Rows discharged **0 → 0**. Endpoint premises removed **0**; none added or weakened. No checked ROW counterexample.

| op | row | status | theorem | receipt |
|---|---|---|---|---|
|132|V228|Direct Aeneas refused references/structured Drop; mutable-output owned reference extracted. All60 chunks and reference composition passed; complete native equality pending.|PV_CBM_CallbackBundle.op132_reference; CellsSpec.callback (reference prerequisites only)|40738.json;40739.json; aeneas-op132-001/receipt.json; aeneas-op132fill-001/receipt.json; numbered chunk receipts|
|133|V229|Direct Aeneas refused references/structured Drop. Mutable-output reference prepared; native equality pending.|none|aeneas-op133-001/receipt.json|
|134|V230|Owned reference extracted and selected. Complete native equality timed out at180s and permitted900s retry; no verdict.|PV_CBM_CallbackBundle.op134_reference (not a source law)|aeneas-op134ref-001/receipt.json; kani-masks-001/receipt.json; kani-masks-900-001/receipt.json|
|79|V201|Built MIR extracted, direct Aeneas refused references/structured Drop. Indexed reference and canonical QM31 harness prepared. Actual QM31/WideExact caller invariant remains open.|none|aeneas-op79-001/receipt.json|
|222|V239|Optional; latest sibling search absent. Indexed reference and partial-domain harnesses prepared; no native association.|none|FRAGMENT-PINS.json|
|224|V241|Optional; latest sibling search absent. Exact source fragment prepared.|none|FRAGMENT-PINS.json|

Before work, all six source-law searches were absent on codex/pv-cb-20261026, codex/pv-cb3-20261026 and codex/pv-cblib-20261027. Frozen crates/programs and all ProverRw imports remain unchanged. The single stable bundle publishes reference selections only, never substitutes them for opN_source.

Proved prerequisites: sparse inventory classification bijections and cardinality3803 (40624), generic bounded append and complete Result right-identity, and separately checked literal chunks. Native classifier kani-classifier-001 passed all61 checks over row<1024,column<16, unwind25, no stubs. None discharges the whole callback. See RECEIPTS.md for every actual target, exit, wall time, RSS, swap, source revision and axioms output. TALLY.json is authoritative for budget/ID use; refused admissions consume IDs but not compile attempts. Last three charged Lean attempts and IDs40897–40899 remain reserved for audit.

Mutable-output extraction preserved native wrapper ownership/destructors. No Drop erasure or backend modification. CELL-DROP-INSPECTION.json records the refused ownership graph. prepare_cells.py --check and prepare_fill_spec.py --check validate current emission; drafts without a passing current-source receipt are explicitly uncredited.

Cache provenance: cb3/lean-objects was absent; no cache copy claimed. PROVENANCE.json and SOURCE-RECHECK.json record the read-only source/manifests match. Restored shared objects support focused candidate evidence, not a coherent deployed release replay. LEAN-IMPORT-PROVENANCE.json pins the unchanged ProverRw imports. No sibling source is overwritten. One capped scope at a time;6G/8G/swap0. Admission refusal triggers180s wait and a fresh ID.

Masks900 timeout: no third identical run. GNU-time parent RSS is incomplete for killed descendants; retained snapshot measured CBMC VmHWM6699344KiB, cgroup peak6873858048 bytes, swap0. TEN-MINUTE-REVIEW.json explicitly records its late physical snapshot; it is not represented as an exact600s measurement.

Next deliverable: complete inventory composition, remaining native comparisons/extractions, and one final bundle audit within the100 Lean/10 Kani budgets. P6 association requires complete shipped/reference equality and actual canonical caller invariants; prepared partial-domain tests do not satisfy that requirement.

Checked composition stage: all60 literal chunks, exact fill definition40732, complete Result wrapper40733, selected callbacks40735, generic composition lemmas40737, revised CellsSpec40738 and bundle40739 passed. CellsSpec records success, length3803 and all-free membership. It does not prove shipped equality or uniqueness/completeness of this inventory. Failed40736 is retained as replaced by symbolic append/length/capacity reasoning; no caps/limits raised. Current checkpoint94/100 Lean,3/10 Kani. All82 live modules match passing source-hash receipts.
