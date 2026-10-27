"""Build a reviewable handoff from completed per-root receipts."""
from pathlib import Path
import json,subprocess
p=Path(__file__).resolve().parents[2]/'evidence/pv-cb9-20261027'
receipts=[]
for q in sorted(p.glob('cb9-op*/receipt.json')):
 r=json.loads(q.read_text());receipts.append(dict(receipt=str(q.relative_to(p)),**r))
(p/'RECEIPTS.json').write_text(json.dumps(receipts,indent=2)+'\n')
rs=[]
for r in receipts:
 stage='Charon' if r['receipt'].split('/')[0].endswith('charon') else 'Aeneas'
 op=r['receipt'].split('/')[0].split('-')[1]
 rs.append(f'| {op} | {stage} | {r["exit"]} | {r["wall"]} | {r["peak_rss_kib"]} | {r["swap"]} | `{r["source_revision"][:10]}` |')
proofs='''No theorem added; no `opN_source` law is claimed for these roots. `#print axioms`: N/A for extraction processes. No Lean compilation was launched because no root reached a nonempty generated Lean extraction. The existing PV_CB3_CallbackBundle and all ProverRw* files are unchanged. No privacy endpoint premise was removed, added or changed. No counterexample was found. The privacy target is **not yet established**.
'''
text='''# CB9 direct extraction handoff

Branch: codex/pv-cb9-20261027. Base: a436dadfee.

Rows discharged: **0**. Four independent OPEN rows were requested; nine named candidates were inspected, op259 was SKIP(sibling), eight had direct shipped roots extracted to LLBC with the pinned Charon; op252 also has a current-crate path-module coverage correction (OP252-COVERAGE.md). Read ROWS.md for per-op status and INVENTORY.md for exact pinned Aeneas refusals.

'''+proofs+'''
## Validation receipts

Every target and complete revision is retained in RECEIPTS.json and the per-run receipt.json. All scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Compilation/extraction was optimized release. The pinned binary SHA-256 values match retained-extractor-pins.txt from the base cb3 evidence (Aeneas 562e1f51..., Charon daad69be...). No preflight switch was disabled.

| op | phase | exit | wall | peak RSS KiB | swaps | revision |
|---|---|---|---|---|---|---|
'''+ '\n'.join(rs)+'''

786 host snapshot files match tracked worktree bytes (source-identity.json). LLBC-AUDIT.json verifies actual root names, source spans, structured bodies and has_errors=false. These checks establish extraction input coverage, not a source-to-model theorem. The mutable historical LLBCs were not reused or attributed to historical evidence: this run uses unique PV_CB3_CB9OpN files.

## Budget and boundaries

Lean: 0/100. Kani: 0/4. Env-J IDs: none used, next 51500. 51797–51799 remain reserved for the bundle audit. No shared env-J source written. No shipped source changed. No keys touched. No Kani field arithmetic runs. Native-effect obligations are recorded separately in NATIVE-DEFERRALS.md for pv-runjoin.

The instruction to move on after each refusal prevents an unchanged retry or an unapproved reference workaround. The budget is unspent, not exhausted. A lead decision is requested for additional eligible direct-extraction rows or route (ii); no source-law or audit compile will be fabricated to consume the budget.

Next concrete deliverable: lead-selected additional extraction rows or a lead-approved route (ii) with its shipped-source link; then complete Result source equations for four rows, additive PV_CB3_CallbackBundle composition, and the reserved bundle audit.

## Commits from the requested base

```text
'''+subprocess.check_output(['git','log','--oneline','a436dadfee..HEAD'],text=True)+'''```
'''
(p/'HANDOFF.md').write_text(text)
print(len(receipts),'execution receipts summarized')
