"""Summarize actual extraction receipts without assigning proof credit."""
from pathlib import Path
import json,re
p=Path(__file__).resolve().parents[2]/'evidence/pv-cb9-20261027'
rows=[]; additions=[]
for op,row in [(226,243),(227,244),(228,245),(230,247),(250,257),(251,258),(252,259),(254,261),(259,265)]:
 if op==259: rows.append(f'| {op} | V{row} | SKIP(sibling) | PV_CB_Op259Exact.op259_source | op259-siblings.txt |');continue
 d=p/f'cb9-op{op}-aeneas'; c=p/f'cb9-op{op}-charon'
 if op==252 and (p/'cb9-op252current-aeneas/receipt.json').exists():d=p/'cb9-op252current-aeneas'
 if (d/'receipt.json').exists():
  r=json.loads((d/'receipt.json').read_text());log=(d/'output.log').read_text(); clean=re.sub(r'\x1b\[[0-9;]*m','',log)
  errs=[x for x in clean.splitlines() if any(s in x for s in ['[Error','Source:','Compiler source:','fail-closed preflight:'])]
  status='REFUSED (OPEN)' if str(r['exit'])!='0' else 'extracted; coverage/typecheck pending (OPEN)'
  additions.append(f'### op{op} / V{row}\n\nStatus: {status}. Direct shipped root `{r["entry"]}`.\n\n```text\n'+ '\n'.join(errs)+'\n```\n\nReceipt: `'+d.name+'/receipt.json`; full log: `'+d.name+'/output.log`. No source theorem, no row credit, no counterexample.\n')
  receipt=d.name+'/receipt.json'
 elif (c/'receipt.json').exists():
  r=json.loads((c/'receipt.json').read_text());status='MIR extracted; Aeneas pending (OPEN)' if str(r['exit'])=='0' else 'Charon failed (OPEN)';receipt=c.name+'/receipt.json'
 else:status='queued (OPEN)';receipt='none'
 rows.append(f'| {op} | V{row} | {status} | none | {receipt} |')
(p/'ROWS.md').write_text('# CB9 row accounting\n\nRows discharged: **0**. Four independent OPEN rows requested; eight eligible candidates after sibling scan. No endpoint premise removed, added or changed. No native-effect result claimed.\n\n| op | row | status | theorem | extraction receipt |\n|---|---|---|---|---|\n'+'\n'.join(rows)+'\n')
s=(p/'INVENTORY.md').read_text().split('\n## CB9 direct-root additions')[0]
(p/'INVENTORY.md').write_text(s+'\n## CB9 direct-root additions\n\nPinned extractor unchanged; preflight enabled. These are extraction obstructions, not checked counterexamples. No Kani arithmetic retry or prover-local copy is authorized.\n\n'+'\n'.join(additions))
