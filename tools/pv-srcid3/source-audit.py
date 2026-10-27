#!/usr/bin/env python3
"""Match final new Lean sources to focused receipts, without replaying."""
import hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];ev=root/'evidence/pv-srcid3-20261026'
a=[json.loads(s) for s in (ev/'attempts.jsonl').read_text().splitlines()]
tracked=subprocess.check_output(['git','diff','--name-only','52a0f8acee','--','docs/research/v8-r0-zk-20261009/lean/R1Z'],cwd=root,text=True).splitlines()
rows=[]
for p in tracked:
 f=root/p
 if not f.exists() or f.suffix!='.lean':continue
 s=f.read_text();sha=hashlib.sha256(f.read_bytes()).hexdigest()
 hits=[r for r in a if r['source_sha256']==sha and r['exit']==0 and r['module']=='R1Z/'+f.stem]
 body=re.sub(r'/\-.*?\-/','',s,flags=re.S);body=re.sub(r'--[^\n]*','',body)
 forbidden=re.findall(r'\b(?:sorry|admit|native_decide|implemented_by|axiom)\b',body)
 rows.append(dict(file=p,sha256=sha,accepted_attempts=[r['attempt'] for r in hits],forbidden=forbidden,axioms=hits[-1]['axioms'] if hits else []))
report=dict(charged_lean=len(a),predecessor_lean=4,remaining_lean=json.loads((ev/'BUDGET.json').read_text())['authorized_lean_total']-4-len(a),kani_invocations=len((ev/'kani-invocations.jsonl').read_text().splitlines()),files=rows)
(ev/'source-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='files'}))
print('Matched',sum(bool(r['accepted_attempts']) for r in rows),'of',len(rows),'source files')
for r in rows:
 if not r['accepted_attempts'] or r['forbidden']:print('REVIEW',r['file'],r['forbidden'])
assert all(r['accepted_attempts'] and not r['forbidden'] for r in rows)
