#!/usr/bin/env python3
"""Read-only section-6 receipt/axiom collector; never starts a job."""
from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parents[3]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-install'
rows=[]
for p in sorted(e.glob('124*-input.json')):
 x=json.loads(p.read_text());a=x['attempt']
 assert hashlib.sha256((e/f'{a}.lean.txt').read_bytes()).hexdigest()==x['source_sha256']
 log=(e/f'out-{a}.log').read_text() if (e/f'out-{a}.log').exists() else ''
 time=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
 match=re.search(r'^exit=(\d+)',log,re.M)
 status=int(match[1]) if match else None
 axioms=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 if status==0:
  assert 'sorryAx' not in log
  for report in axioms:
   if 'depends on axioms:' in report:
    names=report.split('depends on axioms: [')[1].split(']')[0].replace('\n','').split(',')
    assert set(n.strip() for n in names)<= {'propext','Classical.choice','Quot.sound'}
 command=f"sh {x['launcher']} {a} {x['module']} J 7000 7 {x['deps_fingerprint']}"
 x.update(exit_status=status,command=command,time_log=time,print_axioms=axioms,errors=[l for l in log.splitlines() if 'error:' in l],disposition='Accepted focused source proof, not formal release evidence' if status==0 else 'Rejected; preserved changed successor/split required')
 if a==11601:x['disposition']='Reservation refused before Lean; changed/split successor11602; no time/RSS/axioms exist'
 (e/f'{a}-receipt.json').write_text(json.dumps(x,indent=2)+'\n')
 rows.append(dict(attempt=a,module=x['module'],source_sha256=x['source_sha256'],exit=status,wall=re.findall(r'Elapsed .*: (.*)',time),peak_rss_kib=re.findall(r'Maximum resident set size \(kbytes\): (.*)',time),swaps=re.findall(r'Swaps: (.*)',time),axiom_reports=len(axioms)))
(e/'summary.json').write_text(json.dumps(dict(attempts=rows,lean_compiles=sum(r['exit'] is not None for r in rows),passed=sum(r['exit']==0 for r in rows),failed=sum(r['exit'] not in [None,0] for r in rows),reservation_refusals=[r['attempt'] for r in rows if r['exit'] is None],kani_runs=json.loads((e/'native-summary.json').read_text())['actual_kani_runs'] if (e/'native-summary.json').exists() else 0,budget=dict(Lean=100,Kani=20),source_revision_labels='Base commit at invocation plus exact WIP source snapshot and dependency object hashes; source hash is authoritative',scope='Focused source dictionary/model proofs only; no native callback/extractor/ABI/Drop, whole caller/RunJoin or frozen-release closure'),indent=2)+'\n')
print(json.dumps(dict(lean_compiles=sum(r['exit'] is not None for r in rows),passed=sum(r['exit']==0 for r in rows),failed=sum(r['exit'] not in [None,0] for r in rows))))
