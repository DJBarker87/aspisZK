#!/usr/bin/env python3
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s7-kani2-20261021'
records=[];roots={};audits=[]
for p in sorted(E.rglob('receipt.json')):
 r=json.loads(p.read_text());r['receipt']=str(p.relative_to(R));records.append(r)
 if 'module' in r and r.get('exit_status')==0:
  assert all('sorryAx' not in line for line in r['print_axioms']),p
  audits.extend(r['print_axioms'])
 if p.parent.parent.name=='receipts':
  log=(p.parent/'stdout.log').read_text();current={};tid=None;success=[]
  for line in log.splitlines():
   m=re.match(r'Thread (\d+): Checking harness (.+)\.\.\.',line)
   if m:tid=int(m[1]);current[tid]=m[2]
   else:
    m=re.match(r'Thread (\d+):',line)
    if m:tid=int(m[1])
   if 'VERIFICATION:- SUCCESSFUL' in line and tid in current:success.append(current[tid])
  r['successful_roots']=success
  for name in success:roots.setdefault(name,[]).append(str(p.relative_to(E)))
summary=dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),attempts=records,successful_kani_roots=roots,accepted_lean_audits=audits,counts=dict(attempts=len(records),unique_successful_kani_roots=len(roots),lean_audits=len(audits)),status='PARTIAL: complete S7/R17 production composition remains open; no endpoint premise removed')
(E/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary['counts']))
