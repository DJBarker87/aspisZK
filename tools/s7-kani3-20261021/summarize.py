#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani3-20261021'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('proofs/*/receipt.json'))]
accepted=[]
for p in sorted((B/'lean').glob('S7Kani3*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 rs=[r for r in receipts if r.get('source_sha256')==sha and r.get('exit_status')==0]
 assert rs,p
 r=rs[-1]
 assert all('sorryAx' not in x for x in r['print_axioms']),p
 assert len(r['print_axioms'])==len(re.findall(r'^#print axioms ',p.read_text(),re.M)),p
 for report in r['print_axioms']:
  if 'depends on axioms:' in report:
   assert set(re.search(r'\[([^]]*)\]',report)[1].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'},report
 accepted.append(dict(module=p.stem,source_sha256=sha,attempt=r['attempt'],axioms=r['print_axioms'],peak_rss_bytes=r['peak_rss_bytes']))
manifest=dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),attempts=receipts,host=[json.loads(p.read_text()) for p in E.glob('host/*/receipt.json')])
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary=dict(status='PARTIAL: complete frozen constructor and TX trace membership remain open; no S7/S8/R17 discharge',modules=accepted,theorem_audits=sum(len(r['axioms']) for r in accepted),peak_rss_bytes=max(r['peak_rss_bytes'] for r in accepted),all_compiler_attempts_zero_swap=all(r.get('swaps')==0 for r in receipts if r.get('wall_seconds') is not None),kani_roots=2,endpoint_premises_removed=0)
(E/'accepted-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='modules'}))
