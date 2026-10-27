#!/usr/bin/env python3
"""Match current imported project objects to hash-bearing successful receipts."""
import json,pathlib,subprocess,re,hashlib
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';d=json.loads((e/'resume6-full-closure.json').read_text());rev=d['research_revision']
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence'],text=True).splitlines()
paths=[p for p in paths if p.endswith('.jsonl') and 'attempt' in p.lower()]
receipts=[]
for p in paths:
 try:data=subprocess.check_output(['git','show',rev+':'+p],stderr=subprocess.DEVNULL).decode()
 except Exception:continue
 for line in data.splitlines():
  try:r=json.loads(line)
  except Exception:continue
  if isinstance(r,dict):receipts.append((rev+':'+p,r))
for p in e.glob('*attempts.jsonl'):
 for line in p.read_text().splitlines():
  try:r=json.loads(line)
  except Exception:continue
  if isinstance(r,dict):receipts.append((str(p.relative_to(root)),r))
by={}
for p,r in receipts:
 if r.get('exit')!=0 or r.get('nonstandard_axioms') or r.get('axiom_reports_complete') is False:continue
 m=r.get('module','').replace('/','.');src=r.get('source_sha256');obj=r.get('object_sha256')
 if not obj:
  retained=r.get('retained_own_object','');obj=retained.split()[0] if isinstance(retained,str) and re.match(r'^[a-f0-9]{64} ',retained) else None
 if src and obj:by.setdefault((m,obj),[]).append(dict(receipt=p,attempt=r.get('attempt'),source_sha256=src,object_sha256=obj))
for r in d['project_modules']:
 hits=by.get((r['module'],r['object_sha256']),[]);r['object_source_receipts']=hits
 expected=r['research_source_sha256'] or r['source_sha256'];r['expected_source_kind']='research HEAD' if r['research_source_exists'] else 'unmerged branch addition'
 r['verified_compiled_source_matches_expected']=any(x['source_sha256']==expected for x in hits)
 r['provenance_gap']=None if r['verified_compiled_source_matches_expected'] else ('no successful receipt linking current object hash to expected source hash' if not hits else 'current object receipt source differs from expected source')
(e/'resume6-project-provenance.json').write_text(json.dumps(d,indent=2)+'\n')
print('hash-linked',sum(r['verified_compiled_source_matches_expected'] for r in d['project_modules']),'of',len(d['project_modules']))
