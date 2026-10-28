"""Fail closed at every unresolved source-law transfer; never infer from samples.
Inputs are the committed fscan classification snapshots, live hash checked again.
This is an explicit partial structural gate, not a universal equivalence prover.
"""
from pathlib import Path
import json,lzma,hashlib,sys,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
rows=json.loads(lzma.decompress((D/'prior-classify.json.xz').read_bytes()))['rows']
functions=json.loads(lzma.decompress((D/'prior-functions.json.xz').read_bytes()))
sources=json.loads(lzma.decompress((D/'prior-sources.json.xz').read_bytes()))['files']
ids=['V229','V230','V231','V238','V239','V240','V247','V256','V257','V258','V259']
def tokens(s):
 return re.findall(r'::|=>|\w+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
out=[]
for r in rows:
 if r['id'] not in ids:continue
 checks=[];unresolved=[]
 for rec in r['reached_source_inventory']:
  name=rec['function'];f=functions[name]
  candidates=f.get('candidates',{}).get('deployed',[])
  entries=[]
  for c in candidates:
   key=c['key'];p=Path(sources[key]['path']);raw=p.read_bytes();sha=hashlib.sha256(raw).hexdigest()
   assert sha==sources[key]['sha256']==c['file_sha256'],(r['id'],name,key,'live source drift')
   item='\n'.join(raw.decode().splitlines()[c['line']-1:c['end_line']])
   entries.append(dict(key=key,path=str(p),file_sha256=sha,line=c['line'],end_line=c['end_line'],item=item))
  if f['class']=='D' or not candidates:unresolved.append(dict(function=name,reason=f.get('reason'),candidates=len(candidates)))
  if f['class'] in ['B','C']:
   checks.append(dict(function=name,source_class=f['class'],deployed_sources=entries,old_deployed_diff=f.get('diff'),same_body=f.get('body_bytes_identical'),same_item=f.get('item_bytes_identical'),status='NO COMPLETE DEPLOYED BODY LAW RECORDED',required='proved same law or restated complete Result law; source identity alone and finite validation do not discharge this'))
 record=dict(row=r['id'],status='SUSPENDED',source_class='B',gate='partial reached-source structural transfer preflight',changed_source_obligations=checks,unresolved_source_associations=unresolved,prior_residuals=r['residuals'],complete_structural_binding=False,restored=False,native_differential='separate optimized1.94.1 receipts; finite validation only',profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',artifact='devnet_spend; no SBF transfer')
 (D/(r['id']+'-source-gate.json')).write_text(json.dumps(record,indent=2)+'\n');out.append(dict(row=r['id'],changed_obligations=len(checks),unresolved_associations=len(unresolved),status='SUSPENDED'))
print(json.dumps(out,indent=2))
