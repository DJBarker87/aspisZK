#!/usr/bin/env python3
"""Portable, read-only integrity and saved-run checker for R370."""
from __future__ import annotations
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DOC_ROOT=ROOT.parent.parent
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
def sha(b:bytes)->str:return hashlib.sha256(b).hexdigest()
def load(rel:str):return json.loads((ROOT/rel).read_text())
def norm(s:str)->str:return " ".join(s.split())
def main():
 failures=[]
 sums=ROOT/'SHA256SUMS'; expected={}
 for line in sums.read_text().splitlines():
  h,r=line.split('  ',1); expected[r]=h
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p!=sums}
 if actual!=set(expected):failures.append('outer checksum path set differs')
 for r,h in expected.items():
  p=ROOT/r
  if not p.is_file() or sha(p.read_bytes())!=h:failures.append(f'outer checksum mismatch: {r}')
 inv=load('inventory.json')
 source=ROOT/inv['target']['evidence_copy']
 target=DOC_ROOT/inv['target']['repository_path'].split('docs/research/v8-full-view-zk-20260912/',1)[1]
 if not source.is_file() or not target.is_file() or source.read_bytes()!=target.read_bytes():failures.append('promoted target differs from archived source')
 if sha(source.read_bytes())!=inv['target']['sha256']:failures.append('target source SHA mismatch')
 dep=ROOT/inv['dependency']['evidence_copy']
 deptarget=DOC_ROOT/inv['dependency']['repository_path'].split('docs/research/v8-full-view-zk-20260912/',1)[1]
 if not dep.is_file() or not deptarget.is_file() or dep.read_bytes()!=deptarget.read_bytes():failures.append('direct dependency differs from archived/promoted source')
 if sha(dep.read_bytes())!=inv['dependency']['sha256']:failures.append('dependency SHA mismatch')
 if sha((ROOT/inv['runner']['path']).read_bytes())!=inv['runner']['sha256']:failures.append('runner SHA mismatch')
 prov=load(inv['source_provenance'])
 cache=ROOT/prov['r370_cache_inventory']['path']
 r369=ROOT/prov['r369_cfg_and_cross_target_source_census']['path']
 if sha((cache/'source-excerpts.txt').read_bytes())!=prov['r370_cache_inventory']['source_excerpt_sha256']:failures.append('R370 source excerpt SHA mismatch')
 if sha((r369/'inventory.json').read_bytes())!=prov['r369_cfg_and_cross_target_source_census']['inventory_sha256']:failures.append('R369 inventory SHA mismatch')
 if sha((r369/'excerpts.md').read_bytes())!=prov['r369_cfg_and_cross_target_source_census']['excerpts_sha256']:failures.append('R369 excerpts SHA mismatch')
 allgreen=[]; ids=['1790948886769044000','1790948921888089000','1790948960291744000']
 if [r['id'] for r in inv['runs']]!=ids:failures.append('run IDs/order differ')
 for run in inv['runs']:
  src=ROOT/run['source']; log=ROOT/run['log']; recp=ROOT/run['receipt']; receipt=json.loads(recp.read_text()); text=log.read_text(); st=src.read_text()
  if sha(src.read_bytes())!=run['source_sha256'] or sha(src.read_bytes())!=receipt.get('source_sha256'):failures.append(f'source SHA mismatch: {run["id"]}')
  if sha(log.read_bytes())!=run['log_sha256']:failures.append(f'log SHA mismatch: {run["id"]}')
  for k in ('source_revision','exit_status','wall_time','peak_rss_kib','swaps','resources','measurement_boundary'):
   if receipt.get(k)!=run.get(k):failures.append(f'receipt/inventory {k} mismatch: {run["id"]}')
  if receipt.get('direct_local_import_sha256',{}).get('AspisV8R19.FullCoefficientBoundary')!=inv['dependency']['sha256']:failures.append(f'direct import SHA mismatch: {run["id"]}')
  patterns={'wall_time':r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)','peak_rss_kib':r'Maximum resident set size \(kbytes\): (\d+)','swaps':r'Swaps: (\d+)','exit_status':r'Exit status: (\d+)'}
  for k,pat in patterns.items():
   m=re.search(pat,text); val=(m[1] if k=='wall_time' else int(m[1])) if m else None
   if val!=receipt.get(k):failures.append(f'raw log/receipt {k} mismatch: {run["id"]}')
  if run['resources']!={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}:failures.append(f'resource cap mismatch: {run["id"]}')
  requests=re.findall(r'^#print axioms\s+(.+?)\s*$',st,re.M)
  reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)",text)
  if len(requests)!=3 or len(reports)!=len(requests):failures.append(f'axiom request/report count mismatch: {run["id"]}')
  for (name,raw),request in zip(reports,requests):
   if not (name==request or name.endswith('.'+request)):failures.append(f'axiom report name mismatch: {run["id"]}: {request}')
   axioms={x.strip() for x in raw.replace('\n',' ').split(',') if x.strip()}
   allowed=FOUNDATIONS if run['exit_status']==0 else FOUNDATIONS|{'sorryAx'}
   if not axioms<=allowed:failures.append(f'unexpected axiom set: {run["id"]}: {sorted(axioms-allowed)}')
  rec_reports=[norm(x) for x in receipt.get('complete_print_axioms',[])]
  log_reports=[norm(m.group(0)) for m in re.finditer(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",text)]
  if rec_reports!=log_reports:failures.append(f'complete reports differ between receipt/log: {run["id"]}')
  if run['exit_status']==0:
   if run['id']!=inv['successful_run_id']:failures.append('unexpected green run ID')
   if 'sorryAx' in '\n'.join(rec_reports):failures.append('sorryAx in green axiom output')
   allgreen.extend(rec_reports)
  elif 'sorryAx' not in '\n'.join(rec_reports):failures.append(f'rejected draft sorryAx trail missing: {run["id"]}')
 note=DOC_ROOT/'R370_CURRENT_KERNEL_EVALUATION.md'
 if not note.is_file() or sha(note.read_bytes())!=inv['release_note']['sha256']:failures.append('note hash mismatch')
 if len(allgreen)!=3:failures.append(f'expected 3 green axiom reports, found {len(allgreen)}')
 print(json.dumps({'status':'PASS' if not failures else 'FAIL','checksummed_files':len(expected),'target_byte_identity':source.is_file() and target.is_file() and source.read_bytes()==target.read_bytes(),'runs':len(inv['runs']),'green_axiom_reports':len(allgreen),'failures':failures},indent=2))
 if failures:raise SystemExit(1)
if __name__=='__main__':main()
