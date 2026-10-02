#!/usr/bin/env python3
"""Portable, read-only integrity and saved-run checker for R372."""
from __future__ import annotations
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DOC_ROOT=ROOT.parent.parent
FOUNDATIONS={'propext','Classical.choice','Quot.sound'}
def sha(b:bytes)->str:return hashlib.sha256(b).hexdigest()
def load(r:str):return json.loads((ROOT/r).read_text())
def norm(s:str)->str:return ' '.join(s.split())
def main():
 failures=[]; sums=ROOT/'SHA256SUMS'; expected={}
 for line in sums.read_text().splitlines():
  h,r=line.split('  ',1);expected[r]=h
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p!=sums}
 if actual!=set(expected):failures.append('outer checksum path set differs')
 for r,h in expected.items():
  p=ROOT/r
  if not p.is_file() or sha(p.read_bytes())!=h:failures.append(f'outer checksum mismatch: {r}')
 inv=load('inventory.json')
 src=ROOT/inv['target']['evidence_copy']; target=DOC_ROOT/inv['target']['repository_path'].split('docs/research/v8-full-view-zk-20260912/',1)[1]
 if not src.is_file() or not target.is_file() or src.read_bytes()!=target.read_bytes():failures.append('promoted target differs from archived source')
 if sha(src.read_bytes())!=inv['target']['sha256']:failures.append('target SHA mismatch')
 for dep in inv['direct_dependencies']:
  d=ROOT/dep['evidence_copy']; dt=DOC_ROOT/dep['repository_path'].split('docs/research/v8-full-view-zk-20260912/',1)[1]
  if not d.is_file() or not dt.is_file() or d.read_bytes()!=dt.read_bytes():failures.append(f'direct dependency copy mismatch: {dep["module"]}')
  if sha(d.read_bytes())!=dep['sha256']:failures.append(f'direct dependency SHA mismatch: {dep["module"]}')
 if sha((ROOT/inv['runner']['path']).read_bytes())!=inv['runner']['sha256']:failures.append('runner SHA mismatch')
 for census_rel,checks in [("source-provenance/r372-source-column-cache-inventory",('inventory.json','source-files-excerpts.txt')),("source-provenance/r369-cross-target-law-source-census",('inventory.json','excerpts.md'))]:
  for f in checks:
   if not (ROOT/census_rel/f).is_file():failures.append(f'census file missing: {census_rel}/{f}')
 allgreen=[]
 expected_ids=['1790949064716018000','1790949125467117000']
 if [r['id'] for r in inv['runs']]!=expected_ids:failures.append('run IDs/order mismatch')
 for run in inv['runs']:
  source=ROOT/run['source'];log=ROOT/run['log'];rp=ROOT/run['receipt'];rec=json.loads(rp.read_text());text=log.read_text();st=source.read_text()
  if sha(source.read_bytes())!=run['source_sha256'] or sha(source.read_bytes())!=rec.get('source_sha256'):failures.append(f'source SHA mismatch: {run["id"]}')
  if sha(log.read_bytes())!=run['log_sha256']:failures.append(f'log SHA mismatch: {run["id"]}')
  for k in ('source_revision','exit_status','wall_time','peak_rss_kib','swaps','resources','measurement_boundary'):
   if rec.get(k)!=run.get(k):failures.append(f'receipt/inventory {k} mismatch: {run["id"]}')
  for dep in inv['direct_dependencies']:
   if rec.get('direct_local_import_sha256',{}).get(dep['module'])!=dep['sha256']:failures.append(f'import SHA mismatch {dep["module"]}: {run["id"]}')
  pats={'wall_time':r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)','peak_rss_kib':r'Maximum resident set size \(kbytes\): (\d+)','swaps':r'Swaps: (\d+)','exit_status':r'Exit status: (\d+)'}
  for k,p in pats.items():
   m=re.search(p,text);value=(m[1] if k=='wall_time' else int(m[1])) if m else None
   if value!=rec.get(k):failures.append(f'log/receipt {k} mismatch: {run["id"]}')
  if run['resources']!={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}:failures.append(f'resource caps mismatch: {run["id"]}')
  requests=re.findall(r'^#print axioms\s+(.+?)\s*$',st,re.M)
  reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)",text)
  if len(requests)!=len(reports):failures.append(f'axiom request/report count mismatch: {run["id"]}')
  for (name,raw),request in zip(reports,requests):
   if not(name==request or name.endswith('.'+request)):failures.append(f'axiom report name mismatch: {run["id"]}: {request}')
   axioms={x.strip() for x in raw.replace('\n',' ').split(',') if x.strip()}
   allowed=FOUNDATIONS if run['exit_status']==0 else FOUNDATIONS|{'sorryAx'}
   if not axioms<=allowed:failures.append(f'unexpected axiom output: {run["id"]}: {sorted(axioms-allowed)}')
  rec_reports=[norm(x) for x in rec.get('complete_print_axioms',[])]
  log_reports=[norm(m.group(0)) for m in re.finditer(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",text)]
  if rec_reports!=log_reports:failures.append(f'complete axiom outputs differ: {run["id"]}')
  if run['exit_status']==0:
   if run['id']!=inv['successful_run_id']:failures.append('unexpected successful run')
   if 'sorryAx' in '\n'.join(rec_reports):failures.append('sorryAx in green run')
   allgreen.extend(rec_reports)
  elif 'sorryAx' not in '\n'.join(rec_reports):failures.append(f'failed draft sorryAx history missing: {run["id"]}')
 note=DOC_ROOT/'R372_CURRENT_SOURCE_COLUMN_COMPATIBILITY.md'
 if not note.is_file() or sha(note.read_bytes())!=inv['release_note']['sha256']:failures.append('release note hash mismatch')
 if len(allgreen)!=5:failures.append(f'expected 5 green axiom reports; found {len(allgreen)}')
 print(json.dumps({'status':'PASS' if not failures else 'FAIL','checksummed_files':len(expected),'target_byte_identity':src.is_file() and target.is_file() and src.read_bytes()==target.read_bytes(),'runs':len(inv['runs']),'green_axiom_reports':len(allgreen),'failures':failures},indent=2))
 if failures:raise SystemExit(1)
if __name__=='__main__':main()
