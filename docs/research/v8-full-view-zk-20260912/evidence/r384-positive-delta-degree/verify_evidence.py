#!/usr/bin/env python3
"""Offline integrity checker for the saved R384 evidence."""
from __future__ import annotations
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[4]
NOTE=PROJECT/'docs/research/v8-full-view-zk-20260912/R384_CURRENT_POSITIVE_DELTA_DEGREE.md'
FOUNDATIONS={'propext','Classical.choice','Quot.sound'}
THEOREMS=['residual_degree','rowSelector_degree','delta_degree']
FULL=[f'AspisR19.R384PositiveDeltaDegree.{n}' for n in THEOREMS]
CAPS={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise SystemExit('FAIL: '+msg)
def norm(s):return ' '.join(s.split())
def parse_log(s):
 p=re.compile(r"^'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",re.M|re.S)
 return [(n,[a.strip() for a in body.split(',') if a.strip()]) for n,body in p.findall(s)]
def parse_receipt(xs):
 out=[]
 for line in xs:
  v=norm(line);m=re.fullmatch(r"'([^']+)' depends on axioms: \[(.*?)\]",v)
  if m:out.append((m.group(1),[a.strip() for a in m.group(2).split(',') if a.strip()]));continue
  m=re.fullmatch(r"'([^']+)' does not depend on any axioms",v);req(m is not None,'receipt axiom format');out.append((m.group(1),[]))
 return out
inv=json.loads((ROOT/'inventory.json').read_text())
target=PROJECT/inv['target']['repository_path'];copy=ROOT/inv['target']['copy']
req(sha(target)==inv['target']['sha256'] and target.read_bytes()==copy.read_bytes(),'target identity/hash')
source=copy.read_text();req('import AspisV8R19.R381ProjectedPoseidonDegree' in source,'direct R381 import')
runner=ROOT/inv['runner']['path']; req(sha(ROOT/runner)==inv['runner']['sha256'],'runner checksum')
dep=inv['direct_import']; depfile=ROOT/dep['copy']; current=PROJECT/dep['repository_path']
req(sha(depfile)==dep['sha256']==sha(current),'direct R381 copy/current hash')
req(inv['direct_import']['sha256']=='39f90c474833cc54098ab2448b4b87919b6883119e74585488ed232dd3ee50e5','R381 compile-input checksum')
req(len(inv['runs'])==2,'two saved runs')
for r in inv['runs']:
 src=ROOT/r['source'];log=ROOT/r['log'];rp=ROOT/r['receipt'];receipt=json.loads(rp.read_text());txt=log.read_text(errors='replace')
 req(sha(src)==r['source_sha256']==receipt['source_sha256'],'source identity '+r['id'])
 req(sha(log)==r['log_sha256'] and sha(rp)==r['receipt_sha256'],'log/receipt hashes '+r['id'])
 req(receipt['target']==r['target'] and receipt['source_revision']==r['source_revision'],'target/revision '+r['id'])
 req(receipt['runner_sha256']==inv['runner']['sha256'],'run runner '+r['id'])
 req(receipt['resources']==CAPS==r['resources'] and receipt['swaps']==0==r['swaps'],'resource scope '+r['id'])
 req(receipt['direct_local_import_sha256']=={'AspisV8R19.R381ProjectedPoseidonDegree':dep['sha256']},'recorded direct import '+r['id'])
 req(receipt['exit_status']==r['exit_status'] and receipt['wall_time']==r['wall_time'] and receipt['peak_rss_kib']==r['peak_rss_kib'],'receipt metrics '+r['id'])
 req(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {r['wall_time']}" in txt,'GNU wall '+r['id'])
 req(f"Maximum resident set size (kbytes): {r['peak_rss_kib']}" in txt,'GNU RSS '+r['id'])
 req(f"Swaps: {r['swaps']}" in txt and f"Exit status: {r['exit_status']}" in txt,'GNU status/swap '+r['id'])
 reports=parse_log(txt);req(reports==parse_receipt(receipt['complete_print_axioms']),'full log/receipt axiom report '+r['id'])
 req([n for n,_ in reports]==FULL,'exact axiom theorem names '+r['id'])
 for n in THEOREMS:req(f'#print axioms {n}' in src.read_text(),'missing axiom request '+n+'/'+r['id'])
 if r['exit_status']==0:
  req(all(set(axs)==FOUNDATIONS for _,axs in reports),'green axiom whitelist')
  req('sorryAx' not in txt,'green sorryAx')
 else:
  req(r['id']==inv['failed_run_id'] and any('sorryAx' in axs for _,axs in reports),'failed draft history classification')
req(NOTE.is_file() and sha(NOTE)==inv['publication_note_sha256'],'publication note checksum')
req(inv['first_remaining_proposition'].lower() in NOTE.read_text().lower(),'first remaining proposition')
req(inv['no_rebuild'] is True,'no-rebuild record')
cs=ROOT/'SHA256SUMS';listed=set()
for line in cs.read_text().splitlines():
 if not line.strip():continue
 h,rel=line.split('  ',1);rel=rel.removeprefix('./');p=ROOT/rel
 req(p.is_file() and sha(p)==h,'bundle file hash '+rel);listed.add(rel)
actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p!=cs}
req(listed==actual,'bundle file inventory')
print(json.dumps({'status':'PASS','runs':[(r['id'],r['exit_status'],r['wall_time'],r['peak_rss_kib'],r['swaps']) for r in inv['runs']],'theorems':THEOREMS,'green_axioms':sorted(FOUNDATIONS),'files':len(actual)},indent=2))
