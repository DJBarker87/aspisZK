#!/usr/bin/env python3
"""Offline saved-evidence verifier for R381; performs no compilation."""
from __future__ import annotations
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROJECT=ROOT.parents[4]
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
EXPECTED_NAMES=["split_budget","localConstants_degree","branch_degrees","projected_degree","equality_degree","zerocheck_projected_degree"]
EXPECTED_FULL=[f"AspisR19.R381ProjectedPoseidonDegree.{n}" for n in EXPECTED_NAMES]
EXPECTED_CAPS={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok: raise SystemExit('FAIL: '+msg)
def norm(s):return ' '.join(s.split())
def parsed_axioms_text(text):
 out=[]
 for line in text:
  v=norm(line)
  m=re.fullmatch(r"'([^']+)' depends on axioms: \[(.*?)\]",v)
  if m: out.append((m.group(1),[x.strip() for x in m.group(2).split(',') if x.strip()])); continue
  m=re.fullmatch(r"'([^']+)' does not depend on any axioms",v)
  req(m is not None,'unrecognized saved axiom report: '+v)
  out.append((m.group(1),[]))
 return out

def parse_log(text):
 p=re.compile(r"^'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",re.M|re.S)
 out=[]
 for name,body in p.findall(text):
  out.append((name,[x.strip() for x in body.split(',') if x.strip()]))
 return out

inv=json.loads((ROOT/'inventory.json').read_text())
target=PROJECT/inv['target']['repository_path']; promoted=ROOT/inv['target']['copy']
req(target.is_file() and sha(target)==inv['target']['sha256'],'promoted target hash')
req(target.read_bytes()==promoted.read_bytes(),'target/source-copy identity')
req('import AspisV8R19.R377SelectorCoordinateDegree' in promoted.read_text() and 'import AspisV8R19.R380InternalFifthDegree' in promoted.read_text(),'direct imports')
runner=ROOT/inv['runner']['path']; req(sha(ROOT/runner)==inv['runner']['sha256'],'runner hash')

for d in inv['dependency_source_copies']:
 cp=ROOT/d['copy']; tr=PROJECT/d['repository_path']
 req(sha(cp)==d['sha256'] and sha(tr)==d['sha256'],'dependency copy/current source '+d['module'])
require_chain=[
 ('R381ProjectedPoseidonDegree.lean','import AspisV8R19.R377SelectorCoordinateDegree','promoted-source/R381ProjectedPoseidonDegree.lean'),
 ('R381ProjectedPoseidonDegree.lean','import AspisV8R19.R380InternalFifthDegree','promoted-source/R381ProjectedPoseidonDegree.lean'),
 ('R380InternalFifthDegree.lean','import AspisV8R19.R378PairedFifthDegree','dependencies/AspisV8R19/R380InternalFifthDegree.lean'),
 ('R378PairedFifthDegree.lean','import AspisV8R19.R376SimplePointDegree','dependencies/AspisV8R19/R378PairedFifthDegree.lean'),
 ('R376SimplePointDegree.lean','import AspisV8R19.R374SingleCoordinateDegree','dependencies/AspisV8R19/R376SimplePointDegree.lean'),
 ('R377SelectorCoordinateDegree.lean','import AspisV8R19.R374SingleCoordinateDegree','dependencies/AspisV8R19/R377SelectorCoordinateDegree.lean'),
 ('R374SingleCoordinateDegree.lean','import AspisV8R19.SourceStatementPoints','dependencies/AspisV8R19/R374SingleCoordinateDegree.lean')]
for _,needle,path in require_chain:req(needle in (ROOT/path).read_text(),'dependency import graph '+needle)
external=inv['external_import_source']; exp=ROOT/external['copy'];
req(sha(exp)==external['sha256']==external['expected_sha256'],'pinned external source copy')
req(external['mathlib_commit']=='9a04890da70b255c5e1b4da353fa697cf0dd3afe' and external['cache_rebuilt'] is False,'Mathlib provenance')
# Existing source facts are copied byte-identically from earlier evidence bundles.
r377=PROJECT/'docs/research/v8-full-view-zk-20260912/evidence/r377-selector-coordinate-degree'
r378=PROJECT/'docs/research/v8-full-view-zk-20260912/evidence/r378-paired-fifth-degree'
for dest,src in [
 ('source-provenance/selector-split-census.md',r377/'source-route/selector-split-census.md'),
 ('source-provenance/selector-split-manifest.json',r377/'source-route/selector-split-manifest.json'),
 ('source-provenance/paired-pow5-excerpt.rs',r378/'source-provenance/paired-pow5-excerpt.rs'),
 ('source-provenance/paired-pow5-source-manifest.json',r378/'source-provenance/source-excerpt.json')]:
 req((ROOT/dest).read_bytes()==src.read_bytes(),'source provenance copy identity '+dest)

req(len(inv['runs'])==3,'run count')
for record in inv['runs']:
 rid=record['id']; src=ROOT/record['source']; log=ROOT/record['log']; receipt_path=ROOT/record['receipt']; receipt=json.loads(receipt_path.read_text()); txt=log.read_text(errors='replace')
 req(sha(src)==record['source_sha256']==receipt['source_sha256'],'run source '+rid)
 req(sha(log)==record['log_sha256'] and sha(receipt_path)==record['receipt_sha256'],'run logs/receipt '+rid)
 req(receipt['source_revision']==record['source_revision'] and receipt['target']==record['target'],'run identity '+rid)
 req(receipt['runner_sha256']==inv['runner']['sha256'],'run runner '+rid)
 req(receipt['resources']==EXPECTED_CAPS==record['resources'],'run caps '+rid)
 req(receipt['direct_local_import_sha256']==record['direct_local_import_sha256'],'run import hash record '+rid)
 req(receipt['direct_local_import_sha256']=={
  'AspisV8R19.R377SelectorCoordinateDegree':inv['dependency_source_copies'][0]['sha256'],
  'AspisV8R19.R380InternalFifthDegree':inv['dependency_source_copies'][1]['sha256']},'direct local imports '+rid)
 req(receipt['exit_status']==record['exit_status'] and receipt['wall_time']==record['wall_time'] and receipt['peak_rss_kib']==record['peak_rss_kib'] and receipt['swaps']==record['swaps'],'receipt/index metrics '+rid)
 req(receipt['swaps']==0,'nonzero swap '+rid)
 req(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {receipt['wall_time']}" in txt,'raw wall '+rid)
 req(f"Maximum resident set size (kbytes): {receipt['peak_rss_kib']}" in txt,'raw RSS '+rid)
 req(f"Swaps: {receipt['swaps']}" in txt and f"Exit status: {receipt['exit_status']}" in txt,'raw status/swap '+rid)
 reports=parse_log(txt); expected=parsed_axioms_text(receipt['complete_print_axioms'])
 req(reports==expected,'complete raw axiom report comparison '+rid)
 req([name for name,_ in reports]==EXPECTED_FULL,'axiom request names/order '+rid)
 for theorem in EXPECTED_NAMES:req(f'#print axioms {theorem}' in src.read_text(),'source print request '+rid+'/'+theorem)
 if receipt['exit_status']==0:
  req(all(set(axs)==FOUNDATIONS for _,axs in reports),'green axiom whitelist '+rid)
  req('sorryAx' not in txt,'green sorryAx '+rid)
 else:
  req(receipt['exit_status']==1 and any('sorryAx' in axs for _,axs in reports),'failed draft classification '+rid)

success=next(x for x in inv['runs'] if x['id']==inv['successful_run_id'])
req(success['exit_status']==0 and success['wall_time']=='0:11.11' and success['peak_rss_kib']==4542884 and success['swaps']==0,'successful run metrics')
note=PROJECT/'docs/research/v8-full-view-zk-20260912'/inv['publication_note']; req(note.is_file() and sha(note)==inv['publication_note_sha256'],'publication note hash')
req(inv['first_remaining_proposition'].lower() in note.read_text().lower(),'first remaining proposition in note')
req(all('actual Rust' in b or 'No actual Rust' in b for b in inv['boundary'][-1:]),'source boundary metadata')
req(inv['no_rebuild'] is True,'cache/rebuild statement')
# Exact bundle inventory and checksums, excluding only the outer index itself.
cs=ROOT/'SHA256SUMS'; listed=set()
for line in cs.read_text().splitlines():
 if not line.strip():continue
 h,rel=line.split('  ',1);rel=rel.removeprefix('./');f=ROOT/rel
 req(f.is_file() and sha(f)==h,'bundle checksum '+rel);listed.add(rel)
actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p!=cs}
req(listed==actual,'outer inventory completeness')
print(json.dumps({'status':'PASS','runs':[(r['id'],r['exit_status'],r['wall_time'],r['peak_rss_kib'],r['swaps']) for r in inv['runs']],'theorems':EXPECTED_NAMES,'green_axioms':sorted(FOUNDATIONS),'files':len(actual)},indent=2))
