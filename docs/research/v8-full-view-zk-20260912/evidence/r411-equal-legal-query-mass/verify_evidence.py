#!/usr/bin/env python3
"""Read-only verification of saved R411 source/build evidence."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[4]
TARGET=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R411EqualLegalQueryMass.lean'
FINAL='b209c043003f7d2b8d778f59693daf93c2c705201094a292765a9e8a372ec362'
RUNS={'1790962336539789000':(1,'0:01.16',3216300,'445c360637cda75d521ebb974c3fc35bc3e4ac21782d7c4c93bbc053d36c4220'),'1790962366555390000':(0,'0:01.33',3229980,FINAL)}
REPORTS={
 'rename_preimage':'[propext, Quot.sound]',
 'atom_mass_permutation':'[propext, Classical.choice, Quot.sound]',
 'equal_legal_atom_mass':'[propext, Classical.choice, Quot.sound]'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise AssertionError(msg)
norm=lambda x:' '.join(x.split())
req(sha(TARGET)==FINAL and sha(HERE/'R411EqualLegalQueryMass.lean')==FINAL,'promoted source hash mismatch')
req(TARGET.read_bytes()==(HERE/'R411EqualLegalQueryMass.lean').read_bytes(),'source copies differ')
for rid,(status,wall,rss,source_hash) in RUNS.items():
 stem='aspis-focus-'+rid;r=json.loads((HERE/'runs'/(stem+'.receipt.json')).read_text());log=(HERE/'runs'/(stem+'.log')).read_text()
 req(r['source_revision']=='e5f797a294ac11484f5b05038ae11cbe0eb637ca','source revision mismatch')
 req(r['source_sha256']==source_hash and sha(HERE/'runs'/(stem+'.source.lean'))==source_hash,'captured source mismatch')
 req(r['exit_status']==status and f'Exit status: {status}' in log,'status mismatch')
 req((r['wall_time'],r['peak_rss_kib'],r['swaps'])==(wall,rss,0),'metrics mismatch')
 req('Elapsed (wall clock) time (h:mm:ss or m:ss): '+wall in log and 'Maximum resident set size (kbytes): '+str(rss) in log and 'Swaps: 0' in log,'raw metrics mismatch')
 req(re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==r['complete_print_axioms'],'all raw axiom reports mismatch')
 req(r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'caps mismatch')
 req(r['runner_sha256']=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner receipt mismatch')
 if status:req('sorryAx' in log and any('sorryAx' in x for x in r['complete_print_axioms']),'failed attempt missing sorryAx evidence')
 else:
  expected=[f"'AspisV8R19.R411EqualLegalQueryMass.{n}' depends on axioms: {a}" for n,a in REPORTS.items()]
  req([norm(x) for x in r['complete_print_axioms']]==[norm(x) for x in expected],'complete axiom receipt mismatch')
  for x in expected:req(norm(x) in norm(log),'axiom missing from log')
  req('sorryAx' not in log,'sorryAx in successful log')
req(sha(HERE/'runner/run_focus.py')=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner copy mismatch')
cache=json.loads((HERE/'dependency-cache-identities.json').read_text())
req(cache['imports']['AspisV8R19.R409Q22Relabeling']['source_sha256']=='3e2b65983c6d0894d5d83ca06d69017a04875522bfb80070cc97818b435286e2','R409 supplemental hash mismatch')
req(sha(HERE/'dependencies/R409Q22Relabeling.lean')==cache['imports']['AspisV8R19.R409Q22Relabeling']['source_sha256'],'R409 dependency bytes mismatch')
req(sha(HERE/'mathlib-sources/Logic-Equiv-Fintype.lean')==cache['imports']['Mathlib.Logic.Equiv.Fintype']['source_sha256'],'Mathlib source mismatch')
files=json.loads((HERE/'FILES.json').read_text()); actual=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name not in {'FILES.json','SHA256SUMS'})
req(files['files']==actual,'FILES inventory mismatch')
rows=(HERE/'SHA256SUMS').read_text().splitlines()
for row in rows:
 d,rel=row.split('  ',1);p=HERE/rel
 req(rel!='SHA256SUMS' and p.is_file() and sha(p)==d,'checksum mismatch: '+rel)
req({x.split('  ',1)[1] for x in rows}=={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'},'SHA256SUMS incomplete')
print(json.dumps({'status':'pass','target_sha256':FINAL,'runs':list(RUNS),'complete_axiom_names':list(REPORTS),'foundation_union':['Classical.choice','Quot.sound','propext'],'checked_files':len(actual)+1},indent=2))
