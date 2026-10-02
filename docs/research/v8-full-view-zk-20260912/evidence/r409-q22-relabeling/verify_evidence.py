#!/usr/bin/env python3
"""Read-only verification of saved R409 source/build evidence."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
TARGET=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R409Q22Relabeling.lean'
FINAL='3e2b65983c6d0894d5d83ca06d69017a04875522bfb80070cc97818b435286e2'
RUNS={
 '1790962119903304000':(1,'0:01.32',3222436,'f5ff3bb8b35287efc9ac18f6836ead77aab04c6fc83bbab67513a76186defb35'),
 '1790962175551116000':(0,'0:01.48',3235524,FINAL),
}
AXIOMS={
 'keep_rename':'[propext, Quot.sound]', 'scan_rename':'[propext, Quot.sound]', 'finish_rename':'[propext, Quot.sound]',
 'extend_value':'[propext, Classical.choice, Quot.sound]', 'block_values':'[propext, Classical.choice, Quot.sound]',
 'candidate_kernel_rename':'[propext, Classical.choice, Quot.sound]', 'empty_kernel_invariant':'[propext, Classical.choice, Quot.sound]'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise AssertionError(msg)
norm=lambda s:' '.join(s.split())
req(sha(TARGET)==FINAL,'promoted target SHA mismatch')
req(sha(HERE/'R409Q22Relabeling.lean')==FINAL and TARGET.read_bytes()==(HERE/'R409Q22Relabeling.lean').read_bytes(),'promoted/evidence bytes mismatch')
for rid,(status,wall,rss,source_hash) in RUNS.items():
 stem='aspis-focus-'+rid; r=json.loads((HERE/'runs'/(stem+'.receipt.json')).read_text()); log=(HERE/'runs'/(stem+'.log')).read_text()
 req(sha(HERE/'runs'/(stem+'.source.lean'))==source_hash and r['source_sha256']==source_hash,'captured source SHA mismatch '+rid)
 req(r['source_revision']=='8b05550c58481a43a9926a1c5b7b446d0711b67e','revision mismatch '+rid)
 req(r['exit_status']==status and f'Exit status: {status}' in log,'status mismatch '+rid)
 req((r['wall_time'],r['peak_rss_kib'],r['swaps'])==(wall,rss,0),'metrics mismatch '+rid)
 req(r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'resource cap mismatch '+rid)
 req(r['runner_sha256']=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner receipt mismatch '+rid)
 req('Swaps: 0' in log,'log swap mismatch '+rid)
 req('Elapsed (wall clock) time (h:mm:ss or m:ss): '+wall in log and 'Maximum resident set size (kbytes): '+str(rss) in log,'raw metrics mismatch '+rid)
 req(re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==r['complete_print_axioms'],'all raw axiom reports mismatch '+rid)
 if status:
  req(any('sorryAx' in x for x in r['complete_print_axioms']) and 'sorryAx' in log,'failed attempt should retain sorryAx')
 else:
  expected=[f"'AspisV8R19.R409Q22Relabeling.{n}' depends on axioms: {a}" for n,a in AXIOMS.items()]
  req([norm(x) for x in r['complete_print_axioms']]==[norm(x) for x in expected],'complete axiom receipt mismatch')
  for x in expected:req(norm(x) in norm(log),'axiom missing in successful log: '+x)
  req('sorryAx' not in log,'sorryAx in successful attempt')
req(sha(HERE/'runner/run_focus.py')=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner file mismatch')
cache=json.loads((HERE/'dependency-cache-identities.json').read_text())
req(cache['imports']['AspisV8R19.R407Q22CandidateKernel']['source_sha256']=='2fb00855b8588f9c40cc4de645abcdc2978a840cb38a76802330ca1b93050e89','R407 source hash metadata mismatch')
req(sha(HERE/'dependencies/R407Q22CandidateKernel.lean')==cache['imports']['AspisV8R19.R407Q22CandidateKernel']['source_sha256'],'R407 source bytes mismatch')
req(sha(HERE/'mathlib-sources/Logic-Equiv-Basic.lean')==cache['imports']['Mathlib.Logic.Equiv.Basic']['source_sha256'],'Mathlib source mismatch')
require_names=sorted(AXIOMS)
req(sorted(cache.get('complete_report_names',require_names))==require_names,'report name inventory mismatch')
files=json.loads((HERE/'FILES.json').read_text())
actual_sorted=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name not in {'FILES.json','SHA256SUMS'})
req(files['files']==actual_sorted,'FILES inventory mismatch')
rows=(HERE/'SHA256SUMS').read_text().splitlines()
for row in rows:
 digest,rel=row.split('  ',1); p=HERE/rel
 req(rel!='SHA256SUMS' and p.is_file() and sha(p)==digest,'checksum mismatch '+rel)
req({x.split('  ',1)[1] for x in rows}=={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'},'SHA256SUMS incomplete')
print(json.dumps({'status':'pass','target_sha256':FINAL,'runs':list(RUNS),'complete_axiom_names':require_names,'foundation_union':['Classical.choice','Quot.sound','propext'],'checked_files':len(actual_sorted)+1},indent=2))
