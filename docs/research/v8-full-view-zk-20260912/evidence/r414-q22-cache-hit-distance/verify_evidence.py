#!/usr/bin/env python3
"""Read-only verification of saved R414 source/build evidence."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
TARGET=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R414Q22CacheHitDistance.lean'
FINAL='a3ba0367f49a02a07bad714172147e1198f81e48a282fc3e844fc1af18b19bd3'
RID='1790963324576809000'
NAMES=['loop_distance','challenge_distance']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise AssertionError(msg)
norm=lambda s:' '.join(s.split())
req(sha(TARGET)==FINAL and sha(HERE/'R414Q22CacheHitDistance.lean')==FINAL,'promoted hash mismatch')
req(TARGET.read_bytes()==(HERE/'R414Q22CacheHitDistance.lean').read_bytes(),'promoted/evidence bytes differ')
stem='aspis-focus-'+RID;r=json.loads((HERE/'runs'/(stem+'.receipt.json')).read_text());log=(HERE/'runs'/(stem+'.log')).read_text()
req(r['source_revision']=='8cc8d0a78a6137c2e83e19f320dc04e9ed2fc17b','source revision mismatch')
req(r['source_sha256']==FINAL and sha(HERE/'runs'/(stem+'.source.lean'))==FINAL,'snapshot SHA mismatch')
req(r['exit_status']==0 and 'Exit status: 0' in log and 'sorryAx' not in log,'run not green')
req((r['wall_time'],r['peak_rss_kib'],r['swaps'])==('0:01.28',3225496,0),'metrics mismatch')
req('Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.28' in log and 'Maximum resident set size (kbytes): 3225496' in log and 'Swaps: 0' in log,'raw metrics mismatch')
req(re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==r['complete_print_axioms'],'all raw axiom reports mismatch')
req(r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'caps mismatch')
runner='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea'
req(r['runner_sha256']==runner and sha(HERE/'runner/run_focus.py')==runner,'runner mismatch')
expected=[f"'AspisV8R19.R414Q22CacheHitDistance.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in NAMES]
req([norm(x) for x in r['complete_print_axioms']]==[norm(x) for x in expected],'full axiom reports mismatch')
for x in expected:req(norm(x) in norm(log),'axiom absent from log')
local={'AspisV8R19.R413GuardedOracleDistance':'f97e49e4fe955b2b51ad93a4a7fe6e6525a82b6ca6683bbff9da6ba54f8b7b0a','AspisV8R19.R407Q22CandidateKernel':'2fb00855b8588f9c40cc4de645abcdc2978a840cb38a76802330ca1b93050e89'}
req(r['direct_local_import_sha256']==local,'receipt import map mismatch')
cache=json.loads((HERE/'dependency-cache-identities.json').read_text())
for name,h in local.items():
 req(sha(HERE/'dependencies'/(name.split('.')[-1]+'.lean'))==h,'dependency source mismatch '+name)
 req(cache['direct_imports'][name]['source_sha256']==h,'supplemental source hash mismatch '+name)
files=json.loads((HERE/'FILES.json').read_text());actual=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name not in {'FILES.json','SHA256SUMS'})
req(files['files']==actual,'FILES inventory mismatch')
rows=(HERE/'SHA256SUMS').read_text().splitlines()
for row in rows:
 d,rel=row.split('  ',1);p=HERE/rel
 req(rel!='SHA256SUMS' and p.is_file() and sha(p)==d,'checksum mismatch '+rel)
req({x.split('  ',1)[1] for x in rows}=={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'},'SHA256SUMS incomplete')
print(json.dumps({'status':'pass','target_sha256':FINAL,'run':RID,'complete_axiom_names':NAMES,'foundation_set':['Classical.choice','Quot.sound','propext'],'checked_files':len(actual)+1},indent=2))
