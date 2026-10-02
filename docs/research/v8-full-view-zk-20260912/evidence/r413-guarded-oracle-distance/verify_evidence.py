#!/usr/bin/env python3
"""Read-only verification of saved R413 source/build evidence."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
TARGET=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R413GuardedOracleDistance.lean'
FINAL='f97e49e4fe955b2b51ad93a4a7fe6e6525a82b6ca6683bbff9da6ba54f8b7b0a'
RUNS={'1790962704763977000':(1,'0:01.45',3222636,'d098c7377c86e9b2d20f3149605726870203f429fd7e77886057f41118d23042'),'1790962808156955000':(0,'0:01.62',3237940,FINAL)}
NAMES=['mean_mono','mean_interval','mean_sub','abs_mean_le','independent_interval','lazy_interval','guarded_distance']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise AssertionError(msg)
norm=lambda s:' '.join(s.split())
req(sha(TARGET)==FINAL and sha(HERE/'R413GuardedOracleDistance.lean')==FINAL,'promoted source hash mismatch')
req(TARGET.read_bytes()==(HERE/'R413GuardedOracleDistance.lean').read_bytes(),'promoted/evidence source bytes differ')
for rid,(status,wall,rss,source_hash) in RUNS.items():
 stem='aspis-focus-'+rid;r=json.loads((HERE/'runs'/(stem+'.receipt.json')).read_text());log=(HERE/'runs'/(stem+'.log')).read_text()
 req(r['source_revision']=='bd58f59eb91a222a78753e9bc1f88890f3e7c4fd','revision mismatch')
 req(r['source_sha256']==source_hash and sha(HERE/'runs'/(stem+'.source.lean'))==source_hash,'captured source hash mismatch')
 req(r['exit_status']==status and f'Exit status: {status}' in log,'status mismatch')
 req((r['wall_time'],r['peak_rss_kib'],r['swaps'])==(wall,rss,0),'metrics mismatch')
 req(r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'caps mismatch')
 req(r['runner_sha256']=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner hash mismatch')
 req('Swaps: 0' in log,'swap evidence missing')
 req('Elapsed (wall clock) time (h:mm:ss or m:ss): '+wall in log and 'Maximum resident set size (kbytes): '+str(rss) in log,'raw metrics mismatch')
 req(re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==r['complete_print_axioms'],'all raw axiom reports mismatch')
 if status:req('sorryAx' in log and any('sorryAx' in a for a in r['complete_print_axioms']),'failed attempt should retain sorryAx')
 else:
  expected=[f"'AspisV8R19.R413GuardedOracleDistance.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in NAMES]
  req([norm(x) for x in r['complete_print_axioms']]==[norm(x) for x in expected],'complete axiom reports mismatch')
  for a in expected:req(norm(a) in norm(log),'axiom absent from log')
  req('sorryAx' not in log,'sorryAx in final log')
req(sha(HERE/'runner/run_focus.py')=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea','runner copy mismatch')
local='4f43200abc7ba91623e1957b99fadc0c1216f32e82e01785cd91f26983869612'
req(r['direct_local_import_sha256']=={'AspisV8R19.GuardedFirstRead':local},'receipt direct import map changed')
req(sha(HERE/'dependencies/GuardedFirstRead.lean')==local,'direct source dep hash mismatch')
cache=json.loads((HERE/'dependency-cache-identities.json').read_text())
req(cache['direct_imports']['AspisV8R19.GuardedFirstRead']['source_sha256']==local,'supplement source hash mismatch')
files=json.loads((HERE/'FILES.json').read_text()); actual=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name not in {'FILES.json','SHA256SUMS'})
req(files['files']==actual,'FILES inventory mismatch')
rows=(HERE/'SHA256SUMS').read_text().splitlines()
for row in rows:
 d,rel=row.split('  ',1);p=HERE/rel
 req(rel!='SHA256SUMS' and p.is_file() and sha(p)==d,'checksum mismatch '+rel)
req({x.split('  ',1)[1] for x in rows}=={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'},'SHA256SUMS incomplete')
print(json.dumps({'status':'pass','target_sha256':FINAL,'runs':list(RUNS),'complete_axiom_names':NAMES,'foundation_set':['Classical.choice','Quot.sound','propext'],'checked_files':len(actual)+1},indent=2))
