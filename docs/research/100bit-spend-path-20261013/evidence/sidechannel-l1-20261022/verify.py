#!/usr/bin/env python3
"""Validate final focused proof receipts; does not claim native refinement."""
from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'.git').exists())
LEAN=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'
FINAL={'SideChannelL1AttemptRecord':9877,'SideChannelRetryLaw':9878,
       'SideChannelEntropy':9869,'SideChannelEntropyLaw':9872,
       'SideChannelL1JointCoupling':9879,'SideChannelL1Audit':9880}
BASE='83554aa91'
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def axiom_lines(log):
 return [' '.join(s.split()) for s in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",log,re.M|re.S)]
allowed={'propext','Classical.choice','Quot.sound'}
records=[]; names=[]
objects=json.loads((HERE/'object-pins.json').read_text())['objects']
for mod,attempt in FINAL.items():
 meta=json.loads((HERE/f'attempt-{attempt}.json').read_text())
 assert meta['exit']==0,(mod,meta['errors'])
 for dep,sha in meta['deps'].items():
  assert objects[dep]['sha256']==sha,(mod,dep,'changed since compile')
 assert meta['source_sha256']==digest(LEAN/f'{mod}.lean')
 assert meta['source_sha256']==digest(HERE/'sources'/f'{attempt}-{mod}.lean.txt')
 assert meta['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64}
 log=(HERE/f'out-{attempt}.log').read_text(); axioms=axiom_lines(log)
 for line in axioms:
  if 'depends on axioms:' in line:
   used=set(line.split('[',1)[1].rstrip(']').replace(',',' ').split())
   assert used<=allowed,(mod,used)
 source=(LEAN/f'{mod}.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',source)
 names += [f'R1Z.{mod}.{name}' for name in re.findall(r'^theorem (\w+)',source,re.M)]
 records.append({'module':mod,'attempt':attempt,'source_sha256':meta['source_sha256'],
  'deps_fingerprint':meta['deps_fingerprint'],'source_revision':meta['source_revision'],
  'exit':meta['exit'],'time_fields':meta['time_fields'],'axioms':axioms})
audit=(HERE/'out-9880.log').read_text()
for name in names:
 assert f"'{name}' " in audit,name
changed=subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT,text=True).splitlines()
for path in changed:
 assert path.startswith('docs/research/100bit-spend-path-20261013/evidence/sidechannel-l1-20261022/') or path=='docs/research/v8-r0-zk-20261009/r1p-final/SIDE-CHANNEL-L1-20261022.md' or re.fullmatch(r'docs/research/v8-r0-zk-20261009/lean/R1Z/SideChannel\w+\.lean',path),path
inventory=json.loads((HERE/'source-map.json').read_text())
for pin in inventory['files']:
 assert digest(ROOT/pin['path'])==pin['sha256']
raw_white=subprocess.run(['git','diff','--check',BASE],cwd=ROOT,capture_output=True,text=True)
white=subprocess.run(['git','diff','--check',BASE,'--','.',':!**/*.log'],cwd=ROOT,capture_output=True,text=True)
assert white.returncode==0,white.stdout+white.stderr
summary={'status':'focused-model-proofs-pass; native L1 target NOT established',
         'final':records,'audited_theorems':names,'final_audit_attempt':9880,
         'release_replay':False,'native_event_refinement':False,'native_joint_coupling':False,
         'source_pin_check':True,'allowed_file_check':True,'git_diff_check_excluding_raw_logs':white.returncode,
         'raw_log_whitespace':{'exit':raw_white.returncode,'output':raw_white.stdout+raw_white.stderr,
                               'policy':'preserve raw Lean diagnostic bytes, including blank-space lines'},
         'shipped_sources_changed':False,'frozen_ELF_rebuild_triggered':False,
         'notes':['Failed attempts retained and excluded from final proof set.',
                  'External env-J imports use existing cached build evidence; no release closure replay claimed.',
                  'No new cryptographic/runtime trust premise installed.']}
(HERE/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'status':summary['status'],'audited_theorems':len(names),'final_modules':len(FINAL)},indent=2))
