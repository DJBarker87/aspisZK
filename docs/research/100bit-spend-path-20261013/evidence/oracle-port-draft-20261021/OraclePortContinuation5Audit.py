#!/usr/bin/env python3
"""Audit continuation-five focused receipts; do not recompile any theorem."""
import hashlib,json,pathlib,re,subprocess
here=pathlib.Path(__file__).resolve().parent
root=here.parents[4]
base=root/'docs/research/100bit-spend-path-20261013'
modules=['OraclePortSelectedRowObstructionC5','OraclePortCheckpointAbiC5',
 'OraclePortCheckpointSlicesC5','OraclePortCheckpointResumeC5',
 'OraclePortCheckpointPreparedC5','OraclePortCheckpointOracleC5']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]; final=[]; seen=set()
allowed={'propext','Classical.choice','Quot.sound'}
for module in modules:
 attempts=sorted(here.glob(module+'-*/receipt.json'),key=lambda p:int(p.parent.name.rsplit('-',1)[1]))
 assert attempts,module
 for file in attempts:
  r=json.loads(file.read_text());out=file.parent
  assert r['source_sha256']==sha(out/'source.lean')
  assert r['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
  assert r['lean_path'].split(':')[0]=='/tmp/codex-cx-oracle-port-draft-20261021-objects'
  for k in ['source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']:
   assert k in r,(module,k)
  assert r['swaps']==0
  key=(module,r['source_sha256'],r['deps_fingerprint']);assert key not in seen;seen.add(key)
  log=(out/'lean.log').read_text()
  reports=re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log)
  assert reports==r['axioms']
  if r['exit']==0:
   assert not r['errors']
   for report in reports:
    used=set(re.findall(r'\b(?:[A-Za-z][A-Za-z0-9_]*\.)*[A-Za-z][A-Za-z0-9_]*\b',report.split('depends on axioms: [')[-1])) if 'depends on axioms: [' in report else set()
    assert used<=allowed,(module,used)
  receipts.append(r)
 r=json.loads(attempts[-1].read_text());source=base/'lean'/f'{module}.lean'
 assert r['exit']==0 and r['source_sha256']==sha(source)
 for imp in r['direct_imports']:
  assert sha(pathlib.Path(imp['path']))==imp['sha256'],imp
 text=source.read_text()
 theorem_names=re.findall(r'^theorem\s+(\w+)',text,re.M)
 for name in theorem_names:
  assert f'#print axioms {name}' in text,(module,name)
  assert any(f'.{name}\'' in a for a in r['axioms']),(module,name)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|sorryAx|maxRecDepth|maxHeartbeats)\b',text)
 final.append({'module':module,'source_sha256':sha(source),'attempt':r['attempt'],
  'axioms':r['axioms'],'theorems':len(theorem_names)})
changed=subprocess.check_output(['git','diff','--name-status','03cae1909','--','docs/research/100bit-spend-path-20261013/lean'],cwd=root,text=True)
for line in changed.splitlines():
 status,path=line.split('\t');assert status=='A' and pathlib.Path(path).stem in modules,line
oldpath='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessBinPerQueryR19.lean'
old=subprocess.check_output(['git','show','03cae1909:'+oldpath],cwd=root)
assert old==(root/oldpath).read_bytes()
assert (here/'OraclePortC5-existing-headline-signature.diff').read_text()==''
assert (here/'OraclePortC5-v2-signature.diff').read_text()==''
result={'schema':'focused-extractor-proof-packet-v1','base_revision':'03cae1909',
 'attempt_count':len(receipts),'successful_final_modules':len(final),
 'successful_final_axiom_reports':sum(len(m['axioms']) for m in final),
 'peak_rss_bytes':max(r['peak_rss_bytes'] for r in receipts),'swaps':0,
 'headline_premise_deletions':0,'completed_frozen_dV':False,
 'headline_comparison_revision':'4f3df75f58b1b4f9ea9d26139a1ab46990bef7bb',
 'final_modules':final,'attempts':receipts}
(here/'OraclePortContinuation5Manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['attempt_count','successful_final_modules','successful_final_axiom_reports','peak_rss_bytes','swaps','headline_premise_deletions']}))
