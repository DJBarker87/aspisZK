#!/usr/bin/env python3
"""Audit every focused attempt and the sole, strictly weaker signature replacement."""
import difflib,hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKET=HERE.parents[1]
ROOT=PACKET.parents[2]
BASE='bfa31ed06'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def signature(s):
 a=s.index('theorem final_soundness');return s[a:s.index(' := by',a)]+'\n'
before=signature((PACKET/'lean/R1FinalSoundnessBinPerQueryR19.lean').read_text())
after=signature((PACKET/'lean/R1FinalSoundnessBinPerQueryRWire.lean').read_text())
old='(h_Rwire : BoundaryEvidence s → BinaryCompletion D d P (Q + 1161))'
new='(h_Rwire_tag : BoundaryEvidence s → RWireCompletion.InitialTag D d P (Q + 1161))'
assert before.replace(old,new)==after
for name,s in [('before',before),('after',after)]:
 assert (HERE/(name+'-statement.lean.txt')).read_text()==s
 assert s.rstrip() in (PACKET/'design/RWIRE-20261021.md').read_text()
assert (HERE/'signature.diff').read_text()==''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='R19.final_soundness',tofile='RWire.final_soundness'))
data=json.loads((HERE/'manifest.json').read_text());assert data['schema']=='focused-extractor-proof-packet-v1'
accepted=[a for a in data['attempts'] if a['final_current']]
modules={a['module'] for a in accepted}
expected={p.stem for p in (PACKET/'lean').glob('RWire*.lean')}|{'R1FinalSoundnessBinPerQueryRWire'}
assert modules==expected,(modules^expected)
reports=0
for a in data['attempts']:
 folder=HERE/(a['module']+'-'+str(a['attempt']))
 assert a==json.loads((folder/'receipt.json').read_text())
 assert all(a[k]==v for k,v in json.loads((folder/'command.json').read_text()).items())
 assert sha(folder/'source.lean.txt')==a['source_sha256']
 assert a['deps_fingerprint']==hashlib.sha256(json.dumps(a['direct_imports'],sort_keys=True).encode()).hexdigest()
 for key in ['source_revision','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors']: assert key in a
 if not a['final_current']: continue
 assert a['exit']==0 and not a['errors']
 source=PACKET/'lean'/(a['module']+'.lean'); assert sha(source)==a['source_sha256']
 code=source.read_text()
 names=re.findall(r'^(?:private )?(?:@\[[^\n]+\] )?theorem (\w+)',code,re.M)
 audits=re.findall(r'^#print axioms (\w+)',code,re.M)
 assert set(names)==set(audits),(a['module'],set(names)^set(audits))
 assert len(audits)==len(a['axioms'])
 for name in names:
  assert any(a['module']+'.'+name+"'" in line for line in a['axioms'])
 for line in a['axioms']:
  assert line in (folder/'lean.log').read_text()
  if 'depends on axioms:' in line:
   assert set(re.findall(r'[\w.]+',line.split('[',1)[1]))<=ALLOWED,line
  else: assert 'does not depend on any axioms' in line
  reports+=1
 stripped=re.sub(r'/\-.*?\-/','',code,flags=re.S);stripped=re.sub(r'--[^\n]*','',stripped)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',stripped)
 for dep in a['direct_imports']:
  assert sha(dep['path'])==dep['sha256']
  candidates=[Path(p)/(dep['module'].replace('.','/')+'.olean') for p in a['lean_path'].split(':')]
  assert next(str(p) for p in candidates if p.exists())==dep['path']
 obj=Path(a['argv'][a['argv'].index('-o')+1]);assert sha(obj)==a['object_sha256'] and obj.stat().st_size==a['object_size']
 assert a['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
 assert a['lean_path'].split(':')[0]==str(obj.parent)
changes=subprocess.check_output(['git','diff',BASE,'--name-status'],cwd=ROOT,text=True).splitlines()
assert all(s.startswith('A\t') for s in changes),changes
assert not any(s.endswith(('.olean','.tar','.gz','.elf')) for s in changes)
result=dict(status='PASS',base=BASE,scope='Focused cached-object proof evidence, not coherent frozen release replay',accepted_modules=len(accepted),axiom_reports=reports,total_attempts=len(data['attempts']),failed_attempts=sum(a['exit']!=0 for a in data['attempts']),sole_signature_change=dict(before=old,after=new),strictness_theorems=['RWireCompletion.initialTag_of_completion','RWireCounterexamples.strict_weakening'],existing_files_unchanged=True,peak_rss_bytes=max(a['peak_rss_bytes'] for a in data['attempts']),swaps=sum(a['swaps'] for a in data['attempts']),final_compile_wall_seconds=sum(a['wall_seconds'] for a in accepted))
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
