from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-cpilot-20261028'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
names=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates','programs'],text=True).splitlines()
frozen={n:hashlib.sha256(subprocess.check_output(['git','show',rev+':'+n])).hexdigest() for n in names}
rows=[json.loads(l) for l in (E/'NCO_ATTEMPTS.jsonl').read_text().splitlines()]
x=dict(B=B,frozen=frozen,attempts=[r['attempt'] for r in rows])
code='''from pathlib import Path
import json,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NCO_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
changed={};missing=[]
for n,h in x['frozen'].items():
 p=s/n
 if not p.is_file():missing.append(n)
 elif sha(p)!=h:changed[n]=dict(sha256=sha(p),text=p.read_text())
pinsets={};source_snapshots={}
for a in x['attempts']:
 p=b/a/'sources/NCO_SOURCE_PINS.json'
 if p.is_file():pinsets[sha(p)]=p.read_text()
 # Retain exact scratch-only instrumentation as patches, not raw shipped source copies.
 d={}
 for n in ['crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/compact.rs']:
  p=b/a/'sources/NCO_src'/n
  if p.is_file():d[n]=p.read_text()
 source_snapshots[a]=d
p=b/'NCO_reference.llbc'
print(json.dumps(dict(frozen_files=len(x['frozen']),changed=changed,missing=missing,pinsets=pinsets,sources=source_snapshots,llbc=p.read_text(),backend_matches={n:(b/n).read_bytes()==(b.parent/'codex-cx-sound-int2-20261025'/n).read_bytes() for n in ['S2W_run_host.py','S2W_lean_host.py']})))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);texts=x.pop('changed');pinsets=x.pop('pinsets');snapshots=x.pop('sources');llbc=x.pop('llbc')
for h,t in pinsets.items():(E/('NCO_PINSET_'+h[:20]+'.json')).write_text(t)
# Every final changed shipped-path file gets its full exact diff against the frozen source.
patch=[]
for n,v in texts.items():
 original=subprocess.check_output(['git','show',rev+':'+n],text=True)
 patch.extend(difflib.unified_diff(original.splitlines(True),v['text'].splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NCO_SCRATCH.patch').write_text(''.join(patch)+(E/'NCO_harness.patch').read_text())
# Earlier per-attempt exact instrumentation, deduplicated by its own patch hash.
variants={};uses={}
for a,files in snapshots.items():
 diff=[]
 for n,t in files.items():
  original=subprocess.check_output(['git','show',rev+':'+n],text=True)
  diff.extend(difflib.unified_diff(original.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 t=''.join(diff);h=hashlib.sha256(t.encode()).hexdigest();variants[h]=t;uses[a]=h
for h,t in variants.items():(E/('NCO_INSTRUMENT_'+h[:20]+'.patch')).write_text(t)
x['changed']={n:v['sha256'] for n,v in texts.items()};x['instrumentation_by_attempt']=uses
(E/'NCO_FROZEN_SOURCE_AUDIT.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'NCO_E006.llbc').write_text(llbc)
print(json.dumps(dict(frozen_files=x['frozen_files'],changed=list(texts),missing=x['missing'],pinsets=len(pinsets),instrumentation_variants=len(variants),backends=x['backend_matches'])))
