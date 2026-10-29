from NEF_host import *
import sys,os
attempt,kind,target=sys.argv[1:]
assert attempt.startswith('NEF_')
limit={'kani':40,'lean':40,'extract':10,'inspect':100}
old=[json.loads(l) for l in (E/'NEF_ATTEMPTS.jsonl').read_text().splitlines()] if (E/'NEF_ATTEMPTS.jsonl').exists() else []
assert sum(x['kind']==kind for x in old)<limit[kind]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEF_tmp')
files={};deps={}
if kind=='kani':
 for n in ['NEF_gate.py','NEF_graph.py']:files[n]=(E/n).read_text()
 command=['python3','NEF_gate.py',attempt+'.json']
 ni=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEF_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NEF_target','--lib','--features','private-leaf-salts,optimized-terminal,program-build','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--keep-temps','--output-format','regular']
 ni+=json.loads(os.environ.get('NEF_KANI_ARGS','[]'))
 sources=['NEF_src/'+n for n in json.loads((E/'NEF_SCRATCH_PINS.json').read_text())]+list(files)
elif kind=='lean':
 files['NEF_generated/'+target+'.lean']=(E/(target+'.lean')).read_text()
 env['LEAN_PATH']=B+'/NEF_objects:/home/dombarker/project-offloads/codex-cx-slice-q-fnptr-cache-20261029:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'
 command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NEF_generated','-o','NEF_objects/'+target+'.olean','NEF_generated/'+target+'.lean']
 sources=list(files);ni=[]
else:
 files[target]=(E/target).read_text();command=['python3',target];sources=list(files);ni=[]
admit(attempt+'_INPUT')
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NEF_objects').mkdir(exist_ok=True)
if {kind!r}=='kani':
 p=b/'NEF_src';pins={{str(q.relative_to(p)):hashlib.sha256(q.read_bytes()).hexdigest() for q in p.rglob('*') if q.is_file() and q.suffix in ['.rs','.toml','.lock']}}
 (b/'NEF_SOURCE_PINS.json').write_text(json.dumps(pins))
print('uploaded')
''');assert r.returncode==0,r.stderr
cfg=dict(attempt=attempt,kind=kind,module=target,sources=sources,command=command,native_command=ni,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=deps,expected_time='Optimized compilation then one native diagnostic; no field multiplication' if kind=='kani' else 'Focused elaboration' if kind=='lean' else 'Source and GOTO inspection only')
if kind=='lean':
 # Pin every object reachable in the selected Aeneas library and every direct imported object.
 r=py(f'''from pathlib import Path
import hashlib,json
roots={env['LEAN_PATH'].split(':')!r};out={{}}
lib=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/.lake/packages/aeneas')
for root in [lib]:
 for p in root.rglob('*'):
  if p.is_file() and (p.suffix in ['.olean','.ir'] or '.olean.' in p.name):out[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
for line in {files[sources[0]]!r}.splitlines():
 if not line.startswith('import '):continue
 for m in line[7:].split():
  if m in ['Init','Std']:continue
  key=m.replace('.','/')+'.olean';p=next((Path(r)/key for r in roots if (Path(r)/key).exists()),None);assert p is not None,m
  for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if q.is_file():out[str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
 cfg['deps_fingerprint']['selected_objects']=json.loads(r.stdout)
r=launch(cfg)
if kind=='kani':
 q=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in [{(attempt+'-graph-check.json')!r},{(attempt+'-source-check.json')!r},{(attempt+'-graph.stderr')!r},{(attempt+'-lock-check.json')!r}] if (b/n).exists()}}))
''');assert q.returncode==0,q.stderr
 for n,t in json.loads(q.stdout).items():(E/n).write_text(t)
