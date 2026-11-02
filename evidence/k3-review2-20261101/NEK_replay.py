"""Own receipt replay: frozen bodies + retained harness patch, no shared writes."""
from NEK_host import *
from NEK_scan import patched_files,FROZEN,sha
import sys,lzma,re,os
ROOT=E.parents[1]
def seed():
 # Replace only Rust sources in our existing scratch; preserve the frozen lock.
 names=subprocess.check_output(['git','ls-tree','-r','--name-only',FROZEN],text=True).splitlines()
 files={n:subprocess.check_output(['git','show',FROZEN+':'+n]).decode() for n in names if n.startswith(('crates/','programs/')) and n.endswith('.rs')}
 admit('NEK_REPLAY_SETUP')
 r=py(f'''from pathlib import Path
import json,zlib,base64
b=Path({B!r});s=b/'NEK_src'
f=json.loads(zlib.decompress(base64.b64decode({base64.b64encode(zlib.compress(json.dumps(files).encode())).decode()!r})))
for n,t in f.items():p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NEK_FROZEN_RS.json').write_text(json.dumps(f));(b/'NEK_OVERLAY.json').write_text('[]')
print(len(f))
''');assert r.returncode==0,r.stderr
 (E/'NEK_REPLAY_FROZEN.json').write_text(json.dumps({n:sha(t.encode()) for n,t in files.items()},indent=2)+'\n')
def replay(a,rp,patch):
 original=json.loads((ROOT/rp).read_text()); overlay=dict(patched_files((ROOT/patch).read_text()))
 if os.environ.get('NEK_OVERLAY_FILE'):overlay=json.loads(Path(os.environ['NEK_OVERLAY_FILE']).read_text())
 assert overlay,patch
 forbidden=[n for n,t in overlay.items() if re.search(r'\bstatic\s+mut\b',t)]
 assert not forbidden,('needs local record migration',forbidden)
 # Root program allocator is never compiled for a library harness; no writable log.
 (E/(a+'_sources.json.xz')).write_bytes(lzma.compress(json.dumps(overlay,sort_keys=True).encode()))
 admit(a+'_INPUT')
 extra={'NEK_gate.py':(E/'NEK_gate.py').read_text(),'NEK_graph.py':(E/'NEK_graph.py').read_text()}
 r=py(f'''from pathlib import Path
import json,hashlib,zlib,base64
b=Path({B!r});s=b/'NEK_src';f=json.loads((b/'NEK_FROZEN_RS.json').read_text())
for n in json.loads((b/'NEK_OVERLAY.json').read_text()):
 p=s/n
 if n in f:p.write_text(f[n])
 elif p.is_file():p.unlink()
o=json.loads(zlib.decompress(base64.b64decode({base64.b64encode(zlib.compress(json.dumps(overlay).encode())).decode()!r})))
for n,t in o.items():p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NEK_OVERLAY.json').write_text(json.dumps(list(o)))
for n,t in {extra!r}.items():(b/n).write_text(t)
pins={{str(q.relative_to(s)):hashlib.sha256(q.read_bytes()).hexdigest() for q in s.rglob('*') if q.is_file() and q.suffix in ['.rs','.toml','.lock']}}
(b/'NEK_SOURCE_PINS.json').write_text(json.dumps(pins));print(len(pins))
''');assert r.returncode==0,r.stderr
 ni=(original.get('native_command') or original['command'])[:]
 assert 'cargo-kani' in ni[0],('unresolved native argv',rp)
 if '--features' not in ni:
  ni+=['--features',('r0' if '/aspis-core/' in ' '.join(ni) else 'r0,pool-v1-kernel' if '/aspis-statement/' in ' '.join(ni) else 'private-leaf-salts,optimized-terminal,program-build')]
 if os.environ.get('NEK_HARNESS'):
  ni[ni.index('--harness')+1]=os.environ['NEK_HARNESS']
 manifest=ni[ni.index('--manifest-path')+1]
 oldsrc=manifest.split('/crates/')[0] if '/crates/' in manifest else manifest.split('/programs/')[0]
 ni=[v.replace(oldsrc,B+'/NEK_src') for v in ni]
 ni=[B+'/NEK_target' if i>0 and ni[i-1]=='--target-dir' else v for i,v in enumerate(ni)]
 if os.environ.get('NEK_KMX_REQUIRED'):original['copy_patch_sha256']='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 env={k:v for k,v in original['env'].items() if k!='LEAN_PATH'};env['TMPDIR']=B+'/NEK_tmp';env['CARGO_NET_OFFLINE']='true'
 env['CARGO_PROFILE_DEV_OPT_LEVEL']='3';env['CARGO_PROFILE_DEV_DEBUG']='0';env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']='true'
 cfg=dict(attempt=a,kind='kani',module=ni[ni.index('--harness')+1],sources=['NEK_src/'+n for n in overlay]+['NEK_gate.py','NEK_graph.py','NEK_src/Cargo.lock'],command=['python3','NEK_gate.py',a+'.json'],native_command=ni,env=env,timeout=original.get('timeout',240),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(original_receipt=rp,original_sha256=sha((ROOT/rp).read_bytes()),patch=patch,patch_sha256=sha((ROOT/patch).read_bytes())),copy_patch_sha256=original.get('copy_patch_sha256'),expected_time='Optimized cached compilation then original native harness, static-free local/owned records; no multiplication',print_axioms='N/A: kani')
 rc=launch(cfg)
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{p.name:p.read_text() for p in b.glob({(a+'-*check.json')!r})}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
 return rc
if __name__=='__main__':
 if sys.argv[1]=='seed':seed()
 else:
  replay(*sys.argv[1:])
  log=(E/sys.argv[1]/'stdout.log').read_text()
  if re.search(r'could not compile|Found [0-9]+ compilation errors|no matching harness|Failed to match the following harness|Failed to execute cargo',log):raise SystemExit('own compile/selection failure; repair before dependent launch')
