from pathlib import Path
import sys,json,subprocess,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
h.admit('KMX_SETUP')
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',frozen,'crates','programs'],text=True).splitlines()
pins={f:hashlib.sha256(subprocess.check_output(['git','show',frozen+':'+f])).hexdigest() for f in files}
# Only files with a diagnostic overlay need private frozen replacements.
payload={f:subprocess.check_output(['git','show',frozen+':'+f],text=True) for f in ['crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/compact.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','Cargo.lock']}
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({h.B!r});s=b/'KMX_src';base=Path('/home/dombarker/project-offloads/codex-cx-kani-diag-20261027/KDX_src')
assert not s.exists()
for p in base.rglob('*'):
 rel=p.relative_to(base);q=s/rel
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif p.name.startswith('KDX_'):continue
 else:q.symlink_to(p.resolve())
for name,txt in {payload!r}.items():
 p=s/name
 if p.exists() or p.is_symlink():p.unlink()
 p.write_text(txt)
pins={pins!r}
bad=[n for n,sha in pins.items() if not (s/n).is_file() or hashlib.sha256((s/n).read_bytes()).hexdigest()!=sha]
assert not bad,bad
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(Path({h.C!r})/name,b/name)
(b/'KMX_tmp').mkdir();Path({h.CACHE!r}).mkdir(exist_ok=True)
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{(h.C+'/objects')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
(b/'KMX_INITIAL_HOST_PINS.json').write_text(json.dumps(out,indent=2)+'\\n')
(b/'KMX_FROZEN_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\\n')
print(json.dumps(dict(frozen_files=len(pins),bad=bad,lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),cache={h.CACHE!r})))
'''
(E/'KMX_setup_host.py').write_text(code)
r=subprocess.run(['scp',str(E/'KMX_setup_host.py'),str(E/'KMX_gate.py'),h.H+':'+h.B+'/'],capture_output=True,text=True);assert r.returncode==0,r.stderr
r=h.ssh('python3 '+h.B+'/KMX_setup_host.py');assert r.returncode==0,r.stdout+r.stderr
(E/'KMX_SETUP.json').write_text(r.stdout);print(r.stdout)
r=h.remote_py(f'from pathlib import Path\nimport json\nb=Path({h.B!r});print(json.dumps({{n:(b/n).read_text() for n in ["KMX_INITIAL_HOST_PINS.json","KMX_FROZEN_SOURCE_PINS.json"]}}))');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():(E/n).write_text(s)
