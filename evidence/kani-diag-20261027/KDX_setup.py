from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{(h.C+'/objects')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
print(json.dumps(out))''');assert r.returncode==0,r.stderr
(E/'KDX_INITIAL_HOST_PINS.json').write_text(r.stdout)
h.admit('KDX_SETUP')
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
payload={f:subprocess.check_output(['git','show',frozen+':'+f],text=True) for f in ['crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','Cargo.lock']}
code=f'''from pathlib import Path
import shutil,json,hashlib
b=Path({h.B!r});base=Path('/home/dombarker/project-offloads/codex-cx-native-tx1d-20261027/NBM_src');s=b/'KDX_src'
assert not s.exists()
for p in base.rglob('*'):
 rel=p.relative_to(base);q=s/rel
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif p.name.startswith('NBM_'):continue
 else:q.symlink_to(p.resolve())
for name,text in {payload!r}.items():
 p=s/name;p.unlink();p.write_text(text)
p=s/'crates/aspis-r1-cost-probe/src/multiproof.rs';p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="KDX_copy.rs"]\\nmod KDX_copy;\\n')
(s/'crates/aspis-r1-cost-probe/src/KDX_copy.rs').write_text({(E/'KDX_copy.rs.txt').read_text()!r})
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(Path('/home/dombarker/project-offloads/codex-cx-native-tx1d-20261027')/name,b/name)
(b/'KDX_tmp').mkdir()
(b/'KDX_gate.py').write_text({(E/'KDX_gate.py').read_text()!r})
print(json.dumps(dict(lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),borrowed_corpus=str(base))))
'''
(E/'KDX_setup_host.py').write_text(code)
r=subprocess.run(['scp',str(E/'KDX_setup_host.py'),h.H+':'+h.B+'/KDX_setup_host.py'],capture_output=True,text=True);assert r.returncode==0,r.stderr
r=h.ssh('python3 '+h.B+'/KDX_setup_host.py');assert r.returncode==0,r.stderr
(E/'KDX_SETUP.json').write_text(r.stdout)
