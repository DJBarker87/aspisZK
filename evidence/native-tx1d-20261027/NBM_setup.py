from pathlib import Path
import sys,json,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
print(json.dumps(out))''');assert r.returncode==0,r.stderr
(E/'NBM_INITIAL_HOST_PINS.json').write_text(r.stdout)
h.admit('NBM_SETUP')
R=E.parents[1]
payload={f:(R/f).read_text() for f in ['crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/multiproof.rs']}
code=f'''from pathlib import Path
import shutil,json,hashlib
b=Path({h.B!r});base=Path('/home/dombarker/project-offloads/codex-cx-native-tx1a-20261027/NBE_src');s=b/'NBM_src'
assert not s.exists()
for p in base.rglob('*'):
 rel=p.relative_to(base);q=s/rel
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif p.name.startswith('NBE_'):continue
 else:q.symlink_to(p.resolve())
for name,text in {payload!r}.items():
 p=s/name;p.unlink();p.write_text(text)
p=s/'Cargo.lock';p.unlink();shutil.copyfile(base/'Cargo.lock',p)
p=s/'crates/aspis-r1-cost-probe/src/multiproof.rs';p.write_text(p.read_text()+'\\n#[cfg(kani)]\\nmod NBM_copy;\\n')
(s/'crates/aspis-r1-cost-probe/src/NBM_copy.rs').write_text({(E/'NBM_copy.rs.txt').read_text()!r})
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copyfile(Path('/home/dombarker/project-offloads/codex-cx-native-tx1c-20261027')/name,b/name)
(b/'NBM_tmp').mkdir()
print(json.dumps(dict(lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),borrowed_corpus=str(base),files=len(list(s.rglob('*'))))))
'''
r=h.remote_py(code);assert r.returncode==0,r.stderr
(E/'NBM_SETUP.json').write_text(r.stdout)
