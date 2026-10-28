from pathlib import Path
import subprocess,json
import NDB_transport as t
t.admit('NDB_SETUP')
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
# Source archive already uploaded by initial setup; resume own failed formatter.
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
t.upload({'NDB_KMX_copy_stubs.patch':patch})
r=t.py(f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({t.B!r});s=b/'NDB_src'
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(b/'NDB_KMX_copy_stubs.patch')],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
coherent=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((coherent/n).read_bytes())
c=b.parent/'codex-cx-decref-cache-20261028';assert c.is_dir();imports={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in c.rglob('*') if p.is_file()}}
for n in ['NDB_tmp','NDB_generated','NDB_objects']:(b/n).mkdir(exist_ok=True)
lib=[coherent/'objects/Aeneas.olean']+list((coherent/'objects/Aeneas').rglob('*.olean'))
print(json.dumps(dict(cache_imports=imports,library={{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in lib}},source_files=sum(p.is_file() for p in s.rglob('*')))))
''');assert r.returncode==0,r.stdout+r.stderr
(t.E/'NDB_SETUP_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('setup complete',flush=True)
