from pathlib import Path
import subprocess,json
import NCV_transport as t
t.admit('NCV_SETUP')
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
r=t.ssh('test ! -e '+t.B+'/NCV_src && mkdir '+t.B+'/NCV_src');assert r.returncode==0,r.stderr
p=subprocess.Popen(['git','archive',t.REV,*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',t.H,'tar -xf - -C '+t.B+'/NCV_src'],stdin=p.stdout,capture_output=True,text=True);p.stdout.close();assert p.wait()==0 and r.returncode==0,r.stderr
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
t.upload({'NCV_KMX_copy_stubs.patch':patch})
r=t.py(f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({t.B!r});s=b/'NCV_src'
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(b/'NCV_KMX_copy_stubs.patch')],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
coherent=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:(b/n).write_bytes((coherent/n).read_bytes())
c=b.parent/'codex-cx-decref-cache-20261028';c.mkdir(exist_ok=True);imports={{}}
for name in ['codex-cx-cpilot-cache-20261028','codex-cx-tx2codec-cache-20261028','codex-cx-leaf-cache-20261027']:
 root=b.parent/name
 for p in root.rglob('*'):
  if not p.is_file():continue
  q=c/p.relative_to(root);h=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  imports[str(p)]=dict(sha256=h,selected_sha256=hashlib.sha256(q.read_bytes()).hexdigest())
for n in ['NCV_tmp','NCV_generated','NCV_objects']:(b/n).mkdir(exist_ok=True)
lib=[coherent/'objects/Aeneas.olean']+list((coherent/'objects/Aeneas').rglob('*.olean'))
print(json.dumps(dict(cache_imports=imports,library={{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in lib}},source_files=sum(p.is_file() for p in s.rglob('*')))))
''');assert r.returncode==0,r.stdout+r.stderr
(t.E/'NCV_SETUP_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('setup complete',flush=True)
