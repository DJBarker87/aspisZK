from pathlib import Path
import importlib.util,sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent
sys.argv=['setup','none']
s=importlib.util.spec_from_file_location('NBU_native',E/'NBU_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBU_SETUP')
r=m.py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({m.B!r}); cache=Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'); origin=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
assert not cache.exists(),'own cache already exists; inspect'
shutil.copytree(origin,cache)
pins={{str(p.relative_to(cache)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
(b/'NBU_CACHE_IMPORTED.json').write_text(json.dumps(pins,indent=2)+'\\n')
old=Path('/home/dombarker/project-offloads/codex-cx-native-tx2f-20261027')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(old/n,b/n)
(b/'NBU_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(files=len(pins),origin=str(origin),destination=str(cache))))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBU_CACHE_SETUP.json').write_text(r.stdout)
# one frozen scratch archive outside repository, no compiled target copied
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
r=m.ssh('mkdir '+m.B+'/NBU_src');assert r.returncode==0,r.stderr
p=subprocess.Popen(['git','archive',m.REV,*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',m.H,'tar -xf - -C '+m.B+'/NBU_src'],stdin=p.stdout,capture_output=True,text=True);p.stdout.close();assert p.wait()==0 and r.returncode==0,r.stderr
# apply the exact mandated patch (including its Lean/native files), no custom stubs
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
r=m.py(f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({m.B!r});p=b/'NBU_KMX_copy_stubs.patch';p.write_text({patch!r});src=b/'NBU_src'
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(p)],cwd=src);assert r.returncode==0
shutil=None
(src/'crates/aspis-statement/src/KMX_stubs.rs').write_bytes((src/'KMX_stubs.rs').read_bytes())
p=src/'crates/aspis-statement/src/lib.rs';p.write_text('#![cfg_attr(kani, feature(allocator_api, next_index))]\\n'+p.read_text()+'\\n#[cfg(kani)]\\npub mod KMX_stubs;\\n')
print(json.dumps(dict(patch_sha256=hashlib.sha256({patch!r}.encode()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBU_KMX_SETUP.json').write_text(r.stdout)
print('setup done')
