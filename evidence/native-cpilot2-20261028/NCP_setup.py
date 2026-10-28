from pathlib import Path
import NCP_runner as m
import subprocess,json
m.admit('NCP_SOURCE_SETUP')
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
r=m.ssh('mkdir '+m.B+'/NCP_src');assert r.returncode==0,r.stderr
p=subprocess.Popen(['git','archive',m.REV,*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',m.H,'tar -xf - -C '+m.B+'/NCP_src'],stdin=p.stdout,capture_output=True,text=True);p.stdout.close();assert p.wait()==0 and r.returncode==0,r.stderr
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
r=m.py(f'''from pathlib import Path
import subprocess,json,hashlib
b=Path({m.B!r});p=b/'NCP_KMX_copy_stubs.patch';p.write_text({patch!r});src=b/'NCP_src'
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(p)],cwd=src);assert r.returncode==0
(src/'crates/aspis-statement/src/KMX_stubs.rs').write_bytes((src/'KMX_stubs.rs').read_bytes())
p=src/'crates/aspis-statement/src/lib.rs';p.write_text('#![cfg_attr(kani, feature(allocator_api, next_index))]\\n'+p.read_text()+'\\n#[cfg(kani)] pub mod KMX_stubs;\\n#[cfg(kani)] pub mod NCP_controls;\\n')
print(json.dumps(dict(patch_sha256=hashlib.sha256({patch!r}.encode()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(m.E/'NCP_KMX_SETUP.json').write_text(r.stdout)
