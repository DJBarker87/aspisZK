from pathlib import Path
import subprocess,json
import NCX_transport as t
E=t.E
t.admit('NCX_NATIVE_SETUP')
paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
r=t.ssh('test ! -e '+t.B+'/NCX_src && mkdir '+t.B+'/NCX_src');assert r.returncode==0,r.stderr
p=subprocess.Popen(['git','archive',t.REV,*paths],stdout=subprocess.PIPE)
r=subprocess.run(['ssh','-o','ControlMaster=no',t.H,'tar -xf - -C '+t.B+'/NCX_src'],stdin=p.stdout,capture_output=True,text=True);p.stdout.close();assert p.wait()==0 and r.returncode==0,r.stderr
t.upload({'NCX_KMX_copy_stubs.patch':Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text(),'NCX_frozen_graph.sha256':Path('evidence/native-decref-20261028/NCV_frozen_graph.sha256').read_text()})
r=t.py(f'''from pathlib import Path
import subprocess
b=Path({t.B!r})
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(b/'NCX_KMX_copy_stubs.patch')],cwd=b/'NCX_src',capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
''');assert r.returncode==0,r.stderr
print('native scratch frozen source installed')
