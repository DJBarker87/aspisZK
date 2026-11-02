from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,hashlib,json,shutil,time
out={'captured_epoch':time.time(),'tools':{}}
for name,path,cmd in [('cargo-kani','/home/dombarker/.cargo/bin/cargo-kani',['/home/dombarker/.cargo/bin/cargo','kani','--version']),('kani-compiler','/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler',['/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler','--version']),('cbmc','/home/dombarker/.kani/kani-0.67.0/bin/cbmc',['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--version']),('kani-driver','/home/dombarker/.kani/kani-0.67.0/bin/kani-driver',['/home/dombarker/.kani/kani-0.67.0/bin/kani-driver','--version']),('bundled-rustc','/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc',['/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc','-vV']),('kissat','/home/dombarker/.kani/kani-0.67.0/bin/kissat',['/home/dombarker/.kani/kani-0.67.0/bin/kissat','--version'])]:
 p=Path(path);h=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 r=subprocess.run(cmd,capture_output=True,text=True)
 out['tools'][name]={'path':str(p),'sha256':h.hexdigest(),'size':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns,'version_exit':r.returncode,'version_stdout':r.stdout,'version_stderr':r.stderr}
p=Path('/home/dombarker/.kani/kani-0.67.0/rustc-version');out['bundled_rustc_record']=p.read_text()
r=subprocess.run(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],capture_output=True,text=True);out['deployed_rustc']={'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr;d=json.loads(r.stdout);old=json.loads((E/'host/K79201/tool-pins.json').read_text())
for n in ['kani-compiler','cbmc']:assert d['tools'][n]['sha256']==old[n]['sha256'],n
additional=json.loads((E/'TOOL-PINS-ADDITIONAL.json').read_text())
for name,path in [('cargo-kani','/home/dombarker/.cargo/bin/cargo-kani'),('kani-driver','/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),('bundled-rustc','/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc')]:assert d['tools'][name]['sha256']==additional[path]['sha256'],name
d['additional_tools_match_initial_pins']=True
d['core_tools_match_initial_pair']=True;d['method']='Read-only hash/version inspection; no compiler/solver/build invocation, no installation.';(E/'D549-TOOL-PINS.json').write_text(json.dumps(d,indent=2)+'\n');print({n:v['sha256']for n,v in d['tools'].items()})
