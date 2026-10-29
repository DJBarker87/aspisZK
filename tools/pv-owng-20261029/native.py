from pathlib import Path
import subprocess,hashlib,json,os
D=Path('/home/dombarker/project-offloads/codex-pv-owng-20261029')
O=Path('/home/dombarker/project-offloads/codex-pv-ownd-20261029')
lib=O/'target/release/deps/libaspis_statement-d9a1a32deb1a9c73.rlib'
assert lib.is_file()
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','aspis_statement='+str(lib),'-L','dependency='+str(lib.parent),str(D/'probe.rs'),'-o',str(D/'probe')]
print('phase: compile/link small original-root probe against existing release rlibs',flush=True)
r=subprocess.run(cmd);assert r.returncode==0
# This diagnostic probe executes original statement roots, not host_forest replacements.
r=subprocess.run([str(D/'probe')],capture_output=True,text=True);print(r.stdout,flush=True);assert r.returncode==0
commands={}
for name,c in [('symbols',['nm','-C',str(D/'probe')]),('disassembly',['objdump','-dC',str(D/'probe')]),('relocations',['readelf','-rW',str(D/'probe')]),('rustc',['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv'])]:
 q=subprocess.run(c,capture_output=True,text=True);assert q.returncode==0;commands[name]=dict(command=c,exit=q.returncode,stdout=q.stdout)
def record(p):return dict(path=str(p),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
(D/'native-result.json').write_text(json.dumps(dict(command=cmd,stdout=r.stdout,commands=commands,inputs=[record(lib),record(D/'probe.rs'),record(O/'deployed-units.json'),record(O/'deployed-client-Cargo.lock')],binary=record(D/'probe'),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',features=json.loads((O/'deployed-units.json').read_text()),classification='diagnostic original-root release probe; not the shipped client artifact; no singleton class assigned'),indent=2)+'\n')
