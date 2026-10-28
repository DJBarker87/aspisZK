"""Fresh private extraction of one exact original wrapper with deployed selection."""
from pathlib import Path
import os,subprocess,json,hashlib,sys,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');row=sys.argv[1];O=D/('resume-'+row.lower()+('-'+sys.argv[2] if len(sys.argv)>2 else ''));O.mkdir(exist_ok=True)
T=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools')
pins={'aeneas':'562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19','charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','charon-driver':'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45'}
for n,h in pins.items():assert hashlib.sha256((T/n).read_bytes()).hexdigest()==h,n
plans=json.load(open(D/'resume-extraction-plans.json'));plan=plans[row]
manifest=(D/'classification-project-fixture/Cargo.toml').read_text().replace('path="fixture.rs"','path="lib.rs"')
(O/'Cargo.toml').write_text(manifest);(O/'Cargo.lock').write_bytes((D/'classification-project-fixture/Cargo.lock').read_bytes());(O/'lib.rs').write_text(plan['wrapper'])
env=dict(os.environ,PATH=str(T)+':/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(D/'resume-extract-target'),CARGO_BUILD_JOBS='4')
m=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(O/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,text=True));nodes={n['id']:n for n in m['resolve']['nodes']}
cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::'+plan['root']]
for inc in plan['includes']:cmd+=['--include',inc]
for opaque in plan.get('opaque',[]):cmd+=['--opaque',opaque]
cmd+=['--dest-file',str(O/(row+'.llbc')),'--','--manifest-path',str(O/'Cargo.toml'),'--release','--offline','--locked','--lib','--jobs','4']
record=dict(command=cmd,tool_pins=pins,plan=plan,features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']],profile=dict(name='release',debug_assertions=False,overflow_checks=False,opt_level=3),toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),inputs={n:hashlib.sha256((O/n).read_bytes()).hexdigest() for n in ['Cargo.toml','Cargo.lock','lib.rs']},qualification='ruling x prime; no cfg kani or pv_cb_extract; wrapper only calls shipped function')
(O/'inputs.json').write_text(json.dumps(record,indent=2)+'\n');print('Expected time: optimized cached compilation then '+row+' extraction',flush=True)
r=subprocess.run(cmd,env=env)
if r.returncode:sys.exit(r.returncode)
G=O/'generated';G.mkdir(exist_ok=True)
cmd2=[str(T/'aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_RDCD_'+row,'-dest',str(G),'-emit-json',str(O/(row+'.llbc'))]
record['aeneas_command']=cmd2;(O/'inputs.json').write_text(json.dumps(record,indent=2)+'\n')
r=subprocess.run(cmd2,env=env)
if r.returncode:sys.exit(r.returncode)
record['outputs']={str(p.relative_to(O)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in list(G.iterdir())+[O/(row+'.llbc')]};(O/'inputs.json').write_text(json.dumps(record,indent=2)+'\n')
