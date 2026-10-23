#!/usr/bin/env python3
"""Focused frozen-source prefix extraction in this job's capped workspace."""
from pathlib import Path
import json,subprocess,shlex,sys,hashlib
R=Path(__file__).resolve().parents[2];T=R/'tools/port4c-20261023';E=R/'evidence/port4c-20261023'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-port4c-20261023'
kind=sys.argv[1];number=1+max((int(p.stem.split('-')[1]) for p in T.glob(kind+'-*.json')),default=0);a=f'{kind}-{number:03}'
if kind=='charon':
 old=json.loads((R/'tools/ports3-20261023/charon-005.json').read_text())
 cmd=old['command'];cmd=cmd[:cmd.index('--include')]+['--include','crate::verifier::batch_prefix_products','--start-from','crate::verifier::batch_prefix_products','--include','aspis_core::field::M31']+cmd[cmd.index('--consts'):]
 cmd=[x.replace('codex-cx-ports3-20261023','codex-cx-port4c-20261023').replace('Port3_StageChildren.llbc','Port4C_Prefix.llbc') for x in cmd]
 cfg={**old,'attempt':a,'command':cmd,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'expected_time':'Optimized compilation and focused MIR extraction of batch_prefix_products only; no proof generation or arithmetic elimination'}
 cfg['env']['CARGO_TARGET_DIR']=B+'/charon-target'
 subprocess.run(['ssh',H,f'test -d {B}/src || cp -a /home/dombarker/project-offloads/codex-cx-ports3-20261023/src {B}/src'],check=True)
 for f in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs']:
  remote=subprocess.check_output(['ssh',H,'sha256sum',B+'/src/'+f],text=True).split()[0]
  assert remote==hashlib.sha256((R/f).read_bytes()).hexdigest(),f
else:
 old=json.loads((R/'tools/ports3-20261023/aeneas-004.json').read_text())
 cmd=[x.replace('codex-cx-ports3-20261023','codex-cx-port4c-20261023').replace('Port3_StageChildren','Port4C_Prefix') for x in old['command']]
 cfg={**old,'attempt':a,'command':cmd,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'sources':['Port4C_Prefix.llbc'],'expected_time':'Focused Aeneas symbolic translation of changed LLBC containing native prefix only'}
cfg['deps_fingerprint']={'scope':'Read-only inherited frozen source snapshot copied into own workspace; requested verifier/candidate bytes checked equal to local current sources; only prefix root transparent'}
c=T/(a+'.json');c.write_text(json.dumps(cfg,indent=2)+'\n')
admission=(T/'Port4C_compile.py').read_text().split("admission='''",1)[1].split("'''",1)[0]
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True);(E/(a+'-reservation.json')).write_text(r.stdout)
subprocess.run(['scp','-q',str(c),str(T/'Port4C_run_host.py'),H+':'+B+'/'],check=True)
r=subprocess.run(['ssh',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port4C_run_host.py {a}.json'],capture_output=True,text=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
