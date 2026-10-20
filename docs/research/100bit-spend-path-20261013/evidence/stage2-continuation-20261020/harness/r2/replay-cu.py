#!/usr/bin/env python3
"""Six saved public/proof fixtures through the rebuilt SBF verifier, stop on failure."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020')
BASE=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019')
D=BASE/'artifacts/pool_gate_adopt'
POOL='/home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/pool/aspis_pool.so'
REG='/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so'
V=H/'artifacts/verifier/aspis_r1_cost_probe_program.so'
B1={'transfer-13':(1199648,1129757),'transfer-255':(1199567,1161066),'transfer-1023':(1199687,1160974),'withdrawal-13':(1198225,1138950),'withdrawal-255':(1198264,1170523),'withdrawal-1023':(1198386,1170263)}
rows=[]
for label,(b1s,b1t) in B1.items():
 kind,n=label.split('-');t=H/'runs-r2/cu'/label;t.mkdir(parents=True)
 old=BASE/'runs/adopt'/label/'task'
 cmd=[str(H/'harness-r2/capped-run.sh'),'cu-'+label,'LiteSVM replay of rebuilt ELF, seconds',str(H),'--',str(D),POOL,str(V),REG,str(t/'evidence.json'),str(t/'task'),kind,'success','--pairs',n,'--reuse',str(old/'r1-s2-proof.bin'),str(old/'r1-s2-public-asf8.bin'),'--split','10','--tx-version','v1']
 subprocess.run(cmd,check=True)
 e=json.loads((t/'evidence.json').read_text())['execution'];s=e['stage1_compute_units'];st=e['compute_units']
 rows.append(dict(fixture=label,stage1_cu=s,settlement_cu=st,b1_stage1=b1s,b1_settlement=b1t,stage1_ok=s<=b1s,settlement_ok=st<=b1t+10000,outcome=e['outcome']))
 (H/'cu-r2.json').write_text(json.dumps(dict(verifier_sha256=hashlib.sha256(V.read_bytes()).hexdigest(),rows=rows),indent=2)+'\n')
 print(label,rows[-1],flush=True)
 assert rows[-1]['outcome']=='accepted' and rows[-1]['stage1_ok'] and rows[-1]['settlement_ok'], 'CU gate failed'
