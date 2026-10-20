#!/usr/bin/env python3
"""Sequential freeze plan. Every nonzero child or assertion stops the run."""
from pathlib import Path
import hashlib,json,subprocess,os
H=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
B=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,**kw):
 print('START',cmd,flush=True);subprocess.run(list(map(str,cmd)),check=True,**kw)
def cap(name,note,cwd,cmd,**kw):run([H/'harness/capped-run.sh',name,note,cwd,'--',*cmd],**kw)
run(['cp','-a','--reflink=auto',B/'charon-target',H/'charon-target'])
for phase in ['charon','aeneas']:run(['python3',H/'harness/extract.py',phase,'freeze'])
p=H/'extraction-freeze/Stage2.llbc';old=B/'extraction-checkpoint-k-inline-55/Stage2.llbc'
(H/'llbc-comparison.json').write_text(json.dumps(dict(sha256=sha(p),bytes=p.stat().st_size,previous_sha256=sha(old),byte_identical=p.read_bytes()==old.read_bytes(),has_errors=json.loads(p.read_text())['has_errors']),indent=2)+'\n')
# Actual linked image and full diagnostic stream, not just stripped executable.
for mode in ['default','devnet']:
 w=H/'stack'/mode;w.mkdir(parents=True)
 run(['cp',H/'artifacts'/mode/'linked.elf',w/'linked.elf'])
 run(['cp',H/'artifacts'/mode/'aspis_r1_cost_probe_program.so',w/'stripped.so'])
 (w/'build.log').write_text(''.join((H/'receipts'/('build-'+mode)/f).read_text() for f in ['stdout.txt','stderr.txt']))
 cap('stack-'+mode,'Strict complete linked verifier ELF audit',H,['python3',H/'harness/verifier-strict-stack.py',w])
# Six fixtures, same driver, pool and registry as B1.
BASE=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019')
D=BASE/'artifacts/pool_gate_adopt';POOL=Path('/home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/pool/aspis_pool.so');REG=Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')
V=H/'artifacts/default/aspis_r1_cost_probe_program.so'
b1={'transfer-13':(1199648,1129757),'transfer-255':(1199567,1161066),'transfer-1023':(1199687,1160974),'withdrawal-13':(1198225,1138950),'withdrawal-255':(1198264,1170523),'withdrawal-1023':(1198386,1170263)}
rows=[]
for label,(s,t) in b1.items():
 kind,n=label.split('-');w=H/'runs/cu'/label;w.mkdir(parents=True)
 f=H/'runs/adopt'/label/'task'
 cap('cu-'+label,'LiteSVM CU fixture replay, seconds',H,[D,POOL,V,REG,w/'evidence.json',w/'task',kind,'success','--pairs',n,'--reuse',f/'r1-s2-proof.bin',f/'r1-s2-public-asf8.bin','--split','10','--tx-version','v1'])
 e=json.loads((w/'evidence.json').read_text())['execution'];a=e['stage1_compute_units'];b=e['compute_units']
 rows.append(dict(fixture=label,stage1_cu=a,settlement_cu=b,b1_stage1=s,b1_settlement=t,stage1_margin=s-a,settlement_margin=t+10000-b,outcome=e['outcome']))
 (H/'cu.json').write_text(json.dumps(rows,indent=2)+'\n');print(rows[-1],flush=True)
 assert e['outcome']=='accepted' and a<=s and b<=t+10000, 'CU gate failed: '+label
for g in ['codec','counter','counter-audit']:
 run(['sh',H/'harness/gates.sh',g])
 if g=='codec':assert sha(H/'receipts/gate-codec-1233/stdout.log')=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321'
 else:
  label='adopted' if g=='counter' else 'audit-eight-way'
  old=BASE/'runs/counter-adopted.json' if g=='counter' else Path('/home/dombarker/project-offloads/codex-r1p-writer-migration-20261019/out/ordered-counter-new.json')
  a=json.loads((H/f'runs/counter-{label}.json').read_text());b=json.loads(old.read_text())
  for r in [a,b]:r['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x:x['input_hex'])
  for k in ['ordered_digest_calls','hash_input_counts','acceptance']:assert a[k]==b[k],(g,k)
for g in ['program','crate-default','crate-detail','crate-audit','pool-default','pool-r1','pool-all','pool-v7','teeth','auth','masked','retry','crate-prover']:
 run(['sh',H/'harness/gates.sh',g])
cap('simulator-d78','Four simulator proofs: optimized P_R1 elimination/proof generation, ~3 min',H/'src',['cargo','run','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--example','r1p_sim_gate','--','4',H/'runs/simulator.json'])
run(['sh',H/'harness/run-plan.sh','mutations',D,V])
(H/'ALL-PASS').write_text('All freeze plan commands and assertions passed\n')
