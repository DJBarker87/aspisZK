from pathlib import Path
import subprocess,hashlib,json,time,shutil,re
W=Path(__file__).resolve().parent;H=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020');B=Path('/home/dombarker/project-offloads/s1-powers-claim-combined-sbf-v1-20261020');E=W/'evidence';E.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={x:(CG/x).read_text().strip() for x in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(512*1024**2),'memory.max':str(1024**3),'memory.swap.max':'0'}
artifact=B/'artifacts/aspis_r1_cost_probe_program.so';assert sha(artifact)=='57d240de8cf88dc4428d1ca65bbd6fb9a5f8bad8df14660caa20994a4df20eef'
rows=[]
def run(name,cmd):
 d=E/name;d.mkdir();(d/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');start=time.monotonic();before=(CG/'memory.events').read_text()
 with (d/'output.log').open('w') as log:result=subprocess.run(['/usr/bin/time','-v','-o',str(d/'time.log'),*cmd],cwd=W,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 txt=(d/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt);rec={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':int((CG/'memory.peak').read_text()),'scope_swap_peak_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text()};(d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 if result.returncode:print((d/'output.log').read_text()[-3000:]);raise SystemExit(result.returncode)
 return rec
cases=[x for x in json.loads((W/'baseline-runs.json').read_text()) if x['name'].startswith('cu-')];assert len(cases)==6
for case in cases:
 name=case['name'];cmd=case['command'].copy();base=json.loads(Path(cmd[4]).read_text());out=W/'runs'/name;out.mkdir(parents=True);cmd[2]=str(artifact);cmd[4]=str(out/'evidence.json');cmd[5]=str(out/'task');rec=run(name,cmd);data=json.loads((out/'evidence.json').read_text());a=data['execution'];b=base['execution'];assert a['error'] is None and a['stage1_error'] is None
 row={'name':name,'baseline_stage1_cu':b['stage1_compute_units'],'candidate_stage1_cu':a['stage1_compute_units'],'stage1_delta':a['stage1_compute_units']-b['stage1_compute_units'],'baseline_settlement_cu':b['compute_units'],'candidate_settlement_cu':a['compute_units'],'settlement_delta':a['compute_units']-b['compute_units'],'stage1_checkpoint_tail_same':a['stage1_checkpoint_tail_sha256']==b['stage1_checkpoint_tail_sha256'],'return_data_same':a['return_data_sha256']==b['return_data_sha256'],'receipt':rec};rows.append(row)
 assert row['stage1_checkpoint_tail_same'] and row['return_data_same'],row
stack=W/'stack';stack.mkdir();shutil.copy(B/'sbf-target-verifier/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',stack/'linked.elf');shutil.copy(artifact,stack/'stripped.so');shutil.copy(B/'evidence/build.log',stack/'build.log');shutil.copy(H/'harness/verifier-strict-stack.py',W/'verifier-strict-stack.py');stackrec=run('strict-stack',['python3',str(W/'verifier-strict-stack.py'),str(stack)])
result={'classification':'CANDIDATE NOT ADOPTED; frozen/live source unchanged','artifact_sha256':sha(artifact),'six_fixture_rows':rows,'strict_stack_receipt':stackrec,'strict_stack_script_sha256':sha(W/'verifier-strict-stack.py'),'limits':limits};(W/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
