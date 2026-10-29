"""Capped-host receipt wrapper, restricted to loopback rehearsal configs."""
import datetime,hashlib,json,pathlib,subprocess,sys,time
label=sys.argv[1];command=sys.argv[2:]
assert label.startswith('NDZ_')
root=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029')
out=root/'evidence/devnet-rehearse-20261029'
config=json.load(open(command[2]));assert config['rpc_url'] in ('http://127.0.0.1:18993','http://127.0.0.1:18995')
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[1])
receipt={'command':command,'expected_time':'paced loader writes and finality' if 'deploy' in command[1] else ('retained selected64 proof artifact reuse and local transaction finality' if config.get('proof_cache_reuse') else 'optimized selected64 proof generation and local transaction finality'),'source_revision':'dfa35acd8390aea176c13710d320d041332b320a','frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','script_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.glob('*.py')},'cgroup':str(cg),'limits':{p:(cg/p).read_text().strip() for p in ['memory.high','memory.max','memory.swap.max']},'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'print_axioms':'N/A: no Lean target'}
assert receipt['limits']['memory.swap.max']=='0'
(out/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
start=time.monotonic()
with (out/(label+'.log')).open('w') as log:
 result=subprocess.run(['/usr/bin/time','-v','-o',str(out/(label+'.time'))]+command,cwd=root,stdout=log,stderr=log)
receipt.update(exit=result.returncode,wall_seconds=time.monotonic()-start,cgroup_memory_peak=(cg/'memory.peak').read_text().strip(),cgroup_swap_peak=(cg/'memory.swap.peak').read_text().strip(),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(out/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
raise SystemExit(result.returncode)
