"""NPC_ capped-host receipt wrapper (NDZ_run.py adapted), restricted to the loopback B2 config."""
import datetime,hashlib,json,pathlib,subprocess,sys,time
label=sys.argv[1];command=sys.argv[2:]
assert label.startswith('NPC_')
root=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet2-20261109/local');out=root/'out'
config=json.load(open(command[2]));assert config['rpc_url']=='http://127.0.0.1:18997'
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().strip().split('::')[1])
receipt={'command':command,'expected_time':'optimized selected64 proof generation (two proofs) and local transaction finality','pool_source_revision':'b936275465600469312d1f058cdc91ea2a11f3dc','verifier_frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','client_source_revision':'dfa35acd8390aea176c13710d320d041332b320a','script_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.py'))+sorted(root.glob('*.sh'))},'cgroup':str(cg),'limits':{p:(cg/p).read_text().strip() for p in ['memory.high','memory.max','memory.swap.max','pids.max']},'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'print_axioms':'N/A: no Lean target'}
assert receipt['limits']['memory.swap.max']=='0' and int(receipt['limits']['memory.max'])<=8589934592 and int(receipt['limits']['memory.high'])<=6442450944
(out/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
start=time.monotonic()
with (out/(label+'.log')).open('w') as log:
 result=subprocess.run(['/usr/bin/time','-v','-o',str(out/(label+'.time'))]+command,cwd=root,stdout=log,stderr=log)
receipt.update(exit=result.returncode,wall_seconds=time.monotonic()-start,cgroup_memory_peak=(cg/'memory.peak').read_text().strip(),cgroup_swap_peak=(cg/'memory.swap.peak').read_text().strip(),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
s=(out/(label+'.time')).read_text()
for key,lab in [('peak_rss_kib','Maximum resident set size'),('swaps','Swaps')]:receipt[key]=next((l.split(':',1)[1].strip() for l in s.splitlines() if lab in l),None)
(out/(label+'-receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
raise SystemExit(result.returncode)
