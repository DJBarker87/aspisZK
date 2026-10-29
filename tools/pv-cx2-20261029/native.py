"""Capped, single-command identity/extraction runs with retained receipts."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1')
G=H.parents[1]/'codex-cx-prover-rw-20261023/native-entropy/reservation.py'
def admit(O,label,amount):
 p=O/label
 r=subprocess.run(['python3',str(G),str(p),'--requested-bytes',str(amount)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (O/(label+'.log')).write_text(r.stdout)
 assert r.returncode==0 and json.loads(p.read_text()).get('allowed') is True,r.stdout
if sys.argv[1]=='inner':
 O=Path(sys.argv[2]);x=json.loads((O/'command.json').read_text())
 cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
 assert list(limits.values())==[str(6*2**30),str(8*2**30),'0','64']
 admit(O,'reservation-at-barrier.json',0)
 start=time.monotonic()
 with (O/'output.log').open('w') as f:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),'timeout','540','taskset','--cpu-list','0-3',*x['command']],cwd=x['cwd'],stdout=f,stderr=subprocess.STDOUT)
 txt=(O/'time.log').read_text();metric=lambda k:int(re.search(re.escape(k)+r':\s*(\d+)',txt)[1])
 receipt=dict(target=x['command'],cwd=x['cwd'],exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),cgroup_peak_bytes=(cg/'memory.peak').read_text().strip(),cgroup_swap_peak_bytes=(cg/'memory.swap.peak').read_text().strip(),limits=limits,source_revision='570c0008098b8cc23d16d86f9edb0c2a41b0e118',print_axioms='N/A: Aeneas translation, no Lean elaboration',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 (O/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');sys.exit(r.returncode)
n=int(sys.argv[1]);assert 73330<=n<=73349
O=H/f'N{n}';O.mkdir();config=json.loads(Path(sys.argv[2]).read_text())
(O/'command.json').write_text(json.dumps(config,indent=2)+'\n')
admit(O,'reservation-before.json',8*2**30)
cmd=['systemd-run','--user','--scope','--unit',f'PV_CX2_N{n}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'native.py'),'inner',str(O)]
with (O/'launcher.log').open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
print(n,r.returncode,flush=True);sys.exit(r.returncode)
