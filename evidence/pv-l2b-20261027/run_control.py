#!/usr/bin/env python3
"""Six bounded, optimized control-only Kani invocations, one scope at a time."""
import datetime,hashlib,json,pathlib,re,shlex,subprocess,sys,time
E=pathlib.Path(__file__).resolve().parent
ROOT=E.parent.parent
HOST='dombarker@100.108.41.90'
JOB='/home/dombarker/project-offloads/codex-pv-l2b-20261027'
RES='/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py'
harness=sys.argv[1]
for old in list((E/'receipts').glob('*/reservation.json'))+list((E/'kani').glob('*/reservation.json')):
 try:
  gate=json.loads(old.read_text())
  if gate.get('allowed') is not False:continue
  stamp=gate.get('utc');when=float(stamp) if isinstance(stamp,(float,int)) else datetime.datetime.fromisoformat(stamp).timestamp()
  wait=(30 if 'error' in gate else 180)-(time.time()-when)
  if wait>0:print(f'Mandatory wait {wait:.1f}s from {old}');sys.exit(78)
 except (ValueError,TypeError):pass
assert harness in ['mask_range','reject_exactly_last','high_bit_fibres','entropy_zero_iff','entropy_marker','cursor_slice']
number=1
while (E/'kani'/f'{harness}-{number}').exists():number+=1
d=E/'kani'/f'{harness}-{number}';d.mkdir(parents=True,exist_ok=False)
def ssh(c):return subprocess.run(['ssh',HOST,c],text=True,capture_output=True)
pre=ssh(f'python3 {RES} {JOB}/reservation-kani-{harness}.json > {JOB}/reservation-kani-{harness}.log 2>&1; cat {JOB}/reservation-kani-{harness}.log')
(d/'preflight.log').write_text(pre.stdout+pre.stderr)
r=ssh(f'cat {JOB}/reservation-kani-{harness}.json');(d/'reservation.json').write_text(r.stdout)
if not json.loads(r.stdout)['allowed']:print('RESERVATION HOLD '+r.stdout[:400]);sys.exit(78)
subprocess.run(['scp','-q',str(E/'control.rs'),f'{HOST}:{JOB}/control.rs'],check=True)
# Expected cost: optimized standalone compilation, then bounded Boolean/index
# checking. No field arithmetic, proof generation or elimination.
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',
 '/usr/bin/time','-v','-o',f'{JOB}/kani-{harness}.time','timeout','180','taskset','--cpu-list','0-3','env',
 'PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','RUSTFLAGS=-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes',
 '/home/dombarker/.cargo/bin/kani','--verbose','-Z','unstable-options','-j','4','--exact','--harness',harness,'--output-format','terse',f'{JOB}/control.rs']
record={'harness':harness,'target':shlex.join(cmd),'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'sha256':hashlib.sha256((E/'control.rs').read_bytes()).hexdigest(),'print_axioms':'N/A (Kani control projection)',
 'scope':'standalone no-stub control/indexing; not shipped-function equivalence','expected':'optimized compilation then named bounded control gate'}
(d/'invocation.json').write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic();p=ssh('cd '+JOB+' && '+shlex.join(cmd)+f' > {JOB}/kani-{harness}.log 2>&1; result=$?; echo exit=$result >> {JOB}/kani-{harness}.log')
for name,remote in [('out.log',f'{JOB}/kani-{harness}.log'),('time.log',f'{JOB}/kani-{harness}.time')]:
 r=ssh('cat '+remote);(d/name).write_text(r.stdout+r.stderr)
record['wall_client_seconds']=time.monotonic()-start
out=(d/'out.log').read_text();timing=(d/'time.log').read_text()
record['exit']=int(re.search(r'^exit=(\d+)',out,re.M)[1])
record['caps']={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64}
for key,pattern in [('wall',r'Elapsed \(wall clock\) time.*: (.+)'),('peak_RSS_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swap',r'Swaps: (\d+)')]:
 m=re.search(pattern,timing);record[key]=m[1] if m else None
(d/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print((d/'out.log').read_text());print((d/'time.log').read_text())
sys.exit(record['exit'])
