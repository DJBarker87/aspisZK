"""Direct frozen-source extraction, no source rewriting or extractor changes."""
from pathlib import Path
import datetime,hashlib,json,os,re,runpy,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029')
R=H/'src'; PIN=H.parent/'codex-pv-cb-20261026/pinned-tools'
rev='27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def inner(o,cmd):
 cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
 assert limits==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],[str(6*2**30),str(8*2**30),'0','64']))
 start=time.monotonic()
 with (o/'output.log').open('w') as f:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(o/'time.log'),*cmd],cwd=R/'tools/r1-cost-probe',stdout=f,stderr=subprocess.STDOUT)
 txt=(o/'time.log').read_text()
 metric=lambda k:int(re.search(re.escape(k)+r':\s*(\d+)',txt)[1]) if re.search(re.escape(k)+r':\s*(\d+)',txt) else None
 (o/'receipt.json').write_text(json.dumps(dict(target=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),cgroup_peak_bytes=(cg/'memory.peak').read_text().strip(),cgroup_swap_peak_bytes=(cg/'memory.swap.peak').read_text().strip(),limits=limits,source_revision=rev,print_axioms='N/A: native extraction; no Lean elaboration',utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
 return r.returncode
if sys.argv[1]=='inner':sys.exit(inner(Path(sys.argv[2]),json.loads(sys.argv[3])))
n=int(sys.argv[1]);assert 73300<=n<=73329
entry=sys.argv[2] if len(sys.argv)>2 else 'crate::main'
o=H/f'N{n}';o.mkdir(exist_ok=True)
assert not (o/'receipt.json').exists(), 'never resubmit an executed ID'
assert sha(PIN/'charon')=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
cmd=['timeout','540','taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+str(H/'charon-target'),'CARGO_BUILD_JOBS=4','RUSTFLAGS=-C link-arg=-Wl,--threads=4',str(PIN/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','*','--include','crate','--start-from',entry,'--dest-file',str(o/'PV_CX_Entry.llbc'),'--','--manifest-path',str(R/'tools/r1-cost-probe/Cargo.toml'),'--release','--locked','--offline','--bin','devnet_spend','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--jobs','4']
if len(sys.argv)>3:cmd[cmd.index('--dest-file'):cmd.index('--dest-file')]=json.loads(sys.argv[3])
pins={str(p.relative_to(R)):sha(p) for p in R.rglob('*') if p.is_file()}
(o/'command.json').write_text(json.dumps(dict(command=cmd,source_revision=rev,input_sha256=pins,tools={str(PIN/p):sha(PIN/p) for p in ['charon','charon-driver']},expected_work='Dependency compilation with release profile, followed by MIR extraction; no arithmetic gate or proof generation',profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False),entry=entry),indent=2)+'\n')
# Existing read-only admission scanner, followed immediately by launch in this process.
with (o/'reservation.log').open('w') as f:
 a=subprocess.run(['python3',str(H/'admission.py')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((o/'reservation.log').read_text());assert a.returncode==0 and ad.get('allowed') is True, ('admission refused',a.returncode)
G=H.parent/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py'
scope=['systemd-run','--user','--scope','--unit',f'PV_CX_N{n}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G),str(o/'barrier.json'),'python3',str(H/'native.py'),'inner',str(o),json.dumps(cmd)]
with (o/'launcher.log').open('w') as f:r=subprocess.run(scope,stdout=f,stderr=subprocess.STDOUT)
print(n,r.returncode,flush=True);sys.exit(r.returncode)
