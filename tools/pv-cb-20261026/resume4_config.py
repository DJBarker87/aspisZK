"""Trivial configuration diagnosis, at most three probes in this allocation."""
from pathlib import Path
import subprocess,shlex,json,sys,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
name=sys.argv[1];affinity=len(sys.argv)>2 and sys.argv[2]=='affinity4'
assert re.fullmatch(r'kani-config-00[23](?:-r[0-9]+)?',name)
completed_probes=[p for p in ev.glob('kani-config-*/collected-receipt.json') if json.loads(p.read_text()).get('attempt_charged')]
assert len(completed_probes)<3,'Configuration diagnosis three-probe budget exhausted'
base='/home/dombarker/project-offloads/codex-pv-cb-20261026';host='dombarker@100.108.41.90'
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
out=ev/name;out.mkdir(exist_ok=True);dest=base+'/'+name
assert not (out/'target.json').exists()
def ssh(cmd):return subprocess.run(['ssh',host,cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
r=ssh(f'mkdir -p {dest}; python3 {scanner} {dest}/admission-before.json > {dest}/reservation.log 2>&1')
(out/'reservation-transport.log').write_text(r.stdout)
if r.returncode:print(name,'reservation refusal',r.returncode);sys.exit(r.returncode)
for f in ['Cargo.toml','lib.rs']:
 subprocess.run(['scp',str(root/'tools/pv-cb-20261026/config-probe'/f),host+':'+base+'/config-probe/'+f],check=True)
# Probe3 changes CPU fanout and intentionally starts from its own cold probe cache.
# Only this disposable compilation directory is removed; no source, tool or key.
if affinity:assert ssh('rm -rf '+base+'/config-target').returncode==0
cmd=(["taskset","--cpu-list","0-3"] if affinity else [])+['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/bin:/usr/local/bin:/usr/bin:/bin',f'CARGO_TARGET_DIR={base}/config-target','RUSTFLAGS=--cfg kani','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',base+'/config-probe/Cargo.toml','--lib','--harness','config_probe','--solver','kissat','--output-format','terse','-j','4']
meta=dict(target=cmd,classification='uncharged configuration diagnosis, within three-probe limit',expected_time='cold dependency compilation under the historical Cargo graph, then trivial arbitrary-u8 identity; no dense arithmetic proof',profile='config-probe profile.dev opt-level3',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),affinity4=affinity,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/'target.json').write_text(json.dumps(meta,indent=2)+'\n')
args=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',dest+'/time.log',*cmd]
r=ssh(shlex.join(args)+' > '+dest+'/output.log 2>&1');(out/'transport.log').write_text(r.stdout)
subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/collect_native.py'),name,'config-probe/Cargo.toml','config-probe/lib.rs','config-probe/Cargo.lock','source/Cargo.lock'],check=True)
p=out/'collected-receipt.json';rec=json.loads(p.read_text());rec.update(meta);rec['attempt_charged_to_kani_budget']=False;p.write_text(json.dumps(rec,indent=2)+'\n')
print(name,'exit',rec['exit']);sys.exit(r.returncode)
