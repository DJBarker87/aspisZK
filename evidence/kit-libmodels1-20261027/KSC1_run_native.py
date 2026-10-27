from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-libmodel1-cache-20261027';a=sys.argv[1] if len(sys.argv)>1 else 'KSC1_R001';assert int(a.rsplit('R',1)[1])<=10
def ssh(s):return subprocess.run(['ssh','-o','ConnectTimeout=20',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True);subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
assert not (E/a).exists()
for retry in range(11):
 r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier-{retry}.log 2>&1');get(a+f'-barrier-{retry}.log');get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
 if r.returncode==0 and ad['allowed']:break
 if retry<10 and (r.returncode==78 or not ad['allowed']):time.sleep(60);continue
 raise SystemExit('STOP admission')
(E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,allowed=ad['allowed'],retry=retry)))
cfg=dict(attempt=a,kind='rust',sources=['KSC1_native.py','KSC1_native_test.rs'],command=['python3','KSC1_native.py'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'CARGO_NET_OFFLINE':'true'},deps_fingerprint={'frozen_lock_sha256':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','stdlib_toolchain':'1.94.1/e408947bf','mode':'std-only scratch rustc -O cfg(test); frozen Cargo graph metadata validated first; no release crate build'},expected_time='offline graph validation, optimized std-only compilation, then tiny branch probes; no elimination or proof generation')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
for n in ['KSC1_native.py','KSC1_native_test.rs','KSC1_frozen_manifest.json',a+'.json']:subprocess.run(['scp','-q',str(E/n),H+':'+B+'/'+n],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json');(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
if r.returncode==255:raise SystemExit('Submitted: recover READ ONLY after 60 s; do not resubmit')
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
for n in ['KSC1_graph.json','KSC1_lock.json','KSC1_metadata_stderr.log','KSC1_graph_edges.json']:get(n)
print((E/a/'stdout.log').read_text()[-5500:]);print((E/a/'receipt.json').read_text()[-1200:])
