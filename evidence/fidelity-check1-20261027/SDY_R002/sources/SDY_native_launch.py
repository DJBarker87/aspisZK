from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-fidelity-check1-20261027';a='SDY_R002'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True);subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
files=['SDY_native.py']+[f'SDY_native_test_{n}.rs' for n in ['sampler','verifier','multiproof']]+[f'SDY_frozen_{n}.rs.txt' for n in ['sampler','verifier','multiproof']]
for n in files:subprocess.run(['scp','-q',str(E/n),H+':'+B+'/'+n],check=True)
# A scratch overlay of retained frozen source: unchanged files are read-only symlinks,
# only lock and three cfg(test)-extended sources have private bytes.
setup='''from pathlib import Path
import hashlib,json
b=Path("'''+B+'''");src=Path('/home/dombarker/project-offloads/codex-cx-sampler-diag-20261027/SDX_src');dst=b/'SDY_src'
dst.mkdir(exist_ok=True)
for p in src.rglob('*'):
 q=dst/p.relative_to(src)
 if p.is_dir():q.mkdir(parents=True,exist_ok=True)
 elif not q.exists():q.symlink_to(p)
q=dst/'Cargo.lock';q.unlink();q.write_bytes((src/'Cargo.lock').read_bytes())
for n in ['sampler','verifier','multiproof']:
 q=dst/f'crates/aspis-r1-cost-probe/src/{n}.rs';q.unlink();q.write_bytes((b/f'SDY_frozen_{n}.rs.txt').read_bytes()+(b/f'SDY_native_test_{n}.rs').read_bytes())
'''
r=subprocess.run(['ssh',H,'python3 -'],input=setup,text=True,capture_output=True);assert r.returncode==0,r.stderr
cfg=dict(attempt=a,kind='rust',module='SDY four functions twelve fixtures',sources=files+['SDY_src/Cargo.lock'],command=['python3','SDY_native.py'],timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',env={'CARGO_NET_OFFLINE':'true'},deps_fingerprint={},expected_time='release compilation, then twelve tiny write-path fixtures',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json');(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
for n in ['SDY_graph.json','SDY_lock.json','SDY_metadata_stderr.log']:
 if ssh(f'test -f {B}/{n}').returncode==0:get(n)
print((E/a/'stdout.log').read_text()[-10000:]);print((E/a/'receipt.json').read_text())
