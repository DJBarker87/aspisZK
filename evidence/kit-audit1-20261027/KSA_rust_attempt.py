from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027';a=sys.argv[1] if len(sys.argv)>1 else 'KSA_R001'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
assert not (E/a/'receipt.json').exists()
r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier-0.log 2>&1');get(a+'-barrier-0.log');get(a+'-reservation.json')
ad=json.loads((E/(a+'-reservation.json')).read_text());(E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,allowed=ad['allowed']))+'\n')
if r.returncode or not ad['allowed']:raise SystemExit('WAIT admission refused; no submission')
if a=='KSA_R001':subprocess.run(['python3',str(E/'KSA_native_prepare.py')],check=True)
else:
 if a in ['KSA_R003','KSA_R004','KSA_R005','KSA_R006']:
  subprocess.run(['scp','-q',str(E/'KSA_native_test.rs'),H+':'+B+'/KSA_native_test.rs'],check=True)
  body="from pathlib import Path\np=Path("+repr(B+'/KSA_src/crates/aspis-core/src/lib.rs')+")\ns=p.read_text().split('\\n#[cfg(test)]\\nmod KSA_diagnostic')[0]\np.write_text(s+Path("+repr(B+'/KSA_native_test.rs')+").read_text())\n"
  rr=ssh("python3 - <<'PYHOST'\n"+body+"PYHOST");assert rr.returncode==0,rr.stderr
 import hashlib
 paths=['results/r0-opening-20261009/kats.json','results/r0-opening-20261009/transport-kat.json','results/r0-codes-20261009/kats.txt','results/r0-samplers-20261009/kats.json']
 rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 arch=subprocess.Popen(['git','archive',rev,'--']+paths,stdout=subprocess.PIPE)
 rr=subprocess.run(['ssh',H,'tar -xf - -C '+B+'/KSA_src'],stdin=arch.stdout);arch.stdout.close();assert arch.wait()==0 and rr.returncode==0
 mf=json.loads((E/'KSA_native_sources.json').read_text())
 for path in paths:
  if not any(x['path']==path for x in mf['files']):mf['files'].append(dict(path=path,sha256=hashlib.sha256(subprocess.check_output(['git','show',rev+':'+path])).hexdigest()))
 (E/'KSA_native_sources.json').write_text(json.dumps(mf,indent=2)+'\n')
manifest=json.loads((E/'KSA_native_sources.json').read_text())
cfg=dict(attempt=a,kind='rust',module=None,sources=['KSA_native.py','KSA_native_test.rs']+['KSA_src/'+r['path'] for r in manifest['files']],command=['python3','KSA_native.py'],timeout=300,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision=manifest['revision'],source_tree_dirty=True,env={'CARGO_NET_OFFLINE':'true'},deps_fingerprint={'frozen_lock_sha256':next(x['sha256'] for x in manifest['files'] if x['path']=='Cargo.lock'),'scope':'frozen release native plus appended cfg(test) wrapper'},expected_time='optimized compilation of core unit-test binary; then tiny fixed input differentials, no elimination/proof generation')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
for n in ['KSA_graph.json','KSA_lock.json','KSA_metadata_stderr.log']:
 if ssh('test -f '+B+'/'+n).returncode==0:
  get(n);(E/a/n).write_bytes((E/n).read_bytes())
x=json.loads((E/a/'receipt.json').read_text());print({k:x[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']});print((E/a/'stdout.log').read_text()[-4500:])
