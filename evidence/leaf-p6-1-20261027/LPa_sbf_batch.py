"""Serial job orchestration with unchanged S2H admission and S2W runner."""
from pathlib import Path
import subprocess,json,time,hashlib,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-1-20261027'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def collect(n):subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
ns=['default','devnet','pool']
for i,n in enumerate(ns,1):
 if len(sys.argv)>1 and i not in [int(a) for a in sys.argv[1:]]:continue
 a='LPa_SBF_'+n
 prior=len(list(E.glob(a+'-barrier-*.log')))
 for retry in range(prior,11):
  log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');collect(log)
  exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
  if not exists and retry==0:time.sleep(30);continue
  if exists:
   collect(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
   if r.returncode==0 and ad['allowed']:break
   if (r.returncode==78 or 'quiet window' in ad.get('reason','')) and retry<10:print(a,'reservation wait',flush=True);time.sleep(180);continue
  if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission '+r.stdout+r.stderr)
 else:raise SystemExit('STOP reservation retries')
 sources=['LPa_src/Cargo.toml','LPa_src/Cargo.lock']+['LPa_src/'+p for p in json.loads((E/'LPa_sources.json').read_text())]
 plan=json.loads(Path('evidence/sbf-identity-20261024/recapture-plan.json').read_text())['builds'][i-1]
 command=[x.replace('/home/dombarker/project-offloads/codex-cx-sbf-identity-20261024/src',B+'/LPa_src').replace('/home/dombarker/project-offloads/codex-cx-sbf-identity-20261024/capture-'+n+'-v1/artifacts',B+'/LPa_sbf_'+n) for x in plan['command']]
 env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_TARGET_DIR':B+'/LPa_sbf_target','CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS':'-C link-arg=--threads=4'}
 if n=='devnet':
  env.update({k:v for k,v in plan['environment'].items() if k in ['ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']})
 command=['/usr/bin/env','-u','RUSTFLAGS',*(['-u','ASPIS_R1_POOL_PROGRAM_ID','-u','ASPIS_R1_REGISTRY_PROGRAM_ID'] if n!='devnet' else []),*command]
 cfg=dict(attempt=a,kind='sbf',sources=sources,command=command,timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'release_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_delta':'cfg(kani)-only harnesses; original production spans preserved','expected_elf_sha256':plan['expected_sha256']},expected_time='optimized SBF compilation/linking only; no arithmetic gate',env=env,reservation_retries=retry)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 subprocess.run(['scp','-q',*[str(Path(f.removeprefix('LPa_src/'))) for f in sources if f.endswith('.rs')],H+':'+B+'/LPa_src/crates/aspis-r1-cost-probe/src/'],check=True)
 subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
 r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py {a}.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 (E/a).mkdir(exist_ok=True)
 for f in ['receipt.json','stdout.log','time.log']:collect(a+'/'+f)
 # Keep exact compiler input snapshots for every source in the run receipt.
 for f in sources:
  q=E/a/'sources'/f;q.parent.mkdir(parents=True,exist_ok=True)
  local=Path(f.removeprefix('LPa_src/'));q.write_bytes(local.read_bytes())
 rc=json.loads((E/a/'receipt.json').read_text());print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if rc['exit_status']!=0:
  print((E/a/'stdout.log').read_text()[-2500:],flush=True)
  if rc['exit_status'] in [124,137]:
   print('No unchanged retry; independent next harness only',flush=True)

 if rc['exit_status']!=0:raise SystemExit('STOP SBF '+a)
 artifact=B+'/LPa_sbf_'+n+('/aspis_pool.so' if n=='pool' else '/aspis_r1_cost_probe_program.so')
 check=ssh('sha256sum '+artifact+'; stat -c %s '+artifact)
 lines=check.stdout.splitlines();actual=lines[0].split()[0]
 comparison=dict(mode=n,artifact=artifact,sha256=actual,bytes=int(lines[1]),expected_sha256=plan['expected_sha256'],identical=actual==plan['expected_sha256'])
 (E/(a+'-comparison.json')).write_text(json.dumps(comparison,indent=2)+'\n')
 print(comparison,flush=True)
 if not comparison['identical']:raise SystemExit('STOP ELF mismatch')
