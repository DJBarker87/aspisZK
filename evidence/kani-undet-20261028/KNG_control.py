"""Task inputs for the existing S2W runner; no shared infrastructure changes."""
from pathlib import Path
import subprocess,json,shlex,time,sys,hashlib,zlib,base64
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def ssh(s,submitted=False):
 for n in range(10):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,s],capture_output=True,text=True)
  with (E/'KNG_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(command=s,trial=n,submitted=submitted,exit=r.returncode,stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<9:time.sleep(60)
 raise SystemExit('STOP persistent transport failure')
def py(s,submitted=False):return ssh('python3 -c '+shlex.quote(s),submitted)
def admit(a):
 for n in range(11):
  r=py(f'''from pathlib import Path
import subprocess,json
b=Path({B!r});p=b/{(a+'-barrier-'+str(n)+'.log')!r};j=b/{(a+'-reservation-'+str(n)+'.json')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(j)],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,log=p.read_text(),reservation=json.loads(j.read_text()) if j.exists() else None)))''')
  assert r.returncode==0,r.stderr
  x=json.loads(r.stdout);(E/f'{a}-admission-{n}.json').write_text(json.dumps(x,indent=2)+'\n')
  if x['reservation'] is None:
   if n==0:time.sleep(30);continue
   raise SystemExit('STOP missing reservation')
  if x['exit']==0 and x['reservation'].get('allowed') is True:return
  if (x['exit']==78 or x['reservation'].get('allowed') is False) and n<10:time.sleep(180);continue
  raise SystemExit('STOP infrastructure reservation failure')
 raise SystemExit('STOP admission exhausted')
def launch(a,kind,cmd,sources,features=None):
 assert not (E/a/'receipt.json').exists(),'no unchanged reruns'
 if kind=='kani':
  assert len(list(E.glob('KNG_K*/receipt.json')))<60,'whole Kani budget'
 admit(a)
 cfg=dict(attempt=a,kind=kind,command=cmd,sources=sources,timeout=600,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_DEV_OVERFLOW_CHECKS':'true','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':B+'/KNG_target','TMPDIR':B+'/KNG_tmp'},deps_fingerprint={'frozen_revision':REV},expected_time='optimized compilation then named CBMC property; no arithmetic aggregation',resolved_features_per_crate=features)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=py(f'from pathlib import Path;Path({B+"/"+a+".json"!r}).write_text({json.dumps(cfg)!r})');assert r.returncode==0,r.stderr
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 # A submitted transport failure is recovered read-only, never resubmitted.
 r=py(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/{a!r}/n).read_text() for n in ['receipt.json','stdout.log','time.log'] if (b/{a!r}/n).exists()}}))''');assert r.returncode==0,r.stderr
 logs=json.loads(r.stdout);assert 'receipt.json' in logs,'STOP unresolved submitted run'
 (E/a).mkdir()
 for n,t in logs.items():(E/a/n).write_text(t)
 return json.loads(logs['receipt.json'])
if __name__=='__main__':
 if sys.argv[1] in ['setup','overlay']:
  if sys.argv[1]=='setup':
   admit('KNG_SETUP')
   r=py(f'''from pathlib import Path
 import shutil
 b=Path({B!r});assert not (b/'KNG_src').exists();(b/'KNG_src').mkdir();(b/'KNG_tmp').mkdir(exist_ok=True)
 shutil.copyfile('/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/S2W_run_host.py',b/'S2W_run_host.py')''');assert r.returncode==0,r.stdout+r.stderr
   paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
   # First and only source scratch for this job; persistent shared cache retained.
   p=subprocess.Popen(['git','archive',REV,*paths],stdout=subprocess.PIPE);r=subprocess.run(['ssh',H,'tar -xf - -C '+B+'/KNG_src'],stdin=p.stdout,capture_output=True,text=True);p.stdout.close();assert p.wait()==0 and r.returncode==0,r.stderr
  payload={p.name:p.read_text() for p in E.glob('*.rs.txt')}
  r=py(f'''from pathlib import Path
import json,zlib,base64
b=Path({B!r})/'KNG_src';mods=json.loads(zlib.decompress(base64.b64decode({base64.b64encode(zlib.compress(json.dumps(payload).encode())).decode()!r})))
for name,text in mods.items():
 crate='aspis-r1-cost-probe' if name=='KNG_LPi_contracts.rs.txt' else 'aspis-statement'
 if name=='KNG_KMX_stubs.rs.txt':
  for c in ['aspis-statement','aspis-r1-cost-probe']:(b/'crates'/c/'src/KNG_KMX_stubs.rs').write_text(text)
  continue
 parent='lib' if name=='KNG_LPi_contracts.rs.txt' else 'pool_v1/pair_tree_profile' if 'NBH_live' in name else 'pool_v1/pair_forest_terminal' if 'NBU_more' in name else 'pool_v1/pair_terminal'
 src=b/'crates'/crate/'src';dest=src/(name[:-4] if parent=='lib' else 'pool_v1/'+name[:-4]);dest.write_text(text)
 with (src/(parent+'.rs')).open('a') as f:f.write('\\n#[cfg(kani)]\\nmod '+name[:-7]+';\\n')
for c in ['aspis-statement','aspis-r1-cost-probe']:
 p=b/'crates'/c/'src/lib.rs';s=p.read_text();p.write_text('#![feature(allocator_api,next_index)]\\n'+s+'\\n#[cfg(kani)]\\n#[path="KNG_KMX_stubs.rs"]\\nmod KMX_stubs;\\n')
''');assert r.returncode==0,r.stdout+r.stderr
  (E/'KNG_SETUP.json').write_text(json.dumps(dict(frozen_revision=REV,paths="frozen archive paths recorded in KNG_control.py",archive_exit=0,existing_runner_copied_unchanged=True),indent=2)+'\n')
