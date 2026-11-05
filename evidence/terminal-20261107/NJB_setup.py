from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger13-20261107'
B='/home/dombarker/project-offloads/codex-cx-terminal-20261107';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJB_20261107'
seed=json.loads((P/'NIU_EXPORT.json').read_text())['files']
paths=[C+'/NIU_seed']+json.loads((P/'NIU_PATHS.json').read_text())
(E/'NJB_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
code='''from pathlib import Path
import json,subprocess,shutil,hashlib,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'NJB_seed-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NJB_seed-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NJB_seed-reservation.json';print(json.dumps(dict(exit=r.returncode,reservation=json.loads(p.read_text()) if p.exists() else None)),flush=True)
if not p.exists() or r.returncode or json.loads(p.read_text()).get('allowed') is not True:sys.exit(78)
c=Path(C)/'NIU_seed';c.mkdir(parents=True,exist_ok=True);out=[]
for row in seed:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'];q=c/p.name
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
 out.append(dict(row,destination=str(q)))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 q=b/n
 if not q.exists():shutil.copy2(w/n,q)
print(json.dumps(dict(files=out,bytes=sum(x['bytes']for x in out),disk=shutil.disk_usage(b)._asdict())))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nseed='+repr(seed)+'\n'+code,text=True,capture_output=True)
(E/'NJB_SEED.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
lines=r.stdout.splitlines();(E/'NJB_SEED.json').write_text(json.dumps([json.loads(l)for l in lines],indent=1)+'\n')
s=(E.parent/'verify-observed4-20261107/NIH_run.py').read_text().replace('NIH_','NJB_').replace('codex-cx-verify-observed4-20261107','codex-cx-terminal-20261107').replace("{'L':90,'K':100,'E':1}","{'L':100,'K':120,'E':1}")
s=s.replace("print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-3500:]);sys.exit(rc['exit_status'])", "print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])")
(E/'NJB_run.py').write_text(s)
print('NIU seed copied and verified: '+str(sum(x['bytes']for x in seed))+' bytes; existing launcher unchanged')
