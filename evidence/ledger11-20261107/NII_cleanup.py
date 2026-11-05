"""Remove only hash-verified own rebuildable workspace outputs after retention."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger11-20261107';exports=json.loads((E/'NII_EXPORT.json').read_text())
files=[]
for p in E.glob('NII_NEP_*_REACHABLE.txt.sha256'):files.append(dict(path=str(Path(B)/p.name.removeprefix('NII_').removesuffix('.sha256')),sha256=p.read_text().strip(),class_='downloaded raw graph'))
for f in exports['files']:files.append(dict(path=f['source'],retained=f['path'],sha256=f['sha256'],class_='exported own object'))
for n in ['NII_ProofDriver','NII_Driver']:
 x=json.loads((E/'NII_L009'/(n+'_BINARY_PIN.json')).read_text());files.append(dict(path=B+'/NII_native/'+n,sha256=x['sha256'],class_='rebuildable own executable'))
code='''from pathlib import Path
import json,hashlib,subprocess,shutil
b=Path(B);done=[]
ps=subprocess.check_output(['ps','-eo','args'],text=True).splitlines()
active=[line for line in ps if ('S2W_run_host.py NII_'in line or (B+'/NII_native/'in line and ('NII_ProofDriver'in line or'NII_Driver'in line)))]
assert not active,active
for f in files:
 p=Path(f['path']);assert p.is_relative_to(b)and p.is_file(),str(p)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],str(p)
 if 'retained'in f:
  q=Path(f['retained']);assert q.is_file()and hashlib.sha256(q.read_bytes()).hexdigest()==f['sha256']
 size=p.stat().st_size;p.unlink();done.append(dict(f,bytes=size))
cache=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104')
usage=shutil.disk_usage(b);du=subprocess.run(['du','-sk',str(cache)],capture_output=True,text=True)
result=dict(removed=done,removed_bytes=sum(r['bytes']for r in done),cache_retained=str(cache),cache_deleted=False,keys_handled=False,du_cache_kib=du.stdout.strip(),disk_free_bytes=usage.free,all_source_evidence_retained=True,active_own_provers=active)
(b/'NII_HOST_END.json').write_text(json.dumps(result,indent=1));print(json.dumps({k:v for k,v in result.items()if k!='removed'}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nfiles='+repr(files)+'\n'+code,capture_output=True,text=True)
(E/'NII_CLEANUP_TRANSPORT.log').write_text(r.stdout+r.stderr);print(r.stdout,r.stderr);assert r.returncode==0
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NII_HOST_END.json'],capture_output=True);assert r.returncode==0;(E/'NII_HOST_END.json').write_bytes(r.stdout)
