from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111');out=b/'NNK_failures/NNK_L048';out.mkdir(parents=True,exist_ok=True)
roots=json.loads((b/'NNK_AUDIT_ROOTS.json').read_text())['groups'][48];rows=[];files={}
for i,r in enumerate(roots):
 p=b/('NEP_proof48_'+r+'_REACHABLE.txt')
 if not p.exists():continue
 q=out/p.name
 if not q.exists():shutil.copy2(p,q)
 raw=q.read_bytes();assert hashlib.sha256(raw).hexdigest()==hashlib.sha256(p.read_bytes()).hexdigest()
 rows.append(dict(index=i,root=r,path=str(q),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),mtime=p.stat().st_mtime));files[p.name]=raw.decode()
print(json.dumps(dict(rows=rows,files=files)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;x=json.loads(r.stdout)
for name,text in x.pop('files').items():
 p=E/('NNK_FAILURE48_'+name);raw=text.encode();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=1));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
x.update(status='PARTIAL_UNCREDITED',attempt='NNK_L048',completed_child_receipts=0,retained_failure_source='NNK_L048/receipt.json',cause='Uniform full-library field closure walk;55 partial reachable files over152.055s, no single stalled root. Wide aggregation shape retired. Windows at most30 full-library fields; same timeout/caps. No credit from these partial files.')
(E/'NNK_FAILURE48_RECOVERY.json').write_text(json.dumps(x,indent=1)+'\n');print('retained partial files',len(x['rows']))
