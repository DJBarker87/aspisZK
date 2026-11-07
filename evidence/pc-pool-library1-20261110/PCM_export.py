"""Copy own supporting objects to an immutable retained pickup directory."""
from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json,shutil
b=Path(B);d=b/'PCM_exports_20261110';d.mkdir(exist_ok=True);rows=[]
for p in sorted((b/'PCM_objects').glob('PCM_*')):
 if not p.is_file()or p.name.startswith('PCM_Scan.'):continue
 if not any(p.name.endswith(x)for x in ['.olean','.olean.private','.olean.server','.ir']):continue
 q=d/p.name;h=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 rows.append(dict(path=str(q),sha256=h,bytes=q.stat().st_size,module=p.name.split('.olean')[0].split('.ir')[0]))
j=dict(status='SUPPORTING_ONLY_FULL_GATE_BLOCKED',row_credit=0,export=str(d),files=rows)
(b/'PCM_EXPORT.json').write_text(json.dumps(j,indent=1)+'\\n');print(json.dumps(j))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\n'+code,text=True,capture_output=True)
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError(r.stderr)
(E/'PCM_EXPORT.json').write_text(r.stdout);print('PCM supporting export copied and hash pinned')
