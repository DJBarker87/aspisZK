from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-14-20261027'
files=json.loads((E/'LPp_SOURCE.json').read_text())['files']
code='''from pathlib import Path
import hashlib,json
B=Path('''+repr(B)+''')/'LPp_src'
files='''+repr(files)+'''
out={}
for rel,pin in files.items():
 b=(B/rel).read_bytes();n=pin['size'];prefix=hashlib.sha256(b[:n]).hexdigest()==pin['frozen_sha256']
 out[rel]={'frozen_sha256':pin['frozen_sha256'],'scratch_sha256':hashlib.sha256(b).hexdigest(),'frozen_is_exact_prefix':prefix,'suffix':b[n:].decode() if prefix else None}
print(json.dumps(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,"python3 - <<'AUDIT'\n"+code+'\nAUDIT'],capture_output=True,text=True)
 with (E/'LPp_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'step':'source audit','retry':retry,'exit':r.returncode,'stderr':r.stderr})+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or retry==10:raise SystemExit('STOP source-audit transport')
 print('source audit transport wait60',retry,flush=True);time.sleep(60)
x=json.loads(r.stdout);(E/'LPp_NATIVE_SOURCE_AUDIT.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x,indent=2))
