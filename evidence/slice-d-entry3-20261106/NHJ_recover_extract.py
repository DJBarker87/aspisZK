"""Read-only recovery of the successful extraction's exact generated LLBC input."""
from pathlib import Path
import subprocess,json,base64,hashlib,lzma,time,sys
E=Path(__file__).resolve().parent
a=sys.argv[1] if len(sys.argv)>1 else "NHJ_E001";assert a in ["NHJ_E001","NHJ_E002"]
cmd="from pathlib import Path;import lzma,hashlib,base64,json;p=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry3-20261106/NHJ_E001.llbc');b=p.read_bytes();print(json.dumps(dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),xz=base64.b64encode(lzma.compress(b)).decode())))"
cmd=cmd.replace("NHJ_E001",a)
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=cmd,capture_output=True,text=True)
 (E/f'{a}-recover-{retry}.log').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError('Read-only recovery failed; do not resubmit extraction')
x=json.loads(r.stdout);arc=base64.b64decode(x.pop('xz'));b=lzma.decompress(arc);assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256']
(E/(a+'.llbc.xz')).write_bytes(arc);(E/(a+'.llbc.sha256')).write_text(x['sha256']+'\n');(E/(a+'_LLBC_PIN.json')).write_text(json.dumps(x,indent=1)+'\n')
template=E/'NHJ_extracted/NHJ_SnapshotReference/NHJ_SnapshotReference/FunsExternal_Template.lean'
if template.exists():
 b=template.read_bytes();template.with_suffix('.lean.xz').write_bytes(lzma.compress(b));template.with_suffix('.lean.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');template.unlink()
print(json.dumps(dict(status='RECOVERED_READ_ONLY',**x,template='Uncompiled tool-generated axiom template retained compressed; actual FunsExternal is an ordinary definition, no axiom')))
