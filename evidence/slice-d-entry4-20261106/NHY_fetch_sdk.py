"""Read-only source pinning for the exact frozen SDK syscall wrappers."""
from pathlib import Path
import subprocess,json,lzma,hashlib,time,resource,sys
E=Path(__file__).resolve().parent;start=time.monotonic()
code='''from pathlib import Path
import json,hashlib
base=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
paths=[base/n/'src/lib.rs' for n in ['solana-msg-2.2.1','solana-cpi-2.2.1','solana-pubkey-2.4.0']]
print(json.dumps({str(p):p.read_text() for p in paths}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
rows=[]
for path,text in json.loads(r.stdout).items():
 data=text.encode();h=hashlib.sha256(data).hexdigest();n=Path(path).parts[-3];p=E/('NHY_SDK_'+n+'.rs.xz');p.write_bytes(lzma.compress(data));Path(str(p)[:-3]+'.sha256').write_text(h+'  '+n+'/src/lib.rs\n');rows.append(dict(source=path,sha256=h,archive=p.name,bytes=len(data)))
(E/'NHY_SDK_SOURCE_PINS.json').write_text(json.dumps(dict(rows=rows,authority='Exact package versions selected in every deployed frozen-lock graph; wrappers inspected under target_os=solana. Native tests prove arguments only; no syscall value/effect simulation.',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),print_axioms='N/A read-only SDK source recovery'),indent=1)+'\n');print('pinned',len(rows),'SDK source files')
