"""Recover exact historical receipt sources from immutable git or retained host files."""
from NEK_host import *
from NEK_scan import read_json,ROOT,sha
import lzma,sys
A=read_json(ROOT/'evidence/k3-audit-20261030/NEH_APPLICABILITY.json')
def recover(rp):
 row=next(r for r in A['receipts'] if r['receipt']==rp);out={};missing=[]
 for n,v in row.get('matched_sources',{}).items():
  src=v['source']
  if '::' in src:
   path,key=src.split('::',1)
   if path.endswith('.xz'):t=read_json(ROOT/path)[key]
   elif path.endswith('.patch'):
    from NEK_scan import patched_files
    # Some deltas are based on earlier harness additions; unresolved is explicit.
    t=dict(patched_files(((ROOT/path).read_text() if (ROOT/path).exists() else subprocess.check_output(['git','show','HEAD:'+path]).decode()))).get(key)
   else:t=None
  elif ':' in src and src.startswith('4bb3'):t=subprocess.check_output(['git','show',src]).decode()
  else:
   p=ROOT/src
   if p.exists():t=p.read_text()
   else:
    r=subprocess.run(['git','show','HEAD:'+src],capture_output=True);t=r.stdout.decode() if r.returncode==0 else None
  if t is not None and sha(t.encode())==v['sha256']:out[n]=t
  else:missing.append(dict(source=n,sha256=v['sha256']))
 missing+=row.get('missing_sources',[])
 # Strictly content-addressed recovery from reviewed source bundles/patch chains.
 bundles=[ROOT/'evidence/slice-q-compose-20261029/NEB_ADDITIVE_FILES.json']
 bundles+=list(E.glob('NEK_*_variants.json.xz'))+list(E.glob('NEK_*_chain.json.xz'))
 candidates={}
 for p in bundles:
  if p.exists():
   for k,t in read_json(p).items():
    if isinstance(t,str):candidates[sha(t.encode())]=t
 for item in missing:
  if item['sha256'] in candidates:out[item['source']]=candidates[item['sha256']]
 missing=[v for v in missing if v['source'] not in out]
 if missing:
  receipt=read_json(ROOT/rp);ni=receipt.get('native_command') or receipt['command'];manifest=ni[ni.index('--manifest-path')+1];base=manifest.split('/crates/')[0] if '/crates/' in manifest else manifest.split('/programs/')[0];hostdir=str(Path(base).parent)
  code=f'''from pathlib import Path
import json,hashlib
b=Path({hostdir!r});out={{}};missing={missing!r}
for item in missing:
 n=item['source'];p=b/n
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']:out[n]=p.read_text()
print(json.dumps(out))
'''
  r=py(code);assert r.returncode==0,r.stderr;out.update(json.loads(r.stdout))
 unresolved=[v for v in missing if v['source'] not in out]
 (E/('NEK_'+Path(rp).parent.name+'_recovered.json.xz')).write_bytes(lzma.compress(json.dumps(out,sort_keys=True).encode()))
 return out,unresolved
if __name__=='__main__':
 for rp in sys.argv[1:]:
  o,m=recover(rp);print(rp,len(o),'unresolved',m)
