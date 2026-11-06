from NLF_formal import *
import base64
files={n:(E/n).read_text() for n in ['NLF_AUDIT_ROOTS.json','NLF_EXPECTED_IMPORTS.jsonl','NLF_AUDIT_MODULES.json','NLF_audit_one.py']}
for i,mode,name in [(79,'proof0','NLF_ProofDriver'),(80,'scan','NLF_ScanDriver')]:
 r=run(f'NLF_L{i:03d}','audit',mode,['python3','NLF_audit_one.py','NLF_native/'+name,mode],files)
 rr=ssh('python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NLF_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NLF_LOADED_scan.jsonl']
out=[]
for p in paths:
 if p.exists():
  raw=p.read_bytes();out.append(dict(name=p.name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),data=base64.b64encode(lzma.compress(raw)).decode()))
print(json.dumps(out))
''');assert rr.returncode==0,rr.stderr
 for x in json.loads(rr.stdout):
  p=E/('NLF_'+x['name']);raw=lzma.decompress(base64.b64decode(x['data']));assert sha(raw)==x['sha256']
  if p.suffix=='.json':p.write_bytes(raw)
  else:p.with_name(p.name+'.xz').write_bytes(base64.b64decode(x['data']));p.with_name(p.name+'.sha256').write_text(x['sha256']+'\n')
 assert r['exit_status']==0,(mode,'Audit STOP; inspect exact output, no unchanged rerun')
print('NLF second/final combined audit complete; same compiled fixture-tested binaries retained')
