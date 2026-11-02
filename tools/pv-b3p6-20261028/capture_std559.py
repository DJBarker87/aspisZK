"""Read-only source capture and body-token parity for the extracted nth helper."""
from pathlib import Path
import subprocess,json,hashlib,lzma,re
R=Path('evidence/pv-b3p6-20261028/resume18');O=R/'std559-source';O.mkdir(exist_ok=True)
code='''from pathlib import Path
import json,hashlib
names=['iter/range.rs','array/mod.rs','array/drain.rs','slice/mod.rs','slice/index.rs','ub_checks.rs','option.rs','panicking.rs','hint.rs','num/uint_macros.rs']
versions=['1.94.1','nightly-2026-06-01'];out=[]
for v in versions:
 root=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'
 for name in names:
  p=root/name;b=p.read_bytes();out.append(dict(version=v,name=name,path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(out))
'''
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
manifest=[];sources={}
for r in rows:
 b=r.pop('text').encode();assert hashlib.sha256(b).hexdigest()==r['sha256'];p=O/r['version']/(r['name']+'.xz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(b,preset=6));r['local_path']=str(p);r['bytes']=len(b);manifest.append(r);sources[(r['version'],r['name'])]=b.decode()
# The actual old opaque declaration has span 832 at the default implementation.
def body(s):
 start=s.index('default fn spec_nth(');brace=s.index('{',start);depth=1;i=brace+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[start:i]
a=body(sources[('1.94.1','iter/range.rs')]);b=body(sources[('nightly-2026-06-01','iter/range.rs')])
token=lambda s:re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*','',s))
assert token(a)==token(b)
out=dict(files=manifest,spec_nth=dict(instance='294:763ba5cae8a1b6e6a5de',token_identical=True,deployed_body=a,extractor_body=b,deployed_body_sha256=hashlib.sha256(a.encode()).hexdigest(),extractor_body_sha256=hashlib.sha256(b.encode()).hexdigest(),limitation='Only this default Rust item is compared here; no global std parity, specialization-selection or compiler-preservation claim. Primitive StepUsize laws and complete caller application remain separate.'))
(R/'STD-SOURCE-IDENTITY-D559.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(files=len(manifest),spec_nth_token_identical=True)))
