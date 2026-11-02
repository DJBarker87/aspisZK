"""Read-only capture of the exact array IntoIter constructor/fold source.
Numeric projection only; transmute, region, drop and restoration stay OPEN.
"""
from pathlib import Path
import json,hashlib,lzma,subprocess,re
R=Path('evidence/pv-b3p6-20261028/resume18');O=R/'std571-source'
code='''from pathlib import Path
import json,hashlib
out=[]
for v in ['1.94.1','nightly-2026-06-01']:
 for name in ['array/iter.rs','array/iter/iter_inner.rs']:
  p=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'/name
  b=p.read_bytes();out.append(dict(version=v,name=name,path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(out))
'''
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True));src={}
for r in rows:
 s=r.pop('text');b=s.encode();assert hashlib.sha256(b).hexdigest()==r['sha256'];p=O/r['version']/(r['name']+'.xz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(b,preset=6));r['local_path']=str(p);r['bytes']=len(b);src[(r['version'],r['name'])]=s
# Record the entire bodies: differences are findings to inspect, never hidden.
def item(s,needle):
 a=s.index(needle);b=s.index('{',a);i=b+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
items=[]
for name,needle in [('array/iter.rs','fn into_iter(self)'),('array/iter.rs','fn fold<'),('array/iter/iter_inner.rs','const unsafe fn new_unchecked'),('array/iter/iter_inner.rs','fn try_fold<')]:
 bodies={v:item(src[(v,name)],needle)for v in ['1.94.1','nightly-2026-06-01']};items.append(dict(name=name,needle=needle,bodies=bodies,body_tokens_identical=tok(bodies['1.94.1'])==tok(bodies['nightly-2026-06-01'])))
x=dict(source_capture=rows,items=items,numeric_lemma='PV_B3P_CounterGuards571227.initial_cursor_handler_independent',constructor_projection='inspect exact constructor before credit; source state includes transmute and drop fields',full_source_association=False,pointer_borrow_drop='OPEN',premises_removed=[])
(R/'ARRAY-CURSOR-SOURCE-D571.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(items=[{k:i[k]for k in ['needle','body_tokens_identical']}for i in items])))
