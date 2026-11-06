"""Raw reachable outputs: hash reuse for unchanged inherited artifacts, own xz otherwise."""
from NLK_formal import *
import base64
baseline={}
for d,n in [('ledger21-20261110','NLG'),('tx2-adapters3-20261109','NLA'),('sdk-borrow-20261109','NLF')]:
 for p in (E.parent/d).glob('*REACHABLE.txt.sha256'):
  h=p.read_text().split()[0];z=p.with_suffix('.xz')
  if z.exists():baseline.setdefault(h,dict(path=str(z.relative_to(E.parent.parent)),sha256=h,archive_sha256=sha(z.read_bytes())))
script='''from pathlib import Path
import json,hashlib,lzma
b=Path.cwd();old=json.loads((b/'NLK_RAW_BASELINE.json').read_text());rows=[];new=b/'NLK_raw';new.mkdir(exist_ok=True)
for p in sorted(b.glob('NEP_*_REACHABLE.txt')):
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();row=dict(name=p.name,sha256=h,bytes=len(raw))
 if h in old:row['reused']=old[h]
 else:
  q=new/(h+'.xz')
  if not q.exists():q.write_bytes(lzma.compress(raw))
  row['archive']=str(q.relative_to(b));row['archive_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append(row)
(b/'NLK_RAW_REFERENCES.json').write_text(json.dumps(rows,indent=1)+'\\n')
print(json.dumps(dict(raw_files=len(rows),new_archives=len(list(new.glob('*.xz'))),reused=sum('reused' in r for r in rows))))
'''
r=run('NLK_L093','cache','NLK_RawRetention',['python3','NLK_raw_retention.py'],extra={'NLK_raw_retention.py':script,'NLK_RAW_BASELINE.json':json.dumps(baseline)});assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});rows=json.loads((b/'NLK_RAW_REFERENCES.json').read_text());names=sorted({{r['archive'] for r in rows if 'archive' in r}})
print(json.dumps(dict(rows=rows,archives={{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}})))
''');assert r.returncode==0
x=json.loads(r.stdout)
for n,v in x['archives'].items():
 p=E/n;p.parent.mkdir(exist_ok=True);p.write_bytes(base64.b64decode(v))
(E/'NLK_RAW_REFERENCES.json').write_text(json.dumps(x['rows'],indent=1)+'\n')
print(json.dumps(dict(raw_files=len(x['rows']),new_archives=len(x['archives']),reused=sum('reused' in r for r in x['rows']))))
