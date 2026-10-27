"""Find uniquely source-attested missing dependency modules in committed evidence.
No source selection by approximate similarity or by module name alone.
"""
from pathlib import Path
import subprocess,json,re,hashlib,collections
O=Path(__file__).parent
wanted={r['module'] for r in json.loads((O/'EJS_frontier.json').read_text())['missing_unselected']}
records=collections.defaultdict(list)
files=subprocess.check_output(['git','ls-files'],text=True).splitlines()
sha_re=re.compile('[0-9a-f]{64}')
def add(m,s,p,context):
 if m in wanted and isinstance(s,str) and sha_re.fullmatch(s):records[m].append(dict(sha256=s,evidence=p,context=context))
def walk(x,p):
 if isinstance(x,list):
  for v in x:walk(v,p)
 elif isinstance(x,dict):
  m=x.get('module',x.get('name'))
  if isinstance(m,str):
   m=m.removesuffix('.lean').replace('.','/')
   if m in wanted and x.get('source_sha256'):add(m,x['source_sha256'],p,'explicit module/source_sha256')
  for key in ['source','source_path','path','file','frozen_source','src']:
   path=x.get(key)
   if not isinstance(path,str):continue
   if path.endswith(('.lean','.lean.txt')):
    for m in wanted:
     if path.endswith('/'+m+'.lean') or path.endswith('/'+m+'.lean.txt') or path==m+'.lean':
      add(m,x.get('source_sha256',x.get('sha256')),p,key+'='+path)
  for v in x.values():
   if isinstance(v,(dict,list)):walk(v,p)
for p in files:
 if not p.endswith(('.json','.jsonl')) or p.startswith(('evidence/envj-rebuild','evidence/privacy-recount-')):continue
 try:
  raw=Path(p).read_text()
  if not any(m.split('/')[-1] in raw for m in wanted):continue
  for x in ([json.loads(l) for l in raw.splitlines() if l.strip()] if p.endswith('.jsonl') else [json.loads(raw)]):walk(x,p)
 except (ValueError,UnicodeError,OSError):pass
print('attested modules',len(records),flush=True)
unique={m:rs for m,rs in records.items() if len({r['sha256'] for r in rs})==1}
wanted_hashes={rs[0]['sha256'] for rs in unique.values()};resolved={}
# Check exact HEAD blobs and previously resolved historical blobs.
old=json.loads((O.parent/'envj-rebuild-20261026/EJR_final-inventory.json').read_text())['resolved']
for s in wanted_hashes:
 if s in old:resolved[s]=old[s]
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for line in subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines():
 meta,p=line.split('\t',1)
 if not p.endswith(('.lean','.lean.txt')):continue
 oid=meta.split()[2];proc.stdin.write((oid+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split();n=int(head[2]);b=proc.stdout.read(n);proc.stdout.read(1);s=hashlib.sha256(b).hexdigest()
 if s in wanted_hashes and s not in resolved:resolved[s]=dict(blob=oid,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),path=p,bytes=n)
proc.terminate()
ready=[]
for m,rs in unique.items():
 s=rs[0]['sha256']
 if s in resolved:ready.append(dict(module=m,source_sha256=s,**resolved[s],attestations=rs))
report=dict(ready=ready,ambiguous={m:rs for m,rs in records.items() if m not in unique},unique_hash_not_resolved={m:rs for m,rs in unique.items() if rs[0]['sha256'] not in resolved},unattested=sorted(wanted-records.keys()),rule='Only unique explicit recorded source hashes resolved to exact git blobs are eligible. Original 19 selected and 329 variant hash failures remain unchanged; this list concerns previously unselected dependencies.')
(O/'EJS_frontier-inventory.json').write_text(json.dumps(report,indent=2)+'\n');print('eligible',len(ready),'ambiguous',len(report['ambiguous']),'unresolved',len(report['unique_hash_not_resolved']),'unattested',len(report['unattested']))
