import subprocess,json,hashlib,re,collections
from pathlib import Path
O=Path('evidence/envj-rebuild-20261026'); REV=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
files=subprocess.check_output(['git','ls-files'],text=True).splitlines()
records=[]; attempts=set(); hints=collections.defaultdict(set); census=collections.defaultdict(set)
def add(ws,m,s,p,src=None,rank=0,attempt=None):
 if not m or not re.fullmatch('[0-9a-f]{64}',str(s)):return
 m=m.removesuffix('.lean').replace('.','/'); records.append(dict(workspace=ws,module=m,sha256=s,evidence=p,source_hint=src,rank=rank,attempt=attempt,ordinal=len(records)))
 if src and not src.startswith('/'):hints[s].add(src)
def walk(d,p,ws=None):
 if isinstance(d,list):
  for v in d:walk(v,p,ws)
 elif isinstance(d,dict):
  context=json.dumps({k:v for k,v in d.items() if k in ['source','source_path','target','command','cmd','source_file','src','object','object_path','time_log','launcher_stdout']})
  here=ws
  if 'aspis-joint-20261019/sources/' in context or 'env J' in context or 'env-J' in context:here='joint'
  if 'codex-cx-import-union-20261022/sources/' in context:here='union'
  direct_sources=re.findall(r'/home/dombarker/project-offloads/([^/]+)/sources/[^ \"\\]+\.lean',context)
  if direct_sources and not any(v in ['aspis-joint-20261019','codex-cx-import-union-20261022'] for v in direct_sources):here=None
  m=d.get('module');s=d.get('source_sha256')
  a=d.get('attempt',d.get('label'))
  if isinstance(a,str):
   ma=re.search(r'(?:J|IU-)?([0-9]+)$',a)
   if ma:a=int(ma[1])
  if here and m and s:add(here,m,s,p,d.get('source_path',d.get('source')),3 if d.get('exit',d.get('exit_status')) == 0 else 2,a)
  if isinstance(a,str) and re.fullmatch('J?[0-9]+',a):a=int(a.lstrip('J'))
  if here and isinstance(a,int):attempts.add(a)
  path=d.get('path','')
  if isinstance(path,str):
   mt=re.search(r'(aspis-joint-20261019|codex-cx-import-union-20261022)/(?:objects|retained-objects|sources)/(.*)\.(?:olean|lean)$',path)
   if mt:census['joint' if mt[1].startswith('aspis') else 'union'].add(mt[2])
  for k,v in d.items():
   if isinstance(v,(dict,list)):walk(v,p,here)
for p in files:
 if not (p.endswith(('.json','.jsonl'))):continue
 try:
  raw=Path(p).read_text()
  if not any(x in raw for x in ['aspis-joint-20261019','codex-cx-import-union-20261022']) and not ('build-integration/manifest-' in p or 'import-union-20261022/rebuild-plan' in p):continue
  ds=[json.loads(l) for l in raw.splitlines() if l.strip()] if p.endswith('.jsonl') else [json.loads(raw)]
  for d in ds:
   walk(d,p)
   if isinstance(d,dict):
    ws='union' if 'import-union-20261022/rebuild-plan' in p else 'joint' if 'build-integration/manifest-' in p else None
    if ws:
     for r in d.get('order',d.get('ordered',[])):add(ws,r['module'],r['sha256'],p,r.get('source',r.get('path')),1)
 except (ValueError,UnicodeError,KeyError):pass
# SHA-index current committed source-like blobs, then historic objects only for unresolved hashes.
wanted={r['sha256'] for r in records}; resolved={}
entries=subprocess.check_output(['git','ls-tree','-r','HEAD'],text=True).splitlines()
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(oid):
 proc.stdin.write((oid+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();n=int(header[2]);b=proc.stdout.read(n);proc.stdout.read(1);return b
for line in entries:
 meta,p=line.split('\t',1);oid=meta.split()[2]
 if not (p.endswith(('.lean','.lean.txt','.lean.source')) or 'source' in p and p.endswith('.txt')):continue
 b=blob(oid);s=hashlib.sha256(b).hexdigest()
 if s in wanted and s not in resolved:resolved[s]=dict(blob=oid,revision=REV,path=p,bytes=len(b))
print('records',len(records),'hashes',len(wanted),'resolved HEAD',len(resolved),flush=True)
missing=wanted-resolved.keys()
if missing:
 history=subprocess.check_output(['git','rev-list','--objects','--all','--','*.lean','*.lean.txt','*source*.txt'],text=True).splitlines()
 for line in history:
  oid,_,p=line.partition(' ')
  if not p:continue
  try:b=blob(oid)
  except (ValueError,IndexError):continue
  s=hashlib.sha256(b).hexdigest()
  if s in missing:
   resolved[s]=dict(blob=oid,revision=None,path=p,bytes=len(b));missing.remove(s)
  if not missing:break
proc.terminate()
for s,r in resolved.items():
 if r['revision'] is None:
  rev=subprocess.check_output(['git','log','--all','--format=%H','--find-object='+r['blob'],'--',r['path']],text=True).splitlines()
  r['revision']=rev[0] if rev else 'unlocated revision (blob exists)'
by=collections.defaultdict(list)
for r in records:by[(r['workspace'],r['module'])].append(r)
selected=[]
for key,rs in sorted(by.items()):
 # Prefer newest receipt by commit evidence date (attempt ranges are not chronological across workers).
 def score(r):
  return (r['rank'],r['attempt'] if isinstance(r['attempt'],int) else -1,r['evidence'],r['ordinal'])
 r=max(rs,key=score).copy();r['resolution']=resolved.get(r['sha256']);r['variants']=sorted({x['sha256'] for x in rs});selected.append(r)
result=dict(revision=REV,records=records,resolved=resolved,missing_hashes=sorted(missing),selected=selected,census={k:sorted(v) for k,v in census.items()},highest_attempt=max(attempts,default=None),attempts=sorted(attempts))
(O/'EJR_inventory.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# EJR env-J inventory','',f'Source revision: `{REV}`. Committed structured evidence only.',f'Records: {len(records)}; distinct source hashes: {len(wanted)}; resolved: {len(resolved)}; unresolved: {len(missing)}.',f'Highest recorded numeric env-J attempt: {result["highest_attempt"]}. Stream B range 20000–27099 treated as used; 28000–29999 reserved; recovery uses 30000+.','', 'Historical variants are retained in EJR_inventory.json. Selection is provisional: highest numeric recorded receipt attempt, then manifest fallback. This does not prove final disk state or release coherence.','', '| Workspace | Module | SHA256 | Revision / blob |','|---|---|---|---|']
for r in selected:
 z=r['resolution'];lines.append(f'| {r["workspace"]} | {r["module"]} | {r["sha256"]} | '+(f'{z["revision"]} / {z["blob"]}' if z else 'NOT FOUND')+' |')
lines+=['','## Unresolved recorded hashes']+sorted(missing)
lines+=['','## Evidence limits','Objects-only census entries without a recorded source hash are listed separately in JSON; they cannot safely be assigned source bytes by name. No compile run, RSS/wall/swap/axioms: not applicable to inventory. No theorem premise removed; before/after top statement unchanged, ledger delta 0. Non-vacuity is not re-established by infrastructure inspection.']
(O/'EJR_INVENTORY.md').write_text('\n'.join(lines)+'\n')
print('selected',len(selected),'unresolved',len(missing),'highest',result['highest_attempt'],flush=True)
