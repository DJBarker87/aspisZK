from pathlib import Path
import subprocess,json,hashlib,os,re,datetime
P=Path(__file__).resolve().parent; B=P.parent
old=json.loads((B/'recount8/pins.json').read_text()); branches=old['branches'].copy(); branches.update(research='6474027f52',rw='42760700cb',runjoin='codex/pv-runjoin-20261026',b3p6='codex/pv-b3p6-20261028',rdcd4='codex/pv-rdcd4-20261029',l2e='codex/pv-l2e-20261029',evhd='codex/pv-evhd-20261029')
active=['research','rw','runjoin','b3p6','rdcd4','l2e','evhd']; revs=old['revisions'].copy()
if (P/'pins.json').exists():
 pins=json.loads((P/'pins.json').read_text());revs=pins['revisions']
else:
 raise SystemExit('Pinned capture metadata is required; never resolve moving refs during recovery.')
prior={}
for d in sorted(B.glob('recount[1-8]')):
 if (d/'manifest.json').exists():
  for x in json.loads((d/'manifest.json').read_text()):
   if 'snapshot' not in x or 'blob' not in x: continue
   f=d/x['snapshot']
   if f.exists(): prior[x['blob']]=f.resolve()
for f in (P/'objects').glob('*.txt'):prior[f.stem]=f.resolve()
manifest=[]; cache={}
def read(k,path):
 if (k,path) in cache:return cache[k,path]
 q=subprocess.run(['git','show',revs[k]+':'+path],capture_output=True)
 if q.returncode:cache[k,path]=None;return None
 raw=q.stdout
 blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=prior.get(blob,P/'objects'/(blob+'.txt'))
 if not f.exists():f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 manifest.append(dict(ref=k,revision=revs[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P)));cache[k,path]=raw.decode(errors='replace');return cache[k,path]
rows=json.loads((B/'recount8/rows8.json').read_text()); da8={x['id']:x for x in json.loads((B/'recount8/definition-audit8.json').read_text())};audit=[]
for r in rows:
 path,_,decl=r.get('definition','').partition('#');ss=[];missing=[]
 for k in sorted(set(active+[x['ref'] for x in da8[r['id']]['sources']])):
  s=read(k,path) if path else None
  if s is None:missing.append(k)
  else:ss.append({**next(x for x in reversed(manifest) if x['ref']==k and x['path']==path),'declaration':decl})
 audit.append(dict(id=r['id'],definition=r.get('definition'),sources=ss,missing=missing,changed_from8=[x['ref'] for x in ss if x['sha256'] not in {y['sha256'] for y in da8[r['id']]['sources']}]))
# Discover with git grep only; inspect complete changed statements and explicit evidence packets.
for k in active:
 print('capture ref',k,flush=True)
 scopes={'research':[], 'rw':['evidence/pv-*'], 'runjoin':['evidence/pv-runjoin54*','evidence/pv-runjoin55*'], 'b3p6':['evidence/pv-b3p6-20261028/resume12','evidence/pv-b3p6-20261028/resume13'], 'rdcd4':['evidence/pv-rdcd4*'], 'l2e':['evidence/pv-l2e*'],'evhd':['evidence/pv-evhd*']}[k]
 paths=subprocess.run(['git','grep','-I','-l','.',revs[k],'--']+scopes,capture_output=True,text=True).stdout.splitlines() if scopes else []
 for line in paths:
  path=line.split(':',1)[1]
  worker=bool(re.search(r'evidence/pv-(own|rdb2[fgh]|fix|diag|fib|top|l1[efg]|l2e|evhd|rdcd[34]|b3p6|runjoin5|rj4id)',path))
  selected=worker and path.endswith('.md')
  topjson=worker and path.endswith('.json') and not re.search(r'/(lean-|receipts/|raw/|admission|barrier|env-|source-bytes|source-pins|closure-fingerprint|external-|final-object|static-capture)',path) and path.count('/')<=3
  if selected or topjson:read(k,path)
 for path in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PV-OWNER-PACKET-20261027.md','design/PRIVACY-LEDGER-20261026.md']:read(k,path)
(P/'definition-audit9.json').write_text(json.dumps(audit,indent=1)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n')
print(json.dumps(pins,indent=2));print('Witnesses',len(manifest),'changed definitions',sum(bool(x['changed_from8']) for x in audit),'new bytes',sum(f.stat().st_size for f in (P/'objects').glob('*')))
