from pathlib import Path
import json,hashlib,subprocess,collections,re
C=Path('/private/tmp/pv-kscan-cache-20261028');E=Path(__file__).resolve().parent;db=json.loads((C/'d347-source-db.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());wanted=collections.defaultdict(set)
for p in ps:
 r=rs[p['receipt_blob']]
 if not isinstance(r,dict):continue
 for f,v in r.get('inputs',{}).items():
  h=v.get('sha256')
  if h in db or not f.endswith(('.rs','Cargo.toml')):continue
  if '/source/' in f:rel=f.split('/source/',1)[1]
  else:
   a=re.search(r'/codex-(pv-[^/]+)/(.+)',f)
   if not a:continue
   rel='tools/'+a[1]+'/'+a[2]
  wanted[rel].add(h)
for rel,hs in wanted.items():
 revs=subprocess.check_output(['git','log','--all','--format=%H','--',rel],text=True).splitlines()
 for rev in revs:
  p=subprocess.run(['git','show',rev+':'+rel],capture_output=True)
  if p.returncode:continue
  h=hashlib.sha256(p.stdout).hexdigest();db.setdefault(h,dict(text=p.stdout.decode(),origin=rev+':'+rel,kind='committed historical source'))
 print(rel,'versions',len(revs),'exact recovered',len(hs.intersection(db)))
(C/'d347-source-db.json').write_text(json.dumps(db))
