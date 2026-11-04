import json, subprocess, datetime, hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
refs={'research':'d6b809c9e8a','rw':'refs/remotes/origin/codex/cx-prover-rw-20261023', **{k:'codex/pv-'+k+'-'+d for k,d in [('b3p6','20261028'),('evhB','20261103'),('stx','20261104'),('stxb','20261104'),('evh','20261029'),('runjoin','20261026'),('uc','20261029'),('evhc','20261029'),('k3scan','20261101')]}}
pins={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worktree':str(Path.cwd()),'branch':'codex/pv-recount12-20261104','base':'d6b809c9e8a','refs':refs,'revisions':{k:subprocess.check_output(['git','rev-parse',v]).decode().strip() for k,v in refs.items()},'policy':'Candidate current head and live branch heads captured once; all subsequent reads immutable. Uncommitted work excluded.'}
if (P/'pins.json').exists():
 pins=json.loads((P/'pins.json').read_text())
else:(P/'pins.json').write_text(json.dumps(pins,indent=1)+'\n')
from audit12 import *
old=json.loads((B/'recount11/definition-audit11.json').read_text());rows=json.loads((B/'recount11/rows11.json').read_text());out=[]
for r,d in zip(rows,old):
 paths=sorted({s['path'] for s in d['sources']}|{r.get('definition','').split('#')[0]});w=[]
 for k in revs:
  for p in paths:
   if p and read(k,p) is not None:
    z=dict(manifest[k+':'+p]);z['prior_identical']=any(s['sha256']==z['sha256'] and s['path']==p for s in d['sources']);w.append(z)
 out.append({'id':r['id'],'sources':w,'changed':[z for z in w if not z['prior_identical']]})
(P/'definition-audit12.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
# Exact task evidence inputs; retained compressed, immutable Git objects are the ultimate authority.
for k in revs:
 for p in tree(k):
  take=False
  if k in ['stx','stxb','evhB']:
   prefix='evidence/pv-'+{'stx':'stx-20261104','stxb':'stxb-20261104','evhB':'evhB-20261103'}[k]+'/'
   take=p.startswith(prefix) and not '/std/' in p and not '/context-std/' in p
   take |= p.startswith('tools/pv-'+k+'-') and p.endswith(('.rs','.toml','.py','.lean'))
  if k=='b3p6':take=p.startswith('evidence/pv-b3p6-20261028/') and any(t in p for t in ['D603','D610','D617','D623','D628','D630','D636','resume27','resume28','resume29','resume30','resume31','resume32','resume33','resume34','resume35','resume36','resume37','resume38','resume39','resume40','resume41','resume42','resume43','resume44','resume45','resume46','resume47','resume48','resume49','resume50','resume51','resume52'])
  if k=='k3scan':take=p.startswith(('evidence/pv-k3scan3-20261104/','evidence/pv-k3scan-20261101/')) and not any(t in p for t in ['reachable','REACHABLE','metadata','symbol','inventory'])
  if take and p.endswith(('.rs','.md','.json','.jsonl','.txt','.log','.xz','.sha256','.lean','.py','.toml')):read(k,p)
 for p in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PV-OWNER-PACKET-20261027.md','tools/r1-cost-probe/src/bin/user_client/diagnostics.rs']:
  read(k,p)
save();print('snapshots',len(manifest),'changed',[(a['id'],len(a['changed'])) for a in out if a['changed']])
