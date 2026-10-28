"""Read-only proof/evidence accounting; never invokes Lean or a build."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
allowed={'propext','Classical.choice','Quot.sound'};rows=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text());out=(p.parent/'output.log').read_text()
 queries=[]
 for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",out,re.S):
  axioms=[s.strip() for s in (m[3] or '').split(',') if s.strip()]
  queries.append(dict(theorem=m[1],axioms=axioms,accepted=set(axioms)<=allowed))
 source_ok=None
 if j.get('source_blob'):
  b=subprocess.check_output(['git','cat-file','blob',j['source_blob']],cwd=R)
  source_ok=hashlib.sha256(b).hexdigest()==j['source_sha256']
 ok=j['exit']==0 and all(x['accepted'] for x in queries) and 'sorryAx' not in out and source_ok is not False
 rows.append(dict(id=j.get('id',int(p.parent.name[5:])),module=j.get('module'),exit=j['exit'],accepted=ok,source_ok=source_ok,source_sha256=j.get('source_sha256'),wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],queries=queries))
 assert 36000<=rows[-1]['id']<=36199
assert len(rows)<=100
sources=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_W_*.lean')):
 m='R1Z/'+p.stem;h=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r for r in rows if r['module']==m and r['source_sha256']==h and r['accepted']]
 names=re.findall(r'^theorem\s+(\w+)',p.read_text(),re.M)
 ns=re.search(r'^namespace\s+(\S+)',p.read_text(),re.M);namespace=ns[1] if ns else m.replace('/','.')
 printed=set(q['theorem'] for r in matches for q in r['queries'])
 missing=[namespace+'.'+n for n in names if namespace+'.'+n not in printed]
 sources.append(dict(module=m,path=str(p.relative_to(R)),sha256=h,accepted_attempts=[r['id'] for r in matches],missing_axiom_queries=missing,checked=bool(matches) and not missing))
# The unchanged original audit's source has no theorem of its own and its
# original accepted audit is retained; it need not have a restored object.
result=dict(target_established=False,rows_closed=[],endpoint_premises_removed=0,compiler_attempts=len(rows),remaining=100-len(rows),kani_attempts=0,attempts=rows,sources=sources,unverified_sources=[s['module'] for s in sources if not s['checked']],scope='focused proof frontier; no native/deployment or complete frozen manifest claim')
(E/'resume-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['attempts','sources']}))
