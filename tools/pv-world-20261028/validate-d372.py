"""Read-only accounting of the fresh D372 budget and accepted proof frontier."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028';D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
allowed={'propext','Classical.choice','Quot.sound'};rows=[]
for p in sorted(E.glob('lean-504*/receipt.json')):
 j=json.loads(p.read_text());out=(p.parent/'output.log').read_text();queries=[]
 for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",out,re.S):
  axs=[x.strip() for x in (m[3] or '').split(',') if x.strip()]
  queries.append(dict(theorem=m[1],axioms=axs,accepted=set(axs)<=allowed))
 b=subprocess.check_output(['git','cat-file','blob',j['source_blob']],cwd=R)
 source_ok=hashlib.sha256(b).hexdigest()==j['source_sha256']
 rows.append(dict(id=j['id'],module=j['module'],exit=j['exit'],accepted=j['exit']==0 and source_ok and all(q['accepted'] for q in queries) and 'sorryAx' not in out,source_ok=source_ok,source_sha256=j['source_sha256'],source_revision=j['source_revision'],source_blob=j['source_blob'],deps_fingerprint=j['deps_fingerprint'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],queries=queries))
assert [r['id'] for r in rows]==list(range(50400,50500)),[r['id'] for r in rows]
assert all(r['source_ok'] and str(r['swap'])=='0' for r in rows)
changed=subprocess.check_output(['git','diff','--name-only','95740e6864','--','docs/research/v8-r0-zk-20261009/lean/R1Z'],cwd=R,text=True).splitlines();sources=[]
for path in changed:
 p=R/path
 if not p.exists() or not p.stem.startswith('PV_W_'):continue
 b=p.read_bytes();h=hashlib.sha256(b).hexdigest();s=b.decode();ns=re.search(r'^namespace (\S+)',s,re.M)
 names=[ns[1]+'.'+n for n in re.findall(r'^theorem\s+(\w+)',s,re.M)] if ns else []
 matches=[r for r in rows if r['module']=='R1Z/'+p.stem and r['source_sha256']==h and r['accepted']]
 printed={q['theorem'] for r in matches for q in r['queries']}
 sources.append(dict(module='R1Z.'+p.stem,path=path,sha256=h,blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),accepted_attempts=[r['id'] for r in matches],missing_axiom_queries=[n for n in names if n not in printed],checked=bool(matches) and all(n in printed for n in names),diagnostic=p.stem=='PV_W_LoopInspect'))
result=dict(start_revision='95740e686418809a3ceade00cf558cd5a42cc180',target_established=False,rows_newly_closed=[],endpoint_premises_removed=0,endpoint_premises_added=0,endpoint_premises_weakened=0,compiler_attempts=len(rows),remaining=100-len(rows),accepted_attempts=sum(r['accepted'] for r in rows),failed_attempts=sum(not r['accepted'] for r in rows),kani_attempts=0,ids=[50400,50499],attempts=rows,sources=sources,unverified_sources=[x['module'] for x in sources if not x['checked']],audit_queries={str(r['id']):len(r['queries']) for r in rows if r['id']>=50497},scope='focused current source/axioms replay; no native whole-prover, Observation, deployment or frozen-manifest closure')
(E/'d372-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['attempts','sources']}))
assert not result['unverified_sources']
