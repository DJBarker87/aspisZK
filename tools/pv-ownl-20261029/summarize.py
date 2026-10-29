from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownl-20261029';rows=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text());assert 65600<=j['attempt']<=65699
 for f in ['admission-before.json','admission-launch.json','admission-barrier.json']:assert json.loads((p.parent/f).read_text())['allowed'] is True
 if j['exit']==0:assert 'sorryAx' not in j['print_axioms'],j['attempt']
 rows.append(dict(attempt=j['attempt'],module=j['module'],exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],axioms_reports=re.findall(r"'[^']+' depends on axioms: \[[^\]]*\]|'[^']+' does not depend on any axioms",j['print_axioms'],re.S)))
assert len(rows)==100 and len({r['attempt']for r in rows})==100
j=dict(lean_attempts=len(rows),successes=sum(r['exit']==0 for r in rows),failures=[r['attempt']for r in rows if r['exit']!=0],peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),all_swaps_zero=all(r['swap']=='0'for r in rows),native_scopes=1,kani=0,rows=rows)
(E/'validation-summary.json').write_text(json.dumps(j,indent=2)+'\n');print({k:v for k,v in j.items()if k!='rows'})
