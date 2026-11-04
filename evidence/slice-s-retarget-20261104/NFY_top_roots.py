"""Collect every copied named public theorem from successful exact-source logs."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;p=json.loads((E/'NFY_PROVENANCE.json').read_text());by={}
for f in sorted(E.glob('NFY_L*/receipt.json')):
 r=json.loads(f.read_text())
 if r.get('kind')=='lean' and r['exit_status']==0:by[r['module']]=(f,r)
roots={};missing=[]
for i,ns in enumerate(p['groups']):
 m=f'NFY_Part{i:03}'
 if m not in by:missing.append(m);continue
 f,r=by[m];snapshot=f.parent/'sources/NFY_generated'/(m+'.lean');assert snapshot.read_bytes()==(E/(m+'.lean')).read_bytes(),('stale receipt',m)
 bodies=[x['after_body'] for x in p['files'] if x['source_module'] in ns]
 suffixes={n for t in bodies for n in re.findall(r'^(?:protected )?(?:theorem|lemma)\s+([^\s{:(]+)',t,re.M)}
 names=set(re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text(),re.M))
 chosen=sorted(n for n in names if not n.startswith('_private.') and (n.rsplit('.',1)[-1] in suffixes or n in suffixes))
 roots[m]=chosen
assert not missing,missing
(E/'NFY_TOP_ROOTS.json').write_text(json.dumps(dict(modules=roots,roots=sorted({n for ns in roots.values() for n in ns})),indent=1)+'\n')
print(sum(map(len,roots.values())))
