from NMD_formal import *
from NMD_audit import audit
p=E/'NMD_COMBINED_IMPORT.lean';s=p.read_text();assert 'import NMD_ComputedFold' not in s
s=s.replace('import NMD_CandidateFold\n','import NMD_CandidateFold\nimport NMD_ComputedFold\n');p.write_text(s)
modules=['NMD_CutState','NMD_SegmentFold','NMD_CandidateFold','NMD_ComputedFold'];roots=[]
for m in modules:
 source=(E/(m+'.lean')).read_text();roots += [m+'.'+t for t in re.findall(r'^theorem (\w+)',source,re.M)]
roots+=['AspisR1.RPx_Deployed.deployed']
(E/'NMD_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i:i+8] for i in range(0,len(roots),8)]),indent=1)+'\n')
expected={r['module']:r['imports'] for r in [json.loads(l) for l in (E/'NMD_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]}
for m in modules+['NMD_COMBINED_IMPORT']:
 expected[m]=['Init']+re.findall(r'^import ([\w.]+)',(E/(m+'.lean')).read_text(),re.M)
(E/'NMD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n' for m,im in sorted(expected.items())))
(E/'NMD_MODULES.json').write_text(json.dumps(modules,indent=1)+'\n')
r=run('NMD_L013','lean','NMD_COMBINED_IMPORT');assert r['exit_status']==0
for a,target in [('NMD_L014','scan'),('NMD_L015','batch0'),('NMD_L016','batch1')]:
 r=audit(a,'audit',target);assert r['exit_status']==0,(a,'Inspect raw ax2 and retain disagreement if standard-only')
