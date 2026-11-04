"""Adapt only selectors/runtime filenames in the accepted NGJ audit drivers."""
from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger8-20261105'
x=json.loads((E/'NGK_PROVENANCE.json').read_text());rename=x['namespace_map']
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
roots=json.loads((P/'NGJ_AUDIT_ROOTS.json').read_text())['roots']
pool=json.loads((E.parent/'pool-retdata3-20261104/NFV_AUDIT.json').read_text())['roots']
roots=sorted(set(roots+[pat.sub(lambda m:rename[m.group()],r['root']) for r in pool]))
# Add every top theorem printed by all successful retarget attempts, not only
# roots from the predecessor aggregate.
for p in sorted(E.glob('NGK_L*/stdout.log')):
 if json.loads((p.parent/'receipt.json').read_text())['exit_status'] != 0:continue
 for line in p.read_text().splitlines():
  m=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if m and m[1].startswith('NGK_'):roots.append(m[1])
roots=sorted(set(roots))
(E/'NGK_AUDIT_ROOTS.json').write_text(json.dumps(dict(headline='AspisR1.RPx_Deployed.deployed',roots=roots,groups=[roots[i:i+240] for i in range(0,len(roots),240)]),indent=1)+'\n')
for n in ['ProofDriver','Driver']:
 before=(P/('NGJ_'+n+'.lean')).read_text();after=before.replace('NGJ_AUDIT_ROOTS','NGK_AUDIT_ROOTS').replace('NGJ_VERIFIER_IMPORT','NGK_COMBINED_IMPORT').replace('NGJ_EXPECTED_IMPORTS','NGK_EXPECTED_IMPORTS').replace('NGJ_LOADED_scan','NGK_LOADED_scan')
 (E/('NGK_'+n+'.lean')).write_text(after)
 (E/('NGK_'+n+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='NGJ_'+n,tofile='NGK_'+n)))
s=(P/'NGJ_batch.py').read_text().replace('NGJ_','NGK_');(E/'NGK_batch.py').write_text(s)
baselines={r['module']:r for r in map(json.loads,(P/'NGJ_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
# Independently committed source import lists for new modules. Existing imported
# module baselines remain from the accepted predecessor, never candidate scan.
for p in E.glob('NGK_*.lean'):
 imports=re.findall(r'^import ([\w.]+)',p.read_text(),re.M)
 baselines[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(['Init']+imports)))
(E/'NGK_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for n,r in sorted(baselines.items())))
print(len(roots),'roots')
