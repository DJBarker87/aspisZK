from pathlib import Path
import json,re,difflib,hashlib,subprocess
E=Path(__file__).resolve().parent;K=E.parent/'pool-retarget-20261105'
roots=['AspisR1.RPx_Deployed.deployed']
for p in E.glob('NHC_L*/stdout.log'):
 if json.loads((p.parent/'receipt.json').read_text())['exit_status']:continue
 for line in p.read_text().splitlines():
  m=re.match(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",line)
  if m and (m[1].startswith('NHC_') or '.NHC_' in m[1]):roots.append(m[1])
roots=sorted(set(roots));(E/'NHC_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i:i+200] for i in range(0,len(roots),200)]),indent=1)+'\n')
for n in ['ProofDriver','Driver']:
 before=(K/('NGK_'+n+'.lean')).read_text();after=before.replace('NGK_AUDIT_ROOTS','NHC_AUDIT_ROOTS').replace('NGK_COMBINED_IMPORT','NHC_COMBINED_IMPORT').replace('NGK_EXPECTED_IMPORTS','NHC_EXPECTED_IMPORTS').replace('NGK_LOADED_scan','NHC_LOADED_scan')
 (E/('NHC_'+n+'.lean')).write_text(after);(E/('NHC_'+n+'.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='NGK_'+n,tofile='NHC_'+n)))
(E/'NHC_batch.py').write_text((K/'NGK_batch.py').read_text().replace('NGK_','NHC_'))
# Independent source baselines from the canonical predecessor, augmented by actual new sources.
p=K/'NGK_EXPECTED_IMPORTS.jsonl'
if not p.exists():
 raw=subprocess.check_output(['git','show','HEAD:'+str(p)]).decode()
else:raw=p.read_text()
baselines={r['module']:r for r in map(json.loads,raw.splitlines())}
for p in (p for p in E.rglob('*.lean') if 'sources' not in p.relative_to(E).parts):
 n=str(p.relative_to(E)).removesuffix('.lean').replace('/','.')
 baselines[n]=dict(module=n,imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M))))
(E/'NHC_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for n,r in sorted(baselines.items())))
print('roots',len(roots))
