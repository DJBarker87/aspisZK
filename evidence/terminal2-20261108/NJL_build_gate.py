from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'terminal-20261107';N=E.parent/'verify-observed5-20261107'
entries=[json.loads(l)for l in(E/'NJL_ATTEMPTS.jsonl').read_text().splitlines()];passed={}
exclude={'NJL_CopyCarrier','NJL_Driver','NJL_ProofDriver','NJL_COMBINED_IMPORT'}
for x in entries:
 if x.get('kind')!='lean'or x['exit_status']!=0:continue
 m=x['module'];p=E/(m+'.lean')
 if m in exclude or not p.exists():continue
 if x['source_hashes'].get(m+'.lean')!=hashlib.sha256(p.read_bytes()).hexdigest():continue
 passed[m]=x['attempt']
roots=[]
for m in sorted(passed):
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if ns:
  for name in re.findall(r'^theorem ([\w.]+)',s,re.M):roots.append(ns[1]+'.'+name)
roots=sorted(set(roots));required=[root for row in json.loads((E/'NJL_CLOSED.json').read_text())['functions']for root in row['lean_roots']];assert set(required)<=set(roots)
modules=['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NJB_COMBINED_IMPORT','NIX_ResidualCut','NIX_ResidualLog']+sorted(passed)
s=''.join('import '+m+'\n'for m in modules)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for r in roots:s+='#check '+r+'\n#print axioms '+r+'\n'
for r in ['AspisR1.NIX_ResidualCut.packet','AspisR1.NIX_ResidualLog.packet','AspisR1.NJB_SemanticPublic.result']:s+='#check '+r+'\n#print axioms '+r+'\n'
(E/'NJL_COMBINED_IMPORT.lean').write_text(s)
# Source-pinned import expectations, never a baseline harvested from loaded modules.
expected={};origins={};conflicts=[]
for p in [P/'NJB_EXPECTED_IMPORTS.jsonl',N/'NIX_EXPECTED_IMPORTS.jsonl']:
 for line in p.read_text().splitlines():
  x=json.loads(line);m=x['module'];imp=x['imports']
  if m in expected and expected[m]!=imp:
   assert not m.startswith('NIX_'),m
   conflicts.append(dict(module=m,canonical_source=origins[m],canonical_imports=expected[m],unselected_historical_source=str(p),historical_imports=imp))
   continue
  expected[m]=imp;origins[m]=str(p)
(E/'NJL_BASELINE_VARIANTS.json').write_text(json.dumps(dict(policy='Retain the predecessor NJB/NIU coherent source baseline for existing module names; add NIX new names only. The scan still checks every loaded module against this source-pinned selection; no loader-derived override.',variants=conflicts),indent=2)+'\n')
sourcepins=[]
for p in [E/(m+'.lean')for m in passed]+[E/'NJL_COMBINED_IMPORT.lean']:
 xs=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)));m=p.stem
 assert m not in expected or expected[m]==xs
 expected[m]=xs;sourcepins.append(dict(path=str(p),module=m,imports=xs,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'NJL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=xs))+'\n'for m,xs in sorted(expected.items())))
(E/'NJL_GATE_SOURCES.json').write_text(json.dumps(dict(baselines=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in[P/'NJB_EXPECTED_IMPORTS.jsonl',N/'NIX_EXPECTED_IMPORTS.jsonl']],source_extensions=sourcepins,passed=passed),indent=1))
roots+=['AspisR1.NIX_ResidualCut.packet','AspisR1.NIX_ResidualLog.packet','AspisR1.NJB_SemanticPublic.result','AspisR1.RPx_Deployed.deployed'];groups=[roots[i*len(roots)//2:(i+1)*len(roots)//2]for i in range(2)]
(E/'NJL_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1));(E/'NJL_AUDIT_MODULES.json').write_text(json.dumps([['NJL_COMBINED_IMPORT']]*2));(E/'NJL_NIX_EXPORT.json').write_text((N/'NIX_EXPORT.json').read_text())
# Approved audit-driver adaptation: only job paths/selectors, method stays byte-identical.
for n in ['NJB_Driver.lean','NJB_ProofDriver.lean','NJB_gate_setup.py','NJB_link.py']:
 old=(P/n).read_text();new=old.replace('NJB_','NJL_');(E/n.replace('NJB_','NJL_')).write_text(new)
(E/'NJL_AUDIT_ADAPTATIONS.json').write_text(json.dumps([dict(source=str(P/n),sha256=hashlib.sha256((P/n).read_bytes()).hexdigest(),target=n.replace('NJB_','NJL_'),change='NJB_ -> NJL_ only; unchanged hardened walker, import/declaration scan and memory limiter')for n in['NJB_Driver.lean','NJB_ProofDriver.lean','NJB_gate_setup.py','NJB_link.py']],indent=1))
print(json.dumps(dict(passed_modules=len(passed),roots=len(roots),raw_groups=2)))
