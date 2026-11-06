from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;L=E.parent/'terminal2-20261108';O=E.parent/'ledger15-20261108'
entries=[json.loads(l)for l in(E/'NJX_ATTEMPTS.jsonl').read_text().splitlines()];passed={}
for x in entries:
 m=x.get('module','');p=E/(m+'.lean')
 if x.get('kind')!='lean' or x['exit_status']!=0 or not m.startswith('NJX_') or not p.is_file():continue
 if m in ['NJX_Driver','NJX_ProofDriver','NJX_COMBINED_IMPORT']:continue
 if x['source_hashes'].get(m+'.lean')!=hashlib.sha256(p.read_bytes()).hexdigest():continue
 passed[m]=x['attempt']
roots=[]
for m in sorted(passed):
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if ns:
  roots += [ns[1]+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
required=[r for row in json.loads((E/'NJX_CLOSED.json').read_text())['functions']for r in row['lean_roots']];assert set(required)<=set(roots)
modules=['NJO_COMBINED_IMPORT','NJL_COMBINED_IMPORT']+sorted(passed)
s=''.join('import '+m+'\n'for m in modules)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for r in sorted(set(roots)):s+='#check '+r+'\n#print axioms '+r+'\n'
(E/'NJX_COMBINED_IMPORT.lean').write_text(s)
expected={};baselines=[]
for p in [O/'NJO_EXPECTED_IMPORTS.jsonl',L/'NJL_EXPECTED_IMPORTS.jsonl']:
 baselines.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 for row in map(json.loads,p.read_text().splitlines()):
  assert row['module'] not in expected or expected[row['module']]==row['imports'],row['module']
  expected[row['module']]=row['imports']
sourcepins=[]
for p in [E/(m+'.lean')for m in passed]+[E/'NJX_COMBINED_IMPORT.lean']:
 imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)));expected[p.stem]=imports
 sourcepins.append(dict(module=p.stem,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=imports))
(E/'NJX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n'for m,im in sorted(expected.items())))
(E/'NJX_GATE_SOURCES.json').write_text(json.dumps(dict(baselines=baselines,source_extensions=sourcepins,passed=passed),indent=1))
allroots=sorted(set(roots+json.loads((O/'NJO_AUDIT_ROOTS.json').read_text())['roots']+json.loads((L/'NJL_AUDIT_ROOTS.json').read_text())['roots']))
# First NJO+NJL import changes the selected cohort; full raw closure audit is
# required even for compatible theorem-cache replicas whose proof bodies differ.
groups=[allroots[i*len(allroots)//42:(i+1)*len(allroots)//42]for i in range(42)]
assert sum(map(len,groups))==len(allroots) and len(set(sum(groups,[])))==len(allroots)
(E/'NJX_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots,groups=groups,new_roots=sorted(set(roots)),reason='First combined NJO+NJL selected cohort: audit proof bodies as well as compatible theorem-cache declarations. Distinct groups, no unchanged full regression rerun.'),indent=1))
(E/'NJX_AUDIT_MODULES.json').write_text(json.dumps([['NJX_COMBINED_IMPORT']]*len(groups)))
for n in ['NJL_Driver.lean','NJL_ProofDriver.lean','NJL_gate_setup.py','NJL_link.py','NJL_batch.py']:
 old=(L/n).read_text();new=old.replace('NJL_','NJX_');(E/n.replace('NJL_','NJX_')).write_text(new)
(E/'NJX_AUDIT_ADAPTATIONS.json').write_text(json.dumps([dict(source=str(L/n),sha256=hashlib.sha256((L/n).read_bytes()).hexdigest(),target=n.replace('NJL_','NJX_'),change='NJL_ -> NJX_ paths/selectors only; unchanged hardened walker, canonical import/owner scan, memory limiter, fixture checks and verdicts')for n in ['NJL_Driver.lean','NJL_ProofDriver.lean','NJL_gate_setup.py','NJL_link.py','NJL_batch.py']],indent=1))
print(json.dumps(dict(passed_modules=len(passed),new_roots=len(set(roots)),total_raw_roots=len(allroots),raw_groups=len(groups),import_baseline_conflicts=0)))
