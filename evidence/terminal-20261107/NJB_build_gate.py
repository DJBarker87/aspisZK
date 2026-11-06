from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger13-20261107';entries=[json.loads(l)for l in(E/'NJB_ATTEMPTS.jsonl').read_text().splitlines()];passed={}
for e in entries:
 if e.get('kind')!='lean'or e['exit_status']!=0:continue
 m=e['module'];p=E/(m+'.lean')
 if not p.exists()or not m.startswith('NJB_')or m in ['NJB_Driver','NJB_ProofDriver']:continue
 if e['source_hashes'].get(m+'.lean')!=hashlib.sha256(p.read_bytes()).hexdigest():continue
 passed[m]=e['attempt']
roots=[]
for m in sorted(passed):
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 if not ns:continue
 for name in re.findall(r'^theorem ([\w.]+)',s,re.M):roots.append(ns[1]+'.'+name)
roots=sorted(set(roots));assert 'AspisR1.NJB_SemanticPublic.result'in roots
modules=['NIU_COMBINED_IMPORT','NGK_COMBINED_IMPORT']+sorted(passed)
combined=''.join('import '+m+'\n'for m in modules)
combined+='\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for root in roots:combined+='#check '+root+'\n#print axioms '+root+'\n'
(E/'NJB_COMBINED_IMPORT.lean').write_text(combined)
# Preserve the predecessor baseline; extend only from source, never loader-derived import baselines.
expected={json.loads(l)['module']:json.loads(l)['imports']for l in(P/'NIU_EXPECTED_IMPORTS.jsonl').read_text().splitlines()}
sourcepins=[]
for p in [E/(m+'.lean')for m in passed]+[E/'NJB_COMBINED_IMPORT.lean']+list((E/'NJB_dependency_inputs').glob('*.lean')):
 xs=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)));m=p.stem
 if m in expected:assert expected[m]==xs,(m,expected[m],xs)
 expected[m]=xs;sourcepins.append(dict(path=str(p),module=m,imports=xs,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'NJB_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=xs))+'\n'for m,xs in sorted(expected.items())))
(E/'NJB_GATE_SOURCES.json').write_text(json.dumps(dict(baseline=str(P/'NIU_EXPECTED_IMPORTS.jsonl'),baseline_sha256=hashlib.sha256((P/'NIU_EXPECTED_IMPORTS.jsonl').read_bytes()).hexdigest(),source_extensions=sourcepins,passed=passed),indent=1))
# Two independent raw walks, all in the same combined forest containing the headline.
roots.append('AspisR1.RPx_Deployed.deployed');groups=[roots[i*len(roots)//2:(i+1)*len(roots)//2]for i in range(2)]
(E/'NJB_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1));(E/'NJB_AUDIT_MODULES.json').write_text(json.dumps([['NJB_COMBINED_IMPORT']]*2))
print(json.dumps(dict(modules=len(passed),roots=len(roots),raw_groups=2)))
