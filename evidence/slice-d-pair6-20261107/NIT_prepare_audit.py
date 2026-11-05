"""Own audit manifests; unchanged NEP walker and eight fixture identities."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;Q=E.parent/'slice-d-pair5-20261107'
semantic=[]
for p in sorted(E.glob('NIT_*.lean')):
 if p.stem in ['NIT_APIs','NIT_ByteAPIs','NIT_Inspect','NIT_IndexInspect','NIT_Driver','NIT_ProofDriver','NIT_COMBINED_IMPORT']:continue
 semantic.append(p)
roots=['AspisR1.RPx_Deployed.deployed']
for p in semantic:
 namespaces=re.findall(r'^namespace (\S+)',p.read_text(),re.M)
 assert len(namespaces)==1,p
 roots += [namespaces[0]+'.'+name for name in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)]
assert len(roots)==len(set(roots))
(E/'NIT_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
rows={x['module']:x for x in map(json.loads,(Q/'NIQ_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in semantic+[E/'NIT_COMBINED_IMPORT.lean']:
 imports=['Init']+[x for line in p.read_text().splitlines()if line.startswith('import ')for x in line[7:].split()]
 rows[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(imports)))
(E/'NIT_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n'for n in sorted(rows)))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(E/'NIT_AUDIT_PROVENANCE.json').write_text(json.dumps(dict(base_catalog=str(Q/'NIQ_EXPECTED_IMPORTS.jsonl'),base_sha256=sha(Q/'NIQ_EXPECTED_IMPORTS.jsonl'),semantic_modules=[dict(path=str(p.relative_to(E)),sha256=sha(p))for p in semantic],roots=len(roots),walker=sha(E/'NIT_NFA_WALKER.c.txt'),walker_unchanged=sha(E/'NIT_NFA_WALKER.c.txt')==sha(Q/'NIQ_NFA_WALKER.c.txt'),driver_changes='NIQ_ to NIT_ path/module strings only; no walker, fixture or verification changes'),indent=2)+'\n')
print(json.dumps(dict(roots=len(roots),modules=len(semantic))))
