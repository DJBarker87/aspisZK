"""Own audit manifests; unchanged NEP walker and eight fixture identities."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;Q=E.parent/'slice-d-pair6-20261107'
semantic=[]
for p in sorted(E.glob('NIW_*.lean')):
 if p.stem in ['NIW_APIs','NIW_ByteAPIs','NIW_Inspect','NIW_IndexInspect','NIW_Driver','NIW_ProofDriver','NIW_COMBINED_IMPORT']:continue
 semantic.append(p)
roots=['AspisR1.RPx_Deployed.deployed']
for p in semantic:
 namespaces=re.findall(r'^namespace (\S+)',p.read_text(),re.M)
 assert len(namespaces)==1,p
 roots += [namespaces[0]+'.'+name for name in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)]
assert len(roots)==len(set(roots))
(E/'NIW_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
rows={x['module']:x for x in map(json.loads,(Q/'NIT_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in semantic+[E/'NIW_COMBINED_IMPORT.lean']:
 imports=['Init']+[x for line in p.read_text().splitlines()if line.startswith('import ')for x in line[7:].split()]
 rows[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(imports)))
(E/'NIW_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n'for n in sorted(rows)))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(E/'NIW_AUDIT_PROVENANCE.json').write_text(json.dumps(dict(base_catalog=str(Q/'NIT_EXPECTED_IMPORTS.jsonl'),base_sha256=sha(Q/'NIT_EXPECTED_IMPORTS.jsonl'),semantic_modules=[dict(path=str(p.relative_to(E)),sha256=sha(p))for p in semantic],roots=len(roots),walker=sha(E/'NIW_NFA_WALKER.c.txt'),walker_unchanged=sha(E/'NIW_NFA_WALKER.c.txt')==sha(Q/'NIT_NFA_WALKER.c.txt'),driver_changes='NIT_ to NIW_ path/module strings only; no walker, fixture or verification changes'),indent=2)+'\n')
print(json.dumps(dict(roots=len(roots),modules=len(semantic))))
