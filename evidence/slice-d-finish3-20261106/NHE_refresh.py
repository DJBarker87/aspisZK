from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-finish2-20261105'
roots=[]
for p in sorted(E.glob('NHE_*.lean')):
 if p.stem in ['NHE_Driver','NHE_ProofDriver','NHE_COMBINED_IMPORT']:continue
 roots += [p.stem+'.'+r for r in re.findall(r'^#print axioms (\w+)$',p.read_text(),re.M)]
(E/'NHE_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
cat={r['module']:r for l in (P/'NGW_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for r in [json.loads(l)]}
for p in E.glob('NHE_*.lean'):
 imports=['Init']+[w for l in p.read_text().splitlines()if l.startswith('import ')for w in l[7:].split()if w!='all']
 cat[p.stem]=dict(module=p.stem,imports=list(dict.fromkeys(imports)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_path=str(p))
(E/'NHE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(cat[n])+'\n'for n in sorted(cat)))
print('roots',len(roots),'baselines',len(cat))
