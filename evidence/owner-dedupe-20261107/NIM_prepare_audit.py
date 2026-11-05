from pathlib import Path
import json,re,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger11-20261107';Y=E.parent/'slice-d-entry4-20261106'
for name in ['ProofDriver','Driver']:
 s=(P/('NII_'+name+'.lean')).read_text();out=s.replace('NII_DIAGNOSTIC_IMPORT','NIM_COMBINED_IMPORT').replace('NII_','NIM_');(E/('NIM_'+name+'.lean')).write_text(out)
 (E/('NIM_'+name+'.diff')).write_text(''.join(difflib.unified_diff(s.splitlines(True),out.splitlines(True))))
roots=set(json.loads((P/'NII_AUDIT_ROOTS.json').read_text())['roots'])
for p in Y.glob('NHY_*.lean'):roots.update(re.findall(r'^#print axioms ([\w.]+)',p.read_text(),re.M))
# Same root names are preserved in copied modules.
roots=sorted(roots);n=7
(E/'NIM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NIM_AUDIT_MODULES.json').write_text(json.dumps([['NIM_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
b={r['module']:r['imports']for r in map(json.loads,(P/'NII_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in Y.glob('NHY_*.lean'):b[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
for p in E.glob('NIM_*.lean'):
 if p.stem.startswith('NIM_MapReference.'):m=p.stem
 else:m=p.stem
 b[m]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NIM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(b.items())))
(E/'NIM_batch.py').write_text((P/'NII_batch.py').read_text().replace('NII_','NIM_'))
p=E/'NIM_run.py';s=p.read_text().replace("['NIM_DIAGNOSTIC_IMPORT','NHJ_COMBINED_IMPORT']","['NIM_COMBINED_IMPORT']");p.write_text(s)
print('roots',len(roots))
