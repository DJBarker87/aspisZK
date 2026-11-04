from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent
rows={x['module']:x['imports'] for x in map(json.loads,lzma.open(E.parent/'coherent-20261102/NER_STREAM_B_COHORT.jsonl.xz','rt'))}
x=json.loads((E/'NFE_INVENTORY.json').read_text())
for m,r in x['used'].items():rows.setdefault(m,['Init']+r['imports'])
for p in E.glob('NFE_*.lean'):
 rows[p.stem]=['Init']+[n for l in p.read_text().splitlines() if l.startswith('import ') for n in l[7:].split() if n!='all']
p=E/'NFE_EXPECTED_IMPORTS.jsonl';p.write_text(''.join(json.dumps(dict(module=m,imports=list(dict.fromkeys(ins))))+'\n' for m,ins in sorted(rows.items())))
print(len(rows),'pinned expected module import lists')
