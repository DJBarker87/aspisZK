"""Freeze the exact current, successfully compiled owned proof set for one final audit."""
from pathlib import Path
import json,re,hashlib
P=Path(__file__).resolve().parent
selected={}
for line in (P/'NKV_ATTEMPTS.jsonl').read_text().splitlines():
 a=json.loads(line)
 if a['kind']!='lean' or a['exit_status']!=0:continue
 r=json.loads((P/a['full_receipt']).read_text());m=r['module']
 if m in ['NKV_Driver','NKV_ProofDriver','NKV_COMBINED_IMPORT']:continue
 if not all((P/n).exists() and hashlib.sha256((P/n).read_bytes()).hexdigest()==h for n,h in r['source_hashes'].items()):continue
 selected[m]=r
own={m:r for m,r in selected.items() if m.startswith('NKV_')}
current={f.stem for f in P.glob('NKV_*.lean') if f.stem not in ['NKV_Driver','NKV_ProofDriver','NKV_COMBINED_IMPORT']}
assert current==set(own),(sorted(current-set(own)),sorted(set(own)-current))
roots={'AspisR1.RPx_Deployed.deployed'}
for r in selected.values():
 for line in r['print_axioms']:
  hit=re.fullmatch(r"'([^']+)' depends on axioms: \[([^]]*)\]",line)
  empty=re.fullmatch(r"'([^']+)' does not depend on any axioms",line)
  if empty:
   roots.add(empty[1]);continue
  assert hit,line
  assert set(x.strip() for x in hit[2].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},line
  roots.add(hit[1])
modules=['NKN_COMBINED_IMPORT','NKL_COMBINED_IMPORT']+sorted(own)
(P/'NKV_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in modules)+'set_option pp.proofs false\n'+''.join('#print '+r+'\n#print axioms '+r+'\n' for r in sorted(roots)))
records={}
for file in [Path('evidence/batch-merkle3-20261108/NKL_EXPECTED_IMPORTS.jsonl'),Path('evidence/ledger19-20261108/NKN_EXPECTED_IMPORTS.jsonl')]:
 for line in file.read_text().splitlines():
  row=json.loads(line);m=row['module'];assert m not in records or records[m]==row,m;records[m]=row
for m,r in selected.items():
 src=next(n for n in r['sources'] if n.endswith('.lean'))
 imports=['Init']+re.findall(r'^import (?:all )?([A-Za-z0-9_.]+)',(P/src).read_text(),re.M)
 records[m]={'module':m,'imports':list(dict.fromkeys(imports))}
records['NKV_COMBINED_IMPORT']={'module':'NKV_COMBINED_IMPORT','imports':['Init']+modules}
(P/'NKV_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(records[m])+'\n' for m in sorted(records)))
(P/'NKV_AUDIT_ROOTS.json').write_text(json.dumps({'roots':sorted(roots),'groups':[sorted(roots)]},indent=2)+'\n')
(P/'NKV_AUDIT_MODULES.json').write_text(json.dumps([['NKV_COMBINED_IMPORT']])+'\n')
(P/'NKV_PROOF_SET.json').write_text(json.dumps({m:{'attempt':r['attempt'],'source_hashes':r['source_hashes'],'source_revision':r['source_revision'],'print_axioms':r['print_axioms']} for m,r in selected.items()},indent=2)+'\n')
print(json.dumps({'owned_modules':len(own),'private_unchanged_modules':len(selected)-len(own),'audit_roots':len(roots),'expected_modules':len(records)}))
