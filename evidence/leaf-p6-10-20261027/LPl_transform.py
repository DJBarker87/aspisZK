"""Name-only collision repair, with byte-for-byte reproduction checks."""
from pathlib import Path
import json,hashlib,sys,re
E=Path(__file__).resolve().parent;root=E.parent.parent
plan=json.loads((E/'LPl_inherited-plan.json').read_text())
prefixes={'XRk_':'LPl_Kit_', 'LPa_':'LPl_A_', 'LPc_':'LPl_C_', 'LPg_':'LPl_G_', 'LPa.':'LPl_A.', 'LPc.':'LPl_C.', 'LPg.':'LPl_G.'}
rows=[]
for item in plan:
 src=root/item['repository_source'];raw=src.read_bytes();s=raw.decode()
 for before,after in prefixes.items():s=s.replace(before,after)
 for before,after in [('LPa','LPl_A'),('LPc','LPl_C'),('LPg','LPl_G')]:s=re.sub(r'\b'+before+r'\b',after,s)
 m=item['module']
 for before,after in prefixes.items():m=m.replace(before,after)
 if item['module']=='XRk_Types':
  s=s.replace('import Aeneas\n','import Aeneas\nimport ImportUnionNamedDiscriminant\n',1)
  s=s.replace('@[discriminant isize','@[import_union_discriminant')
 out=E/(m+'.lean')
 if '--check' in sys.argv:assert out.read_bytes()==s.encode(),m
 else:out.write_bytes(s.encode())
 rows.append(dict(original=str(src.relative_to(root)),module=m,source_sha256=hashlib.sha256(raw).hexdigest(),sha256=hashlib.sha256(s.encode()).hexdigest(),bytes=len(s.encode()),repair='prefix replacement only; Types additionally uses selected enum-qualified discriminant attribute'))
if '--check' not in sys.argv:(E/'LPl_transform.json').write_text(json.dumps(rows,indent=2)+'\n')
else:assert rows==json.loads((E/'LPl_transform.json').read_text())
print('Checked',len(rows),'exact name-only copies')
