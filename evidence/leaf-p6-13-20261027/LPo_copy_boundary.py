"""Import/name-only copies of accepted partial boundary proofs to LPn's carrier.
No proof-body edits. Original closed leaf packets remain untouched.
"""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
roots=[Path('evidence/leaf-p6-1-20261027'),Path('evidence/leaf-p6-3-20261027')]
index={p.stem:p for root in roots for p in root.glob('*.lean')};order=[];seen=set()
def visit(m):
 if not m.startswith(('LPa_','LPc_')) or m in seen:return
 seen.add(m);p=index[m]
 for l in p.read_text().splitlines():
  if l.startswith('import '):
   for d in l[7:].split():visit(d)
 order.append(m)
visit('LPc_BoundaryProducer')
mod={m:'LPo_B_'+m for m in order};maps={**mod,'XRk_DecodeModels':'LPn_Kit_DecodeModels','XRk_FieldExternal':'LPl_Kit_FieldExternal','XRk_ByteFields':'LPn_Kit_ByteFields','XRk_Release':'LPl_Kit_Release','XRk_Field':'LPl_Kit_Field','XRk_word':'LPn_Kit_word','XRk_q':'LPn_Kit_q','LPa.':'LPo.BA.','namespace LPa\n':'namespace LPo.BA\n','end LPa\n':'end LPo.BA\n','LPc.':'LPo.BC.'}
rows=[]
for m in order:
 p=index[m];raw=p.read_text();s=raw
 s=re.sub('|'.join(re.escape(k) for k in sorted(maps,key=len,reverse=True)),lambda m:maps[m.group()],s)
 (E/(mod[m]+'.lean')).write_text(s)
 rows.append({'module':mod[m],'original':str(p),'original_sha256':hashlib.sha256(raw.encode()).hexdigest(),'sha256':hashlib.sha256(s.encode()).hexdigest()})
(E/'LPo_BOUNDARY_COPIES.json').write_text(json.dumps({'mapping':maps,'sources':rows},indent=2)+'\n')
print('\n'.join(x['module'] for x in rows))
