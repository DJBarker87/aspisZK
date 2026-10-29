"""Compare integer macro bodies potentially inlined or recognized by MIR.
Supporting over-approximation only: it does not establish complete source-level
reachability before inlining. Existing source cohorts/capture remain immutable.
"""
from pathlib import Path
import json,sys
if len(sys.argv)==1:sys.argv.append('partsstdcone')
s=Path('tools/pv-b3p6-20261028/std227_compare_resume5.py').read_text();d={};exec(s[:s.index('indices=')],d)
x=d['x'];index=d['index'];tokens=d['tokens'];p='core/src/num/uint_macros.rs';a=index(x['files'][p]['extractor']['text']);b=index(x['files'][p]['deployed']['text'])
names=['wrapping_add','wrapping_sub','wrapping_mul','wrapping_shl','wrapping_shr','overflowing_add','overflowing_sub','overflowing_mul','unchecked_shl','unchecked_shr','count_ones','trailing_zeros','checked_add'];rows=[]
for name in names:
 aa=[q for q in a if q['name']==name];bb=[q for q in b if q['name']==name];assert len(aa)==len(bb)==1
 same=tokens(aa[0]['body'])==tokens(bb[0]['body']);rows.append(dict(name=name,status='identical-body'if same else'different-body-law-required',extractor=aa[0],deployed=bb[0]))
out=dict(scope='additional integer macro bodies potentially inlined/recognized as MIR primitives; supporting source audit, not a complete pre-inline reachability proof',rows=rows);Path('evidence/pv-b3p6-20261028/std227-inlined-integer-bodies-resume5.json').write_text(json.dumps(out,indent=2)+'\n');print('identical',sum(r['status']=='identical-body'for r in rows),'of',len(rows))
