#!/usr/bin/env python3
"""Stage the exact extracted query loops, without admitting opaque guards.

The public argument-validation wrapper is intentionally excluded: its U32
is_power_of_two/ctpop primitive is not supplied by the pinned Aeneas runtime.
No theorem about that wrapper follows from this loop slice.
"""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--raw',type=Path,required=True)
p.add_argument('--destination',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
pins=json.loads((a.raw.parent.parent/'generated-pins.json').read_text())
for f in a.raw.iterdir():assert sha(f)==pins[str(f.relative_to(a.raw.parent.parent))]
out=a.destination/'AspisR86Query'
records={}
for name in ['Types','Funs']:
    original=(a.raw/(name+'.lean')).read_text()
    text=original
    if name=='Funs':
        marker='/-- [aspis_core::transcript::{aspis_core::transcript::Transcript}::challenge_queries_without_replacement]:\n'
        assert text.count(marker)==1
        text=text[:text.index(marker)]+'end AspisR86Query\n'
        assert text.count('import AspisR86Query.FunsExternal\n')==1
        text=text.replace('import AspisR86Query.FunsExternal\n','')
    assert not re.search(r'\b(axiom|sorry|admit)\b',text)
    text=text.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n')
    target=out/('Loops.lean' if name=='Funs' else 'Types.lean')
    if a.check:assert target.read_text()==text
    else:
        assert not target.exists();out.mkdir(parents=True,exist_ok=True);target.write_text(text)
    records[target.name]={'raw_sha256':sha(a.raw/(name+'.lean')),'staged_sha256':sha(target)}
print(json.dumps({'imports_and_exact_prefix_only':True,'staged':records,
    'excluded':['challenge_queries_without_replacement','query_probe'],
    'guard_primitive_proved':False,'templates_admitted':False}))
