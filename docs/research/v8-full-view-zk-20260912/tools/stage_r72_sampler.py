#!/usr/bin/env python3
"""Import-only staging of the template-free extraction; no body replacement."""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('destination',type=Path)
p.add_argument('--check',action='store_true');a=p.parse_args()
assert sorted(f.name for f in a.raw.iterdir())==['Funs.lean','Types.lean']
for name in ['Types','Funs']:
    text=(a.raw/(name+'.lean')).read_text()
    assert text.count('import Aeneas\n')==1
    assert not re.search(r'\b(axiom|sorry|admit)\b',text)
    staged=text.replace('import Aeneas\n',
        'import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n')
    assert staged.split('namespace AspisR72Sampler\n',1)[1]==text.split('namespace AspisR72Sampler\n',1)[1]
    target=a.destination/'AspisR72Sampler'/(name+'.lean')
    if a.check:assert target.read_text()==staged
    else:
        assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True);target.write_text(staged)
print(json.dumps({'status':'PASS','imports_only':True,'templates':0}))
