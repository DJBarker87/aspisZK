#!/usr/bin/env python3
"""Reuse byte/token-identical extracted types/loops and add the actual entry."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--raw',type=Path,required=True);p.add_argument('--sources',type=Path,required=True)
p.add_argument('--check',action='store_true');a=p.parse_args()
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
pins=json.loads((a.raw.parent.parent/'generated-pins.json').read_text())
for f in a.raw.iterdir():assert sha(f)==pins[str(f.relative_to(a.raw.parent.parent))]
def norm(s):
    s=s.replace('AspisR98Query','AspisR86Query')
    s=s.split('namespace AspisR86Query\n',1)[1]
    s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
    return ''.join(s.split())
raw=(a.raw/'Funs.lean').read_text().replace('AspisR98Query','AspisR86Query')
marker='/-- [aspis_core::transcript::{aspis_core::transcript::Transcript}::challenge_queries_without_replacement]:\n'
assert raw.count(marker)==1;prefix,suffix=raw.split(marker,1)
assert norm(prefix+'end AspisR86Query\n')==norm((a.sources/'AspisR86Query/Loops.lean').read_text())
assert norm((a.raw/'Types.lean').read_text())==norm((a.sources/'AspisR86Query/Types.lean').read_text())
text='''-- Generated R98 public entry; exact old types/loops checked by stage_r98_entry.py.
import AspisR86Query.Loops
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
namespace AspisR86Query
'''+marker+suffix
assert not re.search(r'\b(axiom|sorry|admit|ctpop|is_power_of_two)\b',text)
out=a.sources/'AspisV8R19/QueryEntrySource.lean'
if a.check:assert out.read_text()==text
else:assert not out.exists();out.write_text(text)
print(json.dumps({'raw_funs_sha256':sha(a.raw/'Funs.lean'),'raw_types_sha256':sha(a.raw/'Types.lean'),
 'old_types_sha256':sha(a.sources/'AspisR86Query/Types.lean'),'old_loops_sha256':sha(a.sources/'AspisR86Query/Loops.lean'),
 'entry_sha256':sha(out),'types_and_loop_definitions_identical':True,'new_templates':0}))
