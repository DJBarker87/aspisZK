#!/usr/bin/env python3
"""Reuse the R63 full-runtime runner for one changed leaf or a final leaf list."""
from pathlib import Path
here=Path(__file__).parent
source=(here/'run_r63_lean.py').read_text().replace(
 "p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()",
 "p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--reuse',type=Path,required=True);p.add_argument('--target',action='append',required=True);a=p.parse_args()"
).replace("reuse=root/'aspis-r62-lean-20260929-a'","reuse=a.reuse").replace(
 "base='491ccd3d42e2e07ff2c04cb6dd17c7ea20269ed0'","base='a40fb23673ab80c67e99c06bf156f338b12b2a2e'"
).replace('r63_focused','r64_focused').replace(
 "targets=['AspisV8R19/'+n for n in ['InverseFieldSlice','InverseRuntimeMul','GeneratedInverseLoop']]",
 "targets=a.target\nassert not set(targets)&{r['target_name'] for r in records}"
).replace("'cached':len(records)-3,'compiled':3","'cached':len(records)-len(targets),'compiled':len(targets)")
source=source.replace('from audit_r63_source import check','from audit_r64_source import check_current')
old="audit=check(stage,sources/'AspisV8R19/InverseFieldSlice.lean',selected/'crates/aspis-core/src/field.rs',sources/'AspisV8R19/InverseChain.lean')"
assert source.count(old)==1
source=source.replace(old,"audit=check_current(root/'aspis-r64-extracted-20260929-b',sources/'AspisV8R19/GuardedFieldSlice.lean',selected,Path(__file__).parent/'r64-field-extraction')")
exec(compile(source,str(here/'run_r63_lean.py'),'exec'))
