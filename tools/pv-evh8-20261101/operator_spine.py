"""Reify external Result operators before evaluation, in fresh source spines.
Keep accepted legacy modules byte-identical. No native installation is implied.
"""
from pathlib import Path
import sys
short=sys.argv[1]
assert short in ['MaterialFromEntropy','ApplyMaterial','PrivateSalts','PrepareOpening','PublishCompact','PrivateSaltStep']
p=Path('tools/pv-evh8-20261101/open_spine.py')
s=p.read_text()
old="pure=lambda label:label.startswith('core.result.') or label in ['Aeneas.Std.lift','Array.index_usize']"
new="pure=lambda label:(label.startswith('core.result.') and label not in ['core.result.Result.map','core.result.Result.map_err']) or label in ['Aeneas.Std.lift','Array.index_usize']"
assert s.count(old)==1
s=s.replace(old,new).replace("namespace='PV_EVH_'+short","namespace='PV_EVH_Op'+short").replace("receipt=E/(short+'-generation.json')","receipt=E/('Op'+short+'-generation.json')")
exec(compile(s,str(p),'exec'))
