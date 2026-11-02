"""Runtime-world source spines; explicit external operators and partial view.
Native leaf adequacy is OPEN. Existing accepted spines remain unchanged.
"""
from pathlib import Path
import re,sys
short=sys.argv[1];assert short in ['MaterialFromEntropy','ApplyMaterial','PrivateSalts','PrepareOpening','PublishCompact','PrivateSaltStep']
p=Path('tools/pv-evh8-20261101/open_spine.py');s=p.read_text()
old="pure=lambda label:label.startswith('core.result.') or label in ['Aeneas.Std.lift','Array.index_usize']"
new="pure=lambda label:(label.startswith('core.result.') and label not in ['core.result.Result.map','core.result.Result.map_err']) or label in ['Aeneas.Std.lift','Array.index_usize']"
assert s.count(old)==1;s=s.replace(old,new)
s=s.replace("namespace='PV_EVH_'+short","namespace='PV_EVH_Runtime'+short").replace("receipt=E/(short+'-generation.json')","receipt=E/('Runtime'+short+'-generation.json')")
s=s.replace('PV_EVH_Prefix','PV_EVH_Runtime').replace('PV_EVH_ValueBind','PV_EVH_RuntimeValueBind')
s=s.replace('FinishedView','PartialView').replace('.bind_fixed','.bind_view').replace('.lift_fixed','.lift_view')
s=re.sub(r'\bP\b','Q',s)
exec(compile(s,str(p),'exec'))
