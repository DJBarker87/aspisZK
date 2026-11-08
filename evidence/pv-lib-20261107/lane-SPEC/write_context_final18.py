"""Emit one SPEC-C17 successor; compile before emitting the next row."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];row=sys.argv[1]
assert row in ['361','270','166','15','208','220','316','318','219','125','6','170','17','5','2','1','0','OwnInit']
old='PV_LIB_SPEC_Context'+('OwnInit18' if row=='OwnInit' else 'F'+row+'18')
new='PV_LIB_SPEC_ContextFinal'+('OwnInit18' if row=='OwnInit' else 'F'+row+'18')
s=(R/'lean'/(old+'.lean')).read_text()
s=s.replace('import PV_LIB_SPEC_ContextPost18','import PV_LIB_SPEC_ContextCounterPost18')
s=s.replace('namespace '+old,'namespace '+new).replace('end '+old,'end '+new)
s=s.replace('PV_LIB_SPEC_ContextPost18.','PV_LIB_SPEC_ContextCounterPost18.').replace('PV_LIB_SPEC_ContextMachine18.observe','PV_LIB_SPEC_ContextCounter18.observe')
s='import '+old+'\nimport PV_LIB_SPEC_ContextCounterPost18\n'+s
marker=s.index('\n#print axioms')
s=s[:marker]+'\n/-- Immediate SPEC-C17 before statement, retained unchanged. -/\nabbrev CounterBefore := '+old+'.Contract\n'+s[marker:]
s=s.replace('#print axioms Before','#print axioms Before\n#print axioms CounterBefore')
p=R/'lean'/(new+'.lean');assert not p.exists();p.write_text(s)
