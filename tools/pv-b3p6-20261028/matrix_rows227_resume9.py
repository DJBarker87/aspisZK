"""Keep each three-cell row in one focused source-binding module."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';rows=[]
for component in range(3):
 module=f'PV_B3P_MatrixRow9{component}227'
 s='import PV_B3P_MatrixCell9227\nnamespace PV_B3P_Binding9227\nopen Aeneas Aeneas.Std\nset_option autoImplicit false\n'
 for channel in range(3):
  raw=(L/f'PV_B3P_MatrixCell9{component}{channel}227.lean').read_text()
  s+='\n'+raw[raw.index('theorem '):raw.rindex('end PV_B3P_Binding9227')]
 s+='end PV_B3P_Binding9227\n'
 p=L/(module+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
 rows.append(dict(module=module,component=component,theorems=[f'PV_B3P_Binding9227.accumulation_store9_{component}_{k}'for k in range(3)]))
aggregate='import PV_B3P_MatrixCell9227\nnamespace PV_B3P_Binding9227\nopen Aeneas Aeneas.Std\nset_option autoImplicit false\n'
for component in range(3):
 for channel in range(3):
  raw=(L/f'PV_B3P_MatrixCell9{component}{channel}227.lean').read_text()
  aggregate+='\n'+raw[raw.index('theorem '):raw.rindex('end PV_B3P_Binding9227')]
aggregate+='end PV_B3P_Binding9227\n'
p=L/'PV_B3P_MatrixStores9227.lean'
if '--check'in sys.argv:assert p.read_text()==aggregate
else:p.write_text(aggregate)
p=D/'resume9/matrix-row-applications.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==rows
else:p.write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows))
