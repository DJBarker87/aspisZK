"""Freeze the accepted new-module manifest; create one combined, axioms and
focused closure audit. No failed or unsubmitted declaration is credited.
"""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume14';L=D/'lean'
rows=json.loads((O/'TALLY-resume14.json').read_text())['receipts'];latest={r['module']:r for r in rows}
modules=[];theorems=[];defs=[]
for mod,r in latest.items():
 if r['exit']!=0:continue
 p=L/(mod+'.lean');s=p.read_text();ns=None
 for line in s.splitlines():
  if line.startswith('namespace '):ns=line.split()[1]
  m=re.match(r'(?:noncomputable )?theorem\s+([A-Za-z0-9_]+)',line)
  if m:
   assert ns;theorems.append(ns+'.'+m[1])
 modules.append(mod);defs.append(dict(module=mod,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
assert len(theorems)==len(set(theorems))
imports='\n'.join('import '+m for m in modules)+'\n'
(L/'PV_B3P_Resume14Combined.lean').write_text(imports+'\n#print axioms PV_B3P_Groups14227.selected_all_groups14\n#print axioms PV_B3P_Groups14227.all_groups_joint_witness14\n#print axioms PV_B3P_FrontierStages14227.frontier_indexed_binding14\n')
(L/'PV_B3P_Resume14Axioms.lean').write_text('import PV_B3P_Resume14Combined\n'+'\n'.join('#print axioms '+t for t in theorems)+'\n')
(L/'PV_B3P_Resume14Focused.lean').write_text('import PV_B3P_Resume14Combined\n'+'''#print axioms PV_B3P_Correct14227.selected_callback14
#print axioms PV_B3P_Correct14227.corrected_callback_joint_witness14
#print axioms PV_B3P_Groups14227.source_groups_joint_witness14
#print axioms PV_B3P_Loans14227.transition_loan_continuation14
#print axioms PV_B3P_Fields14227.fields_slice_caller14
#print axioms PV_B3P_Binding14227.matrix_trace_binding14
''')
(O/'focused-manifest.json').write_text(json.dumps(dict(entry='bb12e1b99e63ca6e18a3cb75b646ee8ab159258a',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources=defs,new_theorems=theorems,modules=modules,native_callback_closed=False,scope='one final replay of new accepted focused closure only; unchanged frozen endpoint manifest not repeated'),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),theorems=len(theorems))))
