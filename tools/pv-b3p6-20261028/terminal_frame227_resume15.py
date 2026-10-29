"""Every other callback field is preserved in the proof-only source installation.
Each theorem reduces one record projection only, never an arithmetic body.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';raw=(D/'resolved/R1Z/ProverRwFullExternalFuns.lean').read_text();ids=list(map(int,re.findall(r'^  op(\d+)\b',raw,re.M)));assert ids==list(range(262))
s='''import PV_B3P_TerminalInstall15227
namespace PV_B3P_Terminal15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
'''
for i in ids:
 if i==227:continue
 s+=f'''\ntheorem source_preserved_op{i}_15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) :
    @ExternalFuns.op{i} (PV_B3P_Install227.Types base) (source_install15 base original native) =
      @ExternalFuns.op{i} (PV_B3P_Install227.Types base) original := rfl
#print axioms source_preserved_op{i}_15
'''
s+='end\nend PV_B3P_Terminal15227\n';p=L/'PV_B3P_TerminalFrame15227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(other_fields=len(ids)-1,op227_only_update=True)))
