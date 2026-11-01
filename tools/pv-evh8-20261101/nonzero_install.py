"""Install the source nonzero loop at both entropy call sites; no native claim."""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-evh8-20261101')
s=Path('lean/PV_EVH_EntropyStep.lean').read_text()
fields=s.split('structure Callees where\n',1)[1].split('\nstructure Compatible',1)[0]
fields=fields.split('  entropy_nonzero32_OPEN',1)[0]
views=s.split('structure Compatible (c : Callees) : Prop where\n',1)[1].split('\nopen ControlFlow',1)[0]
views=views.split('  entropy_nonzero32_fixed',1)[0]
import re
names=re.findall(r'^  (\w+)_OPEN :',fields,re.M)
out='''import PV_EVH_NonzeroFlow
import PV_EVH_EntropyStep
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Remaining entropy leaves only; no whole nonzero answer is accepted. -/
structure Callees where
'''+fields+'\nstructure Compatible (c : Callees) : Prop where\n'+views+'''
def install (fuel : Nat) (c : Callees) : PV_EVH_EntropyStep.Callees where
'''+''.join('  '+n+'_OPEN := c.'+n+'_OPEN\n' for n in names)+'''  entropy_nonzero32_OPEN := PV_EVH_NonzeroFlow.run fuel

theorem install_fixed (fuel : Nat) (c : Callees) (hc : Compatible c) :
    PV_EVH_EntropyStep.Compatible (install fuel c) where
'''+''.join('  '+n+'_fixed := hc.'+n+'_fixed\n' for n in names)+'''  entropy_nonzero32_fixed := PV_EVH_NonzeroFlow.run_fixed fuel
#print axioms install_fixed
end PV_EVH_NonzeroInstall
'''
p=Path('lean/PV_EVH_NonzeroInstall.lean')
if '--check' in sys.argv:assert p.read_text()==out;print('PASS nonzero source installation')
else:p.write_text(out);print('Generated nonzero source installation',len(names),'remaining leaves')
