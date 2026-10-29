"""Small symbolic literal-length facts: elements are arbitrary, never reduced."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean');out=['import Aeneas.Std\nnamespace PV_B3P_Length227\nopen Aeneas Aeneas.Std\nset_option autoImplicit false\n']
for n in (3,4,7,8,10,14,15,16,20,32,64):
 args=' '.join('x'+str(i)for i in range(n));xs=','.join('x'+str(i)for i in range(n));out.append(f'theorem size{n} {{α : Type}} ({args} : α) :\n    ([{xs}] : List α).length=({n}#usize).val := rfl\n#print axioms size{n}\n')
out.append('end PV_B3P_Length227\n');(D/'PV_B3P_Length227.lean').write_text('\n'.join(out))
