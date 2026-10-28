from pathlib import Path
import json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
D=json.loads((P/'JHl_WEIGHT_PREFLIGHT.json').read_text());assert all(r['match'] for r in D['rows'])
files={}
for i in range(10):
 name=f'JHl_Basis{i:02}';f=D['factors'][i];n=D['nodes'][i]
 s=f'''import JGp_Rows
import JFn_Basis
set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
def node : U32 := {n}#u32
/-- Numeric identity for the SAME source node constructor. -/
theorem node_call : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value {i}).lineZ=ok node := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_NodeCall.source (JGp_Rows.value {i}).lineZ
  norm_num [JGp_Rows.value,JGp_Row{i}.value] at value
  have same : z=node := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms node_call
'''
 for k in range(6):
  s+=f'''\ntheorem factor{k} : doubledFactor (S7JoinBasisMachine.decode node) {k}=({f[k]} : M31Exact) := by
'''
  if k==0:s+='  rfl\n'
  else:s+=f'''  rw [doubledFactor,factor{k-1}]
  norm_num [M31Exact,P] <;> decide
'''
  s+=f'#print axioms factor{k}\n'
 s+=f'end AspisR1.{name}\nend\n';files[name]=s
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('10 bounded basis-factor modules validated')
