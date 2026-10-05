import json,pathlib
root=pathlib.Path('.');p=json.load(open(root/'.r21-scratch/r806-point02-selected-cells/PLAN.json'))['entries']
for point,row in [('p2',37),('p0',38)]:
 es=sorted([e for e in p if e['point']==point and 35<=e['flat_position']<=73],key=lambda x:x['flat_position']);vals=','.join(map(str,[e['first_limb'] for e in es]));caps=point.upper()
 src=f'''import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R813FiniteFunctionExt39
set_option autoImplicit false
namespace AspisV8R19.R812BlockSix{caps}CertificateRow
open AspisV8R19.R813FiniteFunctionExt39
noncomputable section
abbrev M := ZMod 2147483647
def {point}CertificateValues : Fin 39 → M := ![{vals}]
theorem certificate_{point}_values : (fun j : Fin 39 => R747JointBlock39Preflight.A (⟨{row},by decide⟩ : Fin 39) j) = {point}CertificateValues := by
  apply fin39_ext
'''
 for _ in es: src+='  · rfl\n'
 src+=f'''#print axioms certificate_{point}_values
end
end AspisV8R19.R812BlockSix{caps}CertificateRow
'''
 (root/f'.r21-scratch/R812BlockSix{caps}CertificateRow.lean').write_text(src)
