from pathlib import Path
L=Path('lean')
s='''import NCX_RegistryFixture
import NCX_EntryFixture
import NCX_Install
import JHj_RegistryValue
set_option autoImplicit false
namespace NCX_FixtureCarriers
open Aeneas Aeneas.Std Result AspisR1
attribute [local irreducible] JHb_DataRegistry.bytes JHb_DataEntry.bytes
'''
for family,key in [('Registry','registry'),('Entry','entry')]:
 # Map local fields to exact cohort record fields and symbolic byte laws.
 rows=[('pool','pool','pool' if key=='registry' else 'entry_pool')]
 if key=='registry':rows += [('policy','policy_binding','policy'),('program','registry_program','program')]
 else:rows += [('verifier','verifier_program','verifier'),('profile','profile_binding','profile'),('release','release_binding','release'),('policy','policy_binding','entry_policy')]
 for local,field,binding in rows:
  s+=f'''theorem {key}_{local} : NCX_{family}Fields.{local}=JHj_RegistryValue.{key}.{field} := by
  apply Subtype.ext
  exact JHg_Audit{family}.{local}.symm.trans JHg_BindingsRegistry.{binding}
#print axioms {key}_{local}
'''
 for local,field in [('loader','loader_program'),('programdata','programdata_address')]:
  aud='Registry' if local=='loader' else family
  s+=f'''theorem {key}_{local} : NCX_{family}Fields.{local}=JHj_RegistryValue.{key}.{field} := by
  apply Subtype.ext
  exact JHg_Audit{aud}.{local}.symm
#print axioms {key}_{local}
'''
 s+=f'''theorem {key} : NCX_Carrier.{key} NCX_{family}Value.value=JHj_RegistryValue.{key} := by
  simp only [NCX_Carrier.{key},NCX_{family}Value.value,
    {','.join(key+'_'+l for l,_,_ in rows)},{key}_loader,{key}_programdata]
  rfl
#print axioms {key}
'''
s+='end NCX_FixtureCarriers\n';(L/'NCX_FixtureCarriers.lean').write_text(s)
