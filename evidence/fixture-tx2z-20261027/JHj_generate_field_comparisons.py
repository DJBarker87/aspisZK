from pathlib import Path
R=Path(__file__).resolve().parents[2]
registry=[('pool','JHj_Seeds.key'),('authority','JHg_AccountValues.master.verifier_policy.registry_authority'),('policy_binding','JHg_AccountValues.master.verifier_policy.policy_binding'),('registry_program','JHb_Programs.registry'),('loader_program','JHj_RegistryValue.loader'),('programdata_address','JHj_RegistryValue.registryProgramdata')]
entry=[('pool','JHj_Seeds.key'),('policy_binding','AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING'),('verifier_program','CPH_Program.verifier'),('profile_binding','AdapterRw.r1_pool_adapter.PROFILE_BINDING'),('release_binding','AdapterRw.r1_pool_adapter.RELEASE_BINDING'),('loader_program','JHj_RegistryValue.loader'),('programdata_address','JHj_RegistryValue.verifierProgramdata'),('expected_upgrade_authority','Array.repeat 32#usize 0#u8')]
for n,fields in [('Registry',registry),('Entry',entry)]:
 name='JHj_'+n+'Fields'
 s='import JHj_RegistryValue\nimport JHj_RegistryGuards\nset_option autoImplicit false\nnamespace AspisR1.'+name+'\nopen Aeneas Aeneas.Std Result\n'
 for field,rhs in fields:
  s+='\ntheorem '+field+' : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8\n    JHj_RegistryValue.'+n.lower()+'.'+field+' ('+rhs+')=ok false := by\n'
  if field=='policy_binding' and n=='Registry':s+='  unfold JHj_RegistryValue.registry AdapterRw.r1_pool_adapter.AUDIT_POLICY_BINDING\n'
  s+='  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _\n#print axioms '+field+'\n'
 s+='end AspisR1.'+name+'\n'
 (R/'lean'/(name+'.lean')).write_text(s)
