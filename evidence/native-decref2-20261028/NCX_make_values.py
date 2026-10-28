from pathlib import Path
L=Path('lean')
for family,key in [('Registry','registry'),('Entry','entry')]:
 ty='VerifierRegistryV2' if key=='registry' else 'VerifierRegistryEntryV2'
 s=f'import NCX_{family}Fields\nset_option autoImplicit false\nnamespace NCX_{family}Value\nopen Aeneas Aeneas.Std Result AspisR1\nopen NCX_{family}Fields\n'
 if key=='registry':
  s+='''\ndef value : NCX_Reference.VerifierRegistryV2 :=
  ⟨2#u8,255#u8,pool,authority,policy,generation,delay,program,loader,programdata,255#u8,executable_hash⟩
'''
  nonzero=['pool','policy','program','loader','programdata','executable_hash'];zero=['authority']
 else:
  s+='''\ndef value : NCX_Reference.VerifierRegistryEntryV2 :=
  ⟨.Active,1#u8,254#u8,pool,verifier,profile,release,loader,programdata,254#u8,executable_hash,upgrade_authority,activation,retirement,policy⟩
'''
  nonzero=['pool','verifier','profile','release','loader','programdata','executable_hash','policy'];zero=['upgrade_authority']
 for f in nonzero:
  s+=f'''theorem nz_{f} : NCX_Reference.required_binding_is_zero {f}=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change {f}.val.length ≤ 768;rw [{f}.property];scalar_tac
  · change NCV_ZeroStep.byte {f}.to_slice 0 ≠ 0#u8
    decide
  · change 0 < {f}.val.length;rw [{f}.property];scalar_tac
#print axioms nz_{f}
'''
 # decide on byte unequal 8bit only allowed tiny numerals (byte 168 etc tiny acceptable use by intro contradiction cases instead decide? decide tiny yes)
 for f in zero:
  s+=f'''theorem z_{f} : NCX_Reference.required_binding_is_zero {f}=ok true := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.zero _ 32 rfl (by omega)
#print axioms z_{f}
'''
 s+=f'theorem valid : NCX_Reference.validate_verifier_{"registry_v2" if key=="registry" else "registry_entry_v2"} value=ok (.Ok ()) := by\n'
 s+='  simp only [NCX_Reference.validate_verifier_'+('registry_v2' if key=='registry' else 'registry_entry_v2')+',value,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK,\n    '+','.join('nz_'+f for f in nonzero)+','+','.join('z_'+f for f in zero)+',lift,bind_tc_ok]\n  rfl\n#print axioms valid\n'
 s+=f'end NCX_{family}Value\n';(L/f'NCX_{family}Value.lean').write_text(s)
