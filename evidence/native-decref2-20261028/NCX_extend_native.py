from pathlib import Path
p=Path('evidence/native-decref2-20261028/NCX_instrument.py');s=p.read_text()
# Add validator contracts and local native-spec functions (no record copying).
start=s.index(" d['crates/aspis-statement/src/NCX_native.rs']=n")
s=s[:start]+''' for key,name,fun,arg in [('registry','VerifierRegistryV2','validate_verifier_registry_v2','registry'),('entry','VerifierRegistryEntryV2','validate_verifier_registry_entry_v2','entry')]:
  body=ref[ref.index('pub fn '+fun+'('):];body=body[:body.index('\\npub fn ') if '\\npub fn ' in body else len(body)]
  body=body.replace(fun,'valid_'+key+'_ref',1).replace('required_binding_is_zero(', 'crate::NCX_reference::required_binding_is_zero(')
  n+=body+'\\n'
''' +s[start:]
needle=" d[p]=s\n p='programs/r1-cost-probe/src/lib.rs'"
s=s.replace(needle,''' for key,fun,arg in [('registry','validate_verifier_registry_v2','registry'),('entry','validate_verifier_registry_entry_v2','entry')]:
  prop=f'*r==crate::NCX_native::valid_{key}_ref({arg})'
  if negative:prop='!('+prop+')'
  attrs=f'#[cfg_attr(kani,kani::modifies())]\\n#[cfg_attr(kani,kani::ensures(|r:&Result<(),PoolV1VerifierRegistryFormatError>|{prop}))]\\n'
  s=s.replace('pub fn '+fun+'(',attrs+'pub fn '+fun+'(',1)
 d[p]=s
 p='programs/r1-cost-probe/src/lib.rs' ''')
needle=" n+='#[kani::proof]\\n'+attrs+"
idx=s.index(needle)
s=s[:idx]+''' for key,name,fun in [('registry','VerifierRegistryV2','validate_verifier_registry_v2'),('entry','VerifierRegistryEntryV2','validate_verifier_registry_entry_v2')]:
  fs=fields[name]
  values=','.join(f+(': match kani::any::<u8>()%4{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}' if f=='status' else ':kani::any()') for f in fs)
  n+=f'#[kani::proof_for_contract(aspis_statement::pool_v1::verifier_registry::{fun})]\\n'+attrs+f'#[kani::unwind(34)]\\nfn NCX_validate_{key}_contract(){{let r={name}{{{values}}};let _={fun}(&r);}}\\n'
''' +s[idx:]
p.write_text(s)
