# Executed by NBH_generate in its pinned-source context.
def construct(file,ty):
 s=frozen(file).split('pub struct '+ty+' {',1)[1].split('\n}',1)[0]
 fields=re.findall(r'^    pub (\w+): ([^\n]+),$',s,re.M)
 def val(t):
  if t=='VerifierEntryStatusV1': return 'match kani::any::<u8>() % 4 {0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}'
  if t=='M31':return 'M31(kani::any())'
  return 'kani::any()'
 return ty+'{'+','.join(n+':'+val(t) for n,t in fields)+'}'
reg='use super::*;\n'
Ereg='PoolV1VerifierRegistryFormatError'
for ver in [1,2]:
 for entry in [False,True]:
  ty='VerifierRegistry'+('Entry' if entry else '')+'V'+str(ver)
  name='validate_verifier_registry_'+('entry_' if entry else '')+'v'+str(ver)
  fields=(['pool','verifier_program','profile_binding','release_binding']+(['loader_program','programdata_address','executable_hash'] if ver==2 else [])+['policy_binding'] if entry else ['pool','policy_binding']+(['registry_program','loader_program','programdata_address','executable_hash'] if ver==2 else []))
  zero=' || '.join('r.'+f+'==[0;32]' for f in fields)
  checks=[]
  checks.append(('r.statement_version==0','InvalidStatementVersion') if entry else ('r.flags>3','UnsupportedFlags'))
  checks.append((zero,'ZeroRequiredBinding'))
  if entry:
   if ver==2:checks.append(('r.expected_upgrade_authority!=[0;32]','InvalidAuthorityMode'))
   checks.append(('r.retirement_slot!=u64::MAX && r.retirement_slot<=r.activation_slot','InvalidRetirementSlot'))
  else:
   checks.extend([('((r.flags/2)%2==1)!=(r.authority==[0;32])','InvalidAuthorityMode'),('r.minimum_activation_delay_slots==0','InvalidActivationDelay')])
  result=' else '.join('if '+c+' {Err('+Ereg+'::'+e+')}' for c,e in checks)+' else {Ok(())}'
  reg+=f'fn NBH_{name}(r: &{ty})->Result<(),{Ereg}> {{{result}}}\n'
  reg+=f'#[kani::proof]\nfn NBH_{name}_gate() {{let r={construct("verifier_registry.rs",ty)}; assert_eq!({name}(&r),NBH_{name}(&r));}}\n'
reg+='''#[kani::proof]
fn NBH_zero_gate() { let b:[u8;32]=kani::any(); let z=required_binding_is_zero(&b); let j:usize=kani::any(); kani::assume(j<32); if z {assert_eq!(b[j],0);} if b==[0;32] {assert!(z);} }
'''
# Full decoder Result for arbitrary fixed-capacity slices. Width mismatch is
# independent of contents. Success field transport and ordered validator errors.
for ver,entry,N,magic in [(1,False,128,'ASRG'),(1,True,192,'ASRE'),(2,False,256,'ASR2'),(2,True,320,'ASE2')]:
 ty='VerifierRegistry'+('Entry' if entry else '')+'V'+str(ver)
 name='decode_verifier_registry_'+('entry_' if entry else '')+'v'+str(ver)
 validator='validate_verifier_registry_'+('entry_' if entry else '')+'v'+str(ver)
 checks=[(f'b.len()!={N}','WrongLength'),(f'&b[..4]!=b"{magic}"','WrongMagic'),(f'b[4]!={ver+1}','WrongVersion')]
 if ver==2:checks.append((f'b[{7 if entry else 6}]!=1','InvalidDeploymentMode'))
 reserved= ('b[184..192]!=[0;8]' if entry else 'b[7]!=0 || b[120..128]!=[0;8]') if ver==1 else ('b[314..320]!=[0;6]' if entry else 'b[249..256]!=[0;7]')
 checks.append((reserved,'NonZeroReserved'))
 code=''
 for c,e in checks:code+=f'if {c} {{return Err({Ereg}::{e});}}\n'
 if entry:
  code+='let status=match b[5] {0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,3=>VerifierEntryStatusV1::Retired,_=>return Err('+Ereg+'::InvalidStatus)};\n'
  fields={'status':'status','statement_version':'b[6]','bump':f'b[{7 if ver==1 else 312}]','pool':(8,40),'verifier_program':(40,72),'profile_binding':(72,104),'release_binding':(104,136),'activation_slot':(136,144) if ver==1 else (264,272),'retirement_slot':(144,152) if ver==1 else (272,280),'policy_binding':(152,184) if ver==1 else (280,312)}
  if ver==2:fields.update(loader_program=(136,168),programdata_address=(168,200),executable_hash=(200,232),expected_upgrade_authority=(232,264),programdata_bump='b[313]')
 else:
  fields={'flags':'b[5]','bump':f'b[{6 if ver==1 else 7}]','pool':(8,40),'authority':(40,72),'policy_binding':(72,104),'generation':(104,112),'minimum_activation_delay_slots':(112,120)}
  if ver==2:fields.update(registry_program=(120,152),loader_program=(152,184),programdata_address=(184,216),executable_hash=(216,248),programdata_bump='b[248]')
 for k,v in fields.items():
  if isinstance(v,tuple):
   lo,hi=v; fields[k]=(f'u64::from_le_bytes(b[{lo}..{hi}].try_into().unwrap())' if hi-lo==8 else f'b[{lo}..{hi}].try_into().unwrap()')
 code+='let r='+ty+'{'+','.join(k+':'+v for k,v in fields.items())+'};\n'
 code+=f'NBH_{validator}(&r)?; Ok(r)'
 reg+=f'fn NBH_{name}(b: &[u8])->Result<{ty},{Ereg}> {{{code}}}\n'
 reg+=f'''#[kani::proof]
fn NBH_{name}_gate() {{let b:[u8;{N+1}]=kani::any(); let len:usize=kani::any(); kani::assume(len<={N+1}); assert_eq!({name}(&b[..len]),NBH_{name}(&b[..len]));}}
'''
files[ROOT+'NBH_registry.rs']=reg
fmt='use super::*;\n'
fmt+='''fn NBH_policy(p: &VerifierPolicyV1)->Result<(),PoolV1FormatError> {
 let err=if p.flags>3 {Some(PoolV1FormatError::UnsupportedFlags)} else if p.registry_program==[0;32] || p.policy_binding==[0;32] {Some(PoolV1FormatError::ZeroRequiredBinding)} else if (p.flags%2==1 && (p.flags/2)%2==0) || (((p.flags/2)%2==1)!=(p.registry_authority==[0;32])) {Some(PoolV1FormatError::InvalidAuthorityMode)} else {None}; match err {Some(e)=>Err(e),None=>Ok(())}
}
#[kani::proof]
fn NBH_policy_gate() {let p='''+construct('format.rs','VerifierPolicyV1')+''';assert_eq!(validate_verifier_policy_v1(&p),NBH_policy(&p));}
'''
# Policy bit constants audited below: immutable registry is bit0, deployment bit1.
fmt=fmt.replace('(p.flags%2==1 && (p.flags/2)%2==0)','((p.flags/2)%2==1 && p.flags%2==0)').replace('(((p.flags/2)%2==1)!=','((p.flags%2==1)!=')
fmt+='''fn NBH_identity(b: &[u8])->Result<PoolIdentityV1,PoolV1FormatError> {
 if b.len()!=144 {return Err(PoolV1FormatError::WrongLength)}
 if &b[..4]!=b"ASPI" {return Err(PoolV1FormatError::WrongMagic)}
 if b[4]!=1 {return Err(PoolV1FormatError::WrongVersion)}
 if b[5..8]!=[0;3] || b[108..112]!=[0;4] {return Err(PoolV1FormatError::NonZeroReserved)}
 let asset=u32::from_le_bytes(b[104..108].try_into().unwrap());
 if asset>=2147483647 {return Err(PoolV1FormatError::NonCanonicalAssetId)}
 Ok(PoolIdentityV1{pool:b[8..40].try_into().unwrap(),asset_mint:b[40..72].try_into().unwrap(),token_program:b[72..104].try_into().unwrap(),asset_id:M31(asset),deployment_domain:b[112..144].try_into().unwrap()})
}
#[kani::proof]
fn NBH_identity_gate() {let b:[u8;145]=kani::any(); let n:usize=kani::any();kani::assume(n<=145);assert_eq!(decode_pool_identity_v1(&b[..n]),NBH_identity(&b[..n]));}
fn NBH_policy_decode(b: &[u8])->Result<VerifierPolicyV1,PoolV1FormatError> {
 if b.len()!=104 {return Err(PoolV1FormatError::WrongLength)}
 if &b[..4]!=b"ASPP" {return Err(PoolV1FormatError::WrongMagic)}
 if b[4]!=1 {return Err(PoolV1FormatError::WrongVersion)}
 if b[6..8]!=[0;2] {return Err(PoolV1FormatError::NonZeroReserved)}
 let p=VerifierPolicyV1{flags:b[5],registry_program:b[8..40].try_into().unwrap(),registry_authority:b[40..72].try_into().unwrap(),policy_binding:b[72..104].try_into().unwrap()}; NBH_policy(&p)?; Ok(p)
}
#[kani::proof]
fn NBH_policy_decode_gate() {let b:[u8;105]=kani::any(); let n:usize=kani::any();kani::assume(n<=105);assert_eq!(decode_verifier_policy_v1(&b[..n]),NBH_policy_decode(&b[..n]));}
'''
files[ROOT+'NBH_format.rs']=fmt
