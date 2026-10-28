from pathlib import Path
import subprocess,re,os,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
orig=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
negative=bool(os.environ.get('NCX_NEGATIVE'))
case=os.environ.get('NCX_CASE','full')
ref=(E/'NCX_reference.rs').read_text()
fields={name:re.findall(r'pub (\w+):',ref.split('pub struct '+name+' {')[1].split('\n}')[0]) for name in ['VerifierRegistryV2','VerifierRegistryEntryV2']}
# The source has spaces after colon; field names alone matter.
def files():
 d={}
 p='crates/aspis-statement/src/lib.rs';d[p]=orig(p)+'\n#[cfg(kani)] pub mod NCX_reference;\n#[cfg(kani)] pub mod NCX_native;\n'
 d['crates/aspis-statement/src/NCX_reference.rs']=ref
 n='#![allow(non_snake_case,dead_code)]\nuse crate::pool_v1::verifier_registry::*;\nuse crate::NCX_reference as R;\n'
 enums=['PoolV1VerifierRegistryFormatError','VerifierEntryStatusV1']
 for name in enums:
  variants=re.findall(r'^    (\w+)',ref.split('pub enum '+name+' {')[1].split('}')[0],re.M)
  n+=f'fn eq_{name}(a:&{name},b:&R::{name})->bool {{match (a,b){{'+''.join(f'({name}::{v},R::{name}::{v})=>true,' for v in variants)+'_=>false}}\n'
 for key,name in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
  fs=re.findall(r'pub (\w+)\s*:',ref.split('pub struct '+name+' {')[1].split('\n}')[0]);fields[name]=fs
  expr=[]
  for f in fs:
   expr.append('eq_VerifierEntryStatusV1(&a.status,&b.status)' if f=='status' else 'a.'+f+'==b.'+f)
  n+=f'pub fn eq_{key}(a:&Result<{name},PoolV1VerifierRegistryFormatError>,b:&Result<R::{name},R::PoolV1VerifierRegistryFormatError>)->bool {{match (a,b){{(Ok(a),Ok(b))=>'+ ' && '.join(expr)+', (Err(a),Err(b))=>eq_PoolV1VerifierRegistryFormatError(a,b),_=>false}}\n'
 for key,name,fun,arg in [('registry','VerifierRegistryV2','validate_verifier_registry_v2','registry'),('entry','VerifierRegistryEntryV2','validate_verifier_registry_entry_v2','entry')]:
  body=ref[ref.index('pub fn '+fun+'('):];body=body[:body.index('\npub fn ') if '\npub fn ' in body else len(body)]
  body=body.replace(fun,'valid_'+key+'_ref',1).replace('required_binding_is_zero(', 'crate::NCX_reference::required_binding_is_zero(')
  n+=body+'\n'
 for name in ['VerifierRegistryV2','VerifierRegistryEntryV2']:
  fs=fields[name]
  values=','.join(f+(': match kani::any::<u8>()%4{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}' if f=='status' else ':kani::any()') for f in fs)
  n+='impl kani::Arbitrary for '+name+'{fn any()->Self{Self{'+values+'}}}\n'
 n+='impl kani::Arbitrary for PoolV1VerifierRegistryFormatError {fn any()->Self{match kani::any::<u8>()%12{'+','.join(str(i)+'=>Self::'+v for i,v in enumerate(['WrongLength','WrongMagic','WrongVersion','NonZeroReserved','UnsupportedFlags','InvalidStatus','InvalidAuthorityMode','ZeroRequiredBinding','InvalidActivationDelay','InvalidStatementVersion','InvalidRetirementSlot']))+',_=>Self::InvalidDeploymentMode}}}\n'
 for key,name in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
  fs=fields[name];expr=[]
  for i,f in enumerate(fs):
   cmp='eq_VerifierEntryStatusV1(&a.status,&b.status)' if f=='status' else f'a.{f}[j]==b.{f}[j]' if f in ['pool','authority','policy_binding','registry_program','loader_program','programdata_address','executable_hash','verifier_program','profile_binding','release_binding','expected_upgrade_authority'] else f'a.{f}==b.{f}'
   expr.append(str(i)+'=>'+cmp)
  n+=f'pub fn eq_{key}_coord(a:&Result<{name},PoolV1VerifierRegistryFormatError>,b:&Result<R::{name},R::PoolV1VerifierRegistryFormatError>,field:usize,j:usize)->bool{{match (a,b){{(Ok(a),Ok(b))=>match field{{'+','.join(expr)+',_=>false},(Err(a),Err(b))=>eq_PoolV1VerifierRegistryFormatError(a,b),_=>false}}\n'
 d['crates/aspis-statement/src/NCX_native.rs']=n
 p='crates/aspis-statement/src/pool_v1/verifier_registry.rs';s=orig(p)
 for key,fun in [('registry','decode_verifier_registry_v2'),('entry','decode_verifier_registry_entry_v2')]:
  ty='VerifierRegistryV2' if key=='registry' else 'VerifierRegistryEntryV2'
  if case=='full':domain='true'
  elif case=='length':domain='bytes.len()!='+('256' if key=='registry' else '320')
  elif case in ['reject','magic','version','mode','reserved']:
   size=256 if key=='registry' else 320;mode=6 if key=='registry' else 7;res=249 if key=='registry' else 314
   domain=f'bytes.len()!={size} || bytes[0]==0 || bytes[4]==0 || bytes[{mode}]==0 || bytes[{res}]!=0'
   if case!='reject':domain=f'bytes.len()=={size} && '+{'magic':'bytes[0]==0','version':'bytes[4]==0','mode':f'bytes[{mode}]==0','reserved':f'bytes[{res}]!=0'}[case]
  else:domain='true'
  prop=f'crate::NCX_native::eq_{key}(r,&crate::NCX_reference::{fun}(bytes))'
  if negative:prop='!('+prop+')'
  attrs=f'#[cfg_attr(kani,kani::requires({domain}))]\n#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r:&Result<{ty},PoolV1VerifierRegistryFormatError>|{prop}))]\n'
  s=s.replace('pub fn '+fun+'(',attrs+'pub fn '+fun+'(',1)
 for key,fun,arg in [('registry','validate_verifier_registry_v2','registry'),('entry','validate_verifier_registry_entry_v2','entry')]:
  prop=f'*r==crate::NCX_native::valid_{key}_ref({arg})'
  if negative:prop='!('+prop+')'
  attrs=f'#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r:&Result<(),PoolV1VerifierRegistryFormatError>|{prop}))]\n'
  s=s.replace('pub fn '+fun+'(',attrs+'pub fn '+fun+'(',1)
 d[p]=s
 p='programs/r1-cost-probe/src/lib.rs' ;s=orig(p);s=s.replace('use aspis_r1_cost_probe::verifier','#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;\nuse aspis_r1_cost_probe::verifier',1)
 s+='\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCX_KMX;\n#[cfg(kani)] mod NCX_native;\n';d[p]=s
 attrs='''#[kani::stub(<[u8]>::copy_from_slice,crate::NCX_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCX_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCX_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCX_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCX_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCX_KMX::KMX_realloc)]
'''
 n='#![allow(non_snake_case,dead_code)]\nuse aspis_statement::pool_v1::verifier_registry::*;\n'
 for key,fun,size in [('registry','decode_verifier_registry_v2',256),('entry','decode_verifier_registry_entry_v2',320)]:
  sz=0 if case=='length' else size
  n+=f'#[kani::proof_for_contract(aspis_statement::pool_v1::verifier_registry::{fun})]\n'+attrs+f'#[kani::unwind(34)]\nfn NCX_{key}_contract(){{let b:[u8;{sz}]=kani::any();let _={fun}(&b);}}\n'
  if case in ['reject','magic','version','mode','reserved']:
   mode=6 if key=='registry' else 7;res=249 if key=='registry' else 314;third=82 if key=='registry' else 69
   old=f'fn NCX_{key}_contract(){{let b:[u8;{sz}]=kani::any();let _={fun}(&b);}}'
   body=f'fn NCX_{key}_contract(){{let stage:u8=kani::any();kani::assume(stage<5);if stage==0{{let b:[u8;{size+1}]=kani::any();let _={fun}(&b);}}else{{let mut b:[u8;{size}]=kani::any();b[0]=65;b[1]=83;b[2]={third};b[3]=50;b[4]=3;b[{mode}]=1;match stage{{1=>b[0]=0,2=>b[4]=0,3=>b[{mode}]=0,_=>b[{res}]=1}};let _={fun}(&b);}}}}'
   if case!='reject':
    mutation={'magic':'b[0]=0','version':'b[4]=0','mode':f'b[{mode}]=0','reserved':f'b[{res}]=1'}[case]
    body=f'fn NCX_{key}_contract(){{let mut b:[u8;{size}]=kani::any();b[0]=65;b[1]=83;b[2]={third};b[3]=50;b[4]=3;b[{mode}]=1;{mutation};let _={fun}(&b);}}'
   n=n.replace(old,body)

 for key,name,fun in [('registry','VerifierRegistryV2','validate_verifier_registry_v2'),('entry','VerifierRegistryEntryV2','validate_verifier_registry_entry_v2')]:
  fs=fields[name]
  values=','.join(f+(': match kani::any::<u8>()%4{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}' if f=='status' else ':kani::any()') for f in fs)
  n+=f'#[kani::proof_for_contract(aspis_statement::pool_v1::verifier_registry::{fun})]\n'+attrs+f'#[kani::unwind(34)]\nfn NCX_validate_{key}_contract(){{let r={name}{{{values}}};let _={fun}(&r);}}\n'
 n+='#[kani::proof]\n'+attrs+f'#[kani::unwind(34)]\nfn NCX_copy_control(){{let b:[u8;32]=kani::any();let mut a=[0u8;32];a.copy_from_slice(&b);let j:usize=kani::any();kani::assume(j<32);assert!((a[j]==b[j])!={str(negative).lower()});}}\n'
 for key,name,fun,size in [('registry','VerifierRegistryV2','decode_verifier_registry_v2',256),('entry','VerifierRegistryEntryV2','decode_verifier_registry_entry_v2',320)]:
  prop='!*r' if negative else '*r'
  n+=f'#[kani::requires(b.len()=={size} && field<{len(fields[name])} && j<32)]\n#[kani::modifies()]\n#[kani::ensures(|r:&bool|{prop})]\nfn NCX_{key}_window(b:&[u8],field:usize,j:usize)->bool{{aspis_statement::NCX_native::eq_{key}_coord(&{fun}(b),&aspis_statement::NCX_reference::{fun}(b),field,j)}}\n'
  n+=f'#[kani::proof_for_contract(NCX_{key}_window)]\n'+attrs+f'#[kani::unwind(34)]\nfn NCX_{key}_window_contract(){{let b:[u8;{size}]=kani::any();let f:usize=kani::any();let j:usize=kani::any();kani::assume(f<{len(fields[name])} && j<32);let _=NCX_{key}_window(&b,f,j);}}\n'
 for kind,size,width in [('read',64,32),('word',16,8)]:
  rhs='aspis_statement::NCX_reference::read32(b,p)' if kind=='read' else 'aspis_statement::NCX_reference::word(b,p)'
  expr='a[j]==r[j]' if kind=='read' else 'a==r'
  native='let a:[u8;32]=b[p..p+32].try_into().unwrap();' if kind=='read' else 'let a=u64::from_le_bytes(b[p..p+8].try_into().unwrap());'
  prop='!*r' if negative else '*r'
  n+=f'#[kani::requires(p<={size-width} && j<{width})]\n#[kani::modifies()]\n#[kani::ensures(|r:&bool|{prop})]\nfn NCX_{kind}_window(b:&[u8;{size}],p:usize,j:usize)->bool{{{native}let r={rhs};{expr}}}\n'
  n+=f'#[kani::proof_for_contract(NCX_{kind}_window)]\n'+attrs+f'#[kani::unwind(34)]\nfn NCX_{kind}_window_check(){{let b:[u8;{size}]=kani::any();let p:usize=kani::any();let j:usize=kani::any();kani::assume(p<={size-width} && j<{width});let _=NCX_{kind}_window(&b,p,j);}}\n'
 shape=os.environ.get('NCX_SHAPE','registry')
 ty='VerifierRegistryV2' if shape=='registry' else 'VerifierRegistryEntryV2'
 flag='bump' # common scalar, unmodified but weaker than complete record
 other='programdata_bump'
 control=os.environ.get('NCX_CONTROL','positive')
 prop='matches!(r,Ok(v) if v.bump==a.bump)'
 if control=='ensures':prop='!('+prop+')'
 n+=f'#[kani::modifies(x)]\n#[kani::ensures(|r:&Result<{ty},PoolV1VerifierRegistryFormatError>|{prop})]\nfn NCX_shape(a:{ty},x:&mut u8,y:&mut u8)->Result<{ty},PoolV1VerifierRegistryFormatError>{{*x=1;'+('*y=2;' if control=='modifies' else '')+'Ok(a)}\n'
 n+='#[kani::proof_for_contract(NCX_shape)]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_shape_contract(){let a=kani::any();let mut x=kani::any();let mut y=kani::any();let _=NCX_shape(a,&mut x,&mut y);}\n'
 n+='#[kani::proof]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_shape_real(){let a:'+ty+'=kani::any();let before=a.programdata_bump;let mut x=kani::any();let mut y=kani::any();let r=NCX_shape(a,&mut x,&mut y);assert!(matches!(r,Ok(v) if v.programdata_bump==before));}\n'
 n+='#[kani::proof]\n#[kani::stub_verified(NCX_shape)]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_shape_stub(){let a:'+ty+'=kani::any();let before=a.programdata_bump;let mut x=kani::any();let mut y=kani::any();let r=NCX_shape(a,&mut x,&mut y);assert!(matches!(r,Ok(v) if v.programdata_bump==before));}\n'
 prop='r.is_err()'
 if control=='ensures':prop='!('+prop+')'
 n+=f'#[kani::modifies(x)]\n#[kani::ensures(|r:&Result<(),PoolV1VerifierRegistryFormatError>|{prop})]\nfn NCX_unit(x:&mut u8,y:&mut u8)->Result<(),PoolV1VerifierRegistryFormatError>{{*x=1;'+('*y=2;' if control=='modifies' else '')+'Err(PoolV1VerifierRegistryFormatError::InvalidStatus)}\n'
 n+='#[kani::proof_for_contract(NCX_unit)]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_unit_contract(){let mut x=kani::any();let mut y=kani::any();let _=NCX_unit(&mut x,&mut y);}\n'
 n+='#[kani::proof]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_unit_real(){let mut x=kani::any();let mut y=kani::any();let r=NCX_unit(&mut x,&mut y);assert!(r==Err(PoolV1VerifierRegistryFormatError::InvalidStatus));}\n'
 n+='#[kani::proof]\n#[kani::stub_verified(NCX_unit)]\n'+attrs+'#[kani::unwind(34)]\nfn NCX_unit_stub(){let mut x=kani::any();let mut y=kani::any();let r=NCX_unit(&mut x,&mut y);assert!(r==Err(PoolV1VerifierRegistryFormatError::InvalidStatus));}\n'
 d['programs/r1-cost-probe/src/NCX_native.rs']=n
 return d
if __name__=='__main__':
 out=''
 for p,s in files().items():
  try:old=orig(p)
  except subprocess.CalledProcessError:old=''
  out+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p if old else '/dev/null',tofile='b/'+p))
 (E/'NCX_harness.patch').write_text(out)
