from NJY_forest_segments import helpers,P
from NJY_native import *
import sys
family=sys.argv[2];mode=sys.argv[3];assert family in ['words','step_post','bindings','digest']
shape={'words':('Result<[u64;8],F>','Ok([seed as u64;8])','kani::any::<Result<[u64;8],F>>()','out.is_ok()','match out{Ok(p)=>assert!(p[0]==seed as u64,"unimplied word"),Err(e)=>assert!(e==F::WrongMagic,"unimplied error")}'),
 'step_post':('(Result<(),F>,[u64;8])','(Ok(()),[seed as u64;8])','(kani::any::<Result<(),F>>(),kani::any::<[u64;8]>())','out.0.is_ok()','assert!(out.1[0]==seed as u64,"unimplied post word")'),
 'bindings':('Result<([u8;32],[u8;32]),F>','Ok(([seed;32],[0;32]))','kani::any::<Result<([u8;32],[u8;32]),F>>()','out.is_ok()','match out{Ok(p)=>assert!(p.0[0]==seed,"unimplied binding"),Err(e)=>assert!(e==F::WrongMagic,"unimplied error")}'),
 'digest':('Result<[aspis_core::field::M31;8],F>','Ok([aspis_core::field::M31(seed as u32);8])','if kani::any::<bool>(){Ok(digest())}else{Err(kani::any::<F>())}','out.is_ok()','match out{Ok(p)=>assert!(p[0].0==seed as u32,"unimplied digest"),Err(e)=>assert!(e==F::WrongMagic,"unimplied error")}')}[family]
ret,ctor,anyresult,tag,check=shape
text='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+helpers
text+='impl kani::Arbitrary for F{fn any()->Self{match account_reply(){Ok(())=>F::WrongLength,Err(e)=>e}}}\n'
error='(Err(F::WrongMagic),[seed as u64;8])' if family=='step_post' else 'Err(F::WrongMagic)'
text+='''#[kani::ensures(|out| (TAG==(seed&1==0))!=cfg!(NJY_invert))]
#[kani::modifies()]
fn shape_probe(seed:u8,scratch:&mut u8)->RET{if WRITE{*scratch=seed;}if seed&1==0{CTOR}else{ERROR}}
fn check(seed:u8,out:RET){CHECK}
#[kani::proof_for_contract(shape_probe)]
#[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_contract(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
#[kani::proof]
#[kani::stub_verified(shape_probe)]
#[kani::unwind(193)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn shape_unimplied(){let seed:u8=kani::any();let mut scratch:u8=kani::any();let out=shape_probe(seed,&mut scratch);check(seed,out);}
'''.replace('TAG',tag).replace('RET',ret).replace('CTOR',ctor).replace('ERROR',error).replace('CHECK',check).replace('WRITE','true' if mode=='modifies' else 'false')
module='NJY_'+family+'_shape';(E/(module+'_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/'+str(Path(P).parent/(module+'.rs'))+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines()))
submit(sys.argv[1],'pool_v1::pair_forest_accounts::'+module+'::'+('shape_unimplied' if mode=='unimplied' else 'shape_contract'),P,module,text,mode,extra_sidecars=[('crates/aspis-core/src/field.rs','NJY_m31_arbitrary','impl kani::Arbitrary for super::M31 {fn any()->Self{super::M31(kani::any())}}\n')] if family=='digest' else None)
