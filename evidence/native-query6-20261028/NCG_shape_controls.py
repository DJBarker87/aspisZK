from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_fold_logs.rs').read_text()
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
s+='''
#[kani::ensures(|r:&Option<M31>| matches!(r,Some(v) if v.0==x))]
fn NCG_option_identity(x:u32)->Option<M31>{Some(M31(x))}
#[kani::ensures(|r:&Option<M31>| !matches!(r,Some(v) if v.0==x))]
fn NCG_option_inverted(x:u32)->Option<M31>{Some(M31(x))}
#[kani::ensures(|_r:&Option<M31>|true)]
fn NCG_option_weak(x:u32)->Option<M31>{Some(M31(x))}
#[kani::modifies(a)]
#[kani::ensures(|_r:&Option<M31>|true)]
fn NCG_option_modifies(a:&mut u32,b:&mut u32)->Option<M31>{*a=1;*b=2;Some(M31(0))}
#[kani::requires(!x.is_empty())]
#[kani::ensures(|r:&&[u32]| r.len()==x.len() && r.as_ptr()==x.as_ptr())]
fn NCG_slice_identity(x:&[u32])->&[u32]{x}
#[kani::requires(!x.is_empty())]
#[kani::ensures(|r:&&[u32]| r.len()!=x.len())]
fn NCG_slice_inverted(x:&[u32])->&[u32]{x}
#[kani::requires(!x.is_empty())]
#[kani::ensures(|_r:&&[u32]|true)]
fn NCG_slice_weak(x:&[u32])->&[u32]{x}
#[kani::modifies(a)]
#[kani::ensures(|_r:&&[u32]|true)]
fn NCG_slice_modifies<'a>(a:&mut u32,b:&mut u32,x:&'a[u32])->&'a[u32]{*a=1;*b=2;x}
#[kani::ensures(|r:&Result<Vec<[u64;4]>,Error>| matches!(r,Ok(v) if v.is_empty()))]
fn NCG_vec_identity()->Result<Vec<[u64;4]>,Error>{Ok(Vec::new())}
#[kani::ensures(|r:&Result<Vec<[u64;4]>,Error>| !matches!(r,Ok(v) if v.is_empty()))]
fn NCG_vec_inverted()->Result<Vec<[u64;4]>,Error>{Ok(Vec::new())}
#[kani::ensures(|_r:&Result<Vec<[u64;4]>,Error>|true)]
fn NCG_vec_weak()->Result<Vec<[u64;4]>,Error>{Ok(Vec::new())}
#[kani::modifies(a)]
#[kani::ensures(|_r:&Result<Vec<[u64;4]>,Error>|true)]
fn NCG_vec_modifies(a:&mut u32,b:&mut u32)->Result<Vec<[u64;4]>,Error>{*a=1;*b=2;Ok(Vec::new())}
'''
for typ,setup,call,expect in [
 ('option','let x:u32=kani::any();','x','Some(M31(x))'),
 ('slice','let x:[u32;5]=kani::any();','&x','&x[..]'),
 ('vec','','','Ok(Vec::new())')]:
 fn=f'NCG_{typ}'
 for case,contract,assertion in [
 ('contract','identity',''),('wrong','inverted',''),('weak_contract','weak','')]:
  s+=f'#[kani::proof_for_contract({fn}_{contract})]\n'+attrs+f'fn {fn}_{case}(){{{setup}let _={fn}_{contract}({call});}}\n'
 for case,stub,body,negative in [('real',False,'weak',False),('unimplied',True,'weak',False),('install',True,'identity',False),('install_negative',True,'identity',True)]:
  s+='#[kani::proof]\n'+attrs+(f'#[kani::stub_verified({fn}_{body})]\n' if stub else '')
  op='assert_ne!' if negative else 'assert_eq!'
  # slice comparison equality asserts bytes; deliberately unimplied by weak contract
  s+=f'fn {fn}_{case}(){{{setup}{op}({fn}_{body}({call}),{expect});}}\n'
 s+=f'#[kani::proof_for_contract({fn}_modifies)]\n'+attrs+f'fn {fn}_frame_wrong(){{let mut a:u32=kani::any();let mut b:u32=kani::any();'+('let x:[u32;5]=kani::any();' if typ=='slice' else '')+f'let _={fn}_modifies(&mut a,&mut b'+(',&x' if typ=='slice' else '')+');}\n'
Path('/tmp/NCG_shapes.rs').write_text(s)
(E/'NCG_shapes.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
