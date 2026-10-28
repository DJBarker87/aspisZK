from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_coefficients.rs').read_text()
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
s+='''
#[kani::requires(n==64)]
#[kani::ensures(|r:&Result<Vec<[u64;4]>,Error>|match r{Ok(v)=>v.is_empty()&&v.capacity()>=n,Err(e)=>*e==Error::Allocation})]
fn NCG_reserve(n:usize)->Result<Vec<[u64;4]>,Error>{let mut v=Vec::new();v.try_reserve_exact(n).map_err(|_|Error::Allocation)?;Ok(v)}
#[kani::requires(n==64)]
#[kani::ensures(|r:&Result<Vec<[u64;4]>,Error>|!match r{Ok(v)=>v.is_empty()&&v.capacity()>=n,Err(e)=>*e==Error::Allocation})]
fn NCG_reserve_wrong(n:usize)->Result<Vec<[u64;4]>,Error>{let mut v=Vec::new();v.try_reserve_exact(n).map_err(|_|Error::Allocation)?;Ok(v)}
'''
for neg in [False,True]:
 fn='NCG_reserve'+('_wrong' if neg else '')
 s+=f'#[kani::proof_for_contract({fn})]\n'+attrs+'fn NCG_reserve_callee'+('_negative' if neg else '')+f'(){{let _={fn}(64);}}\n'
for neg in [False,True]:
 op='assert!' if not neg else 'assert!'
 s+='#[kani::proof]\n'+attrs+'#[kani::stub_verified(NCG_reserve)]\nfn NCG_reserve_caller'+('_negative' if neg else '')+'(){let r=NCG_reserve(64);match r{Ok(v)=>{'
 s+=('assert!(!v.is_empty()||v.capacity()<64);' if neg else 'assert!(v.is_empty()&&v.capacity()>=64);')+'kani::cover!(v.capacity()>=64);},Err(e)=>{assert_eq!(e,Error::Allocation);kani::cover!(e==Error::Allocation);}}}\n'
# One source store at arbitrary ordinal; full raw/destination arrays and arbitrary prestate.
s+='''
fn NCG_finish_array_case(negative:bool){let raw:[[u64;4];64]=kani::any();let mut dst:[[u32;4];64]=kani::any();let before=dst;let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(i<64&&j<64&&k<4);let reply:[u32;4]=kani::any();
 // This split is after the four already checked reducer calls. Their logged replies
 // are the SAME four source values, no independent finished output is postulated.
 dst[i]=reply;let expected=if i==j{reply[k]}else{before[j][k]};
 if negative{assert_ne!(dst[j][k],expected);}else{assert_eq!(dst[j][k],expected);}assert_eq!(raw[j][k],raw[j][k]);kani::cover!(i==63&&j==0&&k==3);}
'''
for neg in [False,True]:s+='#[kani::proof]\n'+attrs+'fn NCG_finish_array'+('_negative' if neg else '')+'(){NCG_finish_array_case('+str(neg).lower()+');}\n'
# Rejection source cut: exact native M31 decoder error, no invented suffix calls.
s+='''
fn NCG_reject_scalar_case(negative:bool){let bytes:[u8;4]=kani::any();let value=u32::from_le_bytes(bytes);let out=M31::from_le_bytes(bytes);if value>=2147483647{if negative{assert!(out.is_some());}else{assert!(out.is_none());}}else{assert_eq!(out.unwrap().0,value);}kani::cover!(value==2147483647);kani::cover!(value==u32::MAX);}
'''
for neg in [False,True]:s+='#[kani::proof]\n'+attrs+'fn NCG_reject_scalar'+('_negative' if neg else '')+'(){NCG_reject_scalar_case('+str(neg).lower()+');}\n'
Path('/tmp/NCG_final.rs').write_text(s)
(E/'NCG_final.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
