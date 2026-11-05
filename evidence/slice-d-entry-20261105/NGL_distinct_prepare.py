from NGL_prepare import E,P,update
import json,subprocess,hashlib
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_owned.rs'];s+='''
struct NGL_KeyLog{count:usize,left:*const Pubkey,right:*const Pubkey,left_bytes:[u8;32],right_bytes:[u8;32]}
fn distinct_step<const N:usize>(accounts:&[&OwnedAccount;N],index:usize,mut previous:usize,log:&mut NGL_KeyLog)->(ProgramResult,usize){
 if previous<index{
  let left=accounts[previous].key();let right=accounts[index].key();
  log.count=2;log.left=left as *const Pubkey;log.right=right as *const Pubkey;log.left_bytes=left.to_bytes();log.right_bytes=right.to_bytes();
  if left==right{return(Err(ProgramError::InvalidArgument),previous);}
  previous+=1;
 }
 (Ok(()),previous)
}
#[kani::requires(index<3&&previous<=index)] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn distinct_record3(a:&[OwnedAccount;3],index:usize,previous:usize)->bool{
 let refs=core::array::from_fn::<_,3,_>(|i|&a[i]);let mut log=NGL_KeyLog{count:0,left:core::ptr::null(),right:core::ptr::null(),left_bytes:[0;32],right_bytes:[0;32]};let(r,next)=distinct_step(&refs,index,previous,&mut log);
 if cfg!(NGL_invert){log.left=log.left.wrapping_add(1);}
 let equal=previous<index&&a[previous].key==a[index].key;let exact=if equal{matches!(r,Err(ProgramError::InvalidArgument))&&next==previous}else{matches!(r,Ok(()))&&next==if previous<index{previous+1}else{previous}};
 let calls=if previous<index{log.count==2&&log.left==&a[previous].key as *const Pubkey&&log.right==&a[index].key as *const Pubkey&&log.left_bytes==a[previous].key.to_bytes()&&log.right_bytes==a[index].key.to_bytes()}else{log.count==0&&log.left.is_null()&&log.right.is_null()};exact&&calls
}
#[kani::proof_for_contract(distinct_record3)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn distinct3_contract(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,3,_>(|_|account()));let index:usize=kani::any();let previous:usize=kani::any();kani::assume(index<3&&previous<=index);let _=distinct_record3(&a,index,previous);}
'''
# Same native step, separate compile-time caller arity; not a verdict-driven rename.
part=s[s.index('#[kani::requires(index<3&&previous<=index)]'):]
part=part.replace('distinct_record3','distinct_record7').replace('distinct3_contract','distinct7_contract').replace('index<3','index<7').replace('[OwnedAccount;3]','[OwnedAccount;7]').replace('::<_,3,_>','::<_,7,_>')
s+='\n'+part
update({P+'NGL_owned.rs':s},'distinct_one_iteration')
raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P+'r1_pool_adapter_owned.rs'],text=True)
fragment='''            if accounts[previous].key() == accounts[index].key() {
                return Err(ProgramError::InvalidArgument);
            }
            previous += 1;'''
assert raw.count(fragment)==1
start=raw.index(fragment);(E/'NGL_DISTINCT_SOURCE.json').write_text(json.dumps(dict(frozen_source=P+'r1_pool_adapter_owned.rs',byte_range=[start,start+len(fragment)],sha256=hashlib.sha256(fragment.encode()).hexdigest(),frozen_fragment=fragment,native_cut='distinct_step',erasure='factor the two getter results in original left-to-right order; remove local log writes; remove the observational return-counter tuple; while guard becomes one if on arbitrary invariant prestate',invariant='N=3 or7; index<N; previous<=index; all typed account borrows valid; accounts immutable',no_whole_loop=True),indent=1)+'\n')
