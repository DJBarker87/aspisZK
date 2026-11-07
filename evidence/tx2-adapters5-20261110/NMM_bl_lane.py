from NMM_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
COMMON='''use super::*;
use core::cell::UnsafeCell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// One real local allocation. Every log region is disjoint from shared bytes.
#[repr(C,align(4))]
struct NMM_Input { bytes:[u8;768], args:UnsafeCell<[u8;768]>, replies:UnsafeCell<[u32;192]>, flags:UnsafeCell<[u8;768]> }
fn NMM_error(tag:u8)->aspis_statement::AtomicStatementError {
 use aspis_statement::AtomicStatementError::*;
 match tag {1=>NonCanonicalDigest,2=>NonCanonicalAssetId,3=>FeeOutOfRange,4=>PathDepthMismatch,5=>InsertionIndexOutOfRange,6=>CurrentAnchorMismatch,_=>OutputAnchorMismatch}
}
fn NMM_digest_cut(bytes:&[u8;32])->Result<[M31;8],aspis_statement::AtomicStatementError>{
 let raw:[u32;8]=kani::any();let tag:u8=kani::any();kani::assume(tag<8);
 unsafe {
  let p=bytes.as_ptr();
  let args=p.add(768) as *const UnsafeCell<[u8;32]>;
  let reply=p.add(1536) as *const UnsafeCell<[u32;8]>;
  let flag=p.add(2304) as *const UnsafeCell<u8>;
  (*args).get().write(*bytes);
  (*reply).get().write(raw);
  assert!(*(*flag).get()==0,"child input window called once");
  (*flag).get().write(tag+1);
 }
 if tag==0 {Ok(raw.map(M31))}else{Err(NMM_error(tag))}
}
fn NMM_replay(log:&NMM_Input,bytes:&[u8;32])->Result<[M31;8],aspis_statement::AtomicStatementError>{
 let offset=unsafe{bytes.as_ptr().offset_from(log.bytes.as_ptr())};
 assert!(offset>=0 && offset<=736 && offset%32==0,"transcription call window");
 let k=offset as usize;
 unsafe {
  let tag=(*log.flags.get())[k];
  assert!(tag>0 && tag<=8,"recorded call present");
  kani::assume(tag>0 && tag<=8);
  (*log.flags.get())[k]=0;
  for j in 0..32 {assert!((*log.args.get())[k+j]==bytes[j],"exact recorded callee argument");}
  let mut raw=[0u32;8];for j in 0..8 {raw[j]=(*log.replies.get())[k/4+j];}
  if tag==1 {Ok(raw.map(M31))}else{Err(NMM_error(tag-1))}
 }
}
fn NMM_same(a:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>,b:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>)->bool{
 match(a,b){(Err(x),Err(y))=>x==y,(Ok(x),Ok(y))=>x.bump==y.bump&&x.master==y.master&&x.lane_id==y.lane_id&&x.tree.next_leaf_index==y.tree.next_leaf_index&&x.tree.root==y.tree.root&&x.tree.frontier==y.tree.frontier,_=>false}
}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(aspis_statement::atomic_statement::decode_digest_canonical,NMM_digest_cut)]
'''
def attempt(a,branch,mode,solver=None):
 direct=branch.startswith("direct_");branch=branch.removeprefix("direct_")
 outcome="all"
 for label in ["err","ok"]:
  if branch.startswith(label+"_"):outcome=label;branch=branch[len(label)+1:]
 child_ok=branch.startswith("allok_");branch=branch.removeprefix("allok_")
 pointer=branch.endswith("_ptr");branch=branch.removesuffix("_ptr");scalar=branch.endswith("_word");branch=branch.removesuffix("_word")
 ref=(E/'NMM_FROZEN_217.rs').read_text().replace('fn decode_lane_from_pool_release(', 'fn NMM_reference(log:&NMM_Input,',1).replace('decode_digest_canonical(', 'NMM_replay(log,')
 text=COMMON+ref+ANN+'''fn stage(){
 let input=NMM_Input{bytes:kani::any(),args:UnsafeCell::new([0;768]),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768])};
 let observer:usize=kani::any();kani::assume(observer<768);
 let before=input.bytes[observer];
 kani::assume(DOMAIN);
 let native=decode_lane_from_pool_release(&input.bytes);
 let reference=NMM_reference(&input,&input.bytes);
 assert!(NMM_same(&native,&reference),"complete outcome from recorded replies");
 assert!(input.bytes[observer]==before,"immutable input frame");
 let remaining=unsafe{(*input.flags.get())[observer]};
 assert!(remaining==0 || remaining>=16,"no unmatched child argument record");
}
'''
 domains={'whole':'true','header':'input.bytes[..4]!=POOL_V1_PAIR_FOREST_LANE_MAGIC','body':'input.bytes[..4]==POOL_V1_PAIR_FOREST_LANE_MAGIC'}
 if branch=='success':
  domains[branch]='true'
  head=(E/'NMM_FROZEN_217.rs').read_text().split('    let root =',1)[0]
  head=head[head.index('{')+1:]
  prefix='struct NMM_Header{bump:u8,master:[u8;32],lane:u8,next:u64}\nfn NMM_prefix(bytes:&[u8])->Result<NMM_Header,ProgramError>{'+head+'Ok(NMM_Header{bump:bytes[72],master,lane:bytes[5],next:next_leaf_index})}\n'
  end=text.rfind('fn stage(){');text=text[:end]+"""fn stage(){
 let input=NMM_Input{bytes:kani::any(),args:UnsafeCell::new([0;768]),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768])};
 let observer:usize=kani::any();kani::assume(observer<768);let before=input.bytes[observer];
 let level:usize=kani::any();kani::assume(level<20);let word:usize=kani::any();kani::assume(word<8);let byte=observer%32;
 let native=decode_lane_from_pool_release(&input.bytes);
 if let Ok(value)=native {
  let prefix=NMM_prefix(&input.bytes);assert!(prefix.is_ok(),\"success establishes complete header prefix\");
  if let Ok(h)=prefix {
   let offset=128+32*level;
   let root=unsafe{(*input.replies.get())[24+word]};let frontier=unsafe{(*input.replies.get())[offset/4+word]};
   assert!(unsafe{(*input.flags.get())[96]==1&&(*input.flags.get())[offset]==1},\"success uses Ok replies at exact occurrences\");
   let rootptr=unsafe{input.args.get().cast::<u8>().add(96).cast::<*const u8>().read()};let nodeptr=unsafe{input.args.get().cast::<u8>().add(offset).cast::<*const u8>().read()};
   assert!(rootptr==unsafe{input.bytes.as_ptr().add(96)}&&nodeptr==unsafe{input.bytes.as_ptr().add(offset)},\"success exact digest argument windows\");
   assert!(value.bump==h.bump&&value.master[byte]==h.master[byte]&&value.lane_id==h.lane&&value.tree.next_leaf_index==h.next,\"success metadata fields equal transcription\");
   assert!(value.tree.root[word].0==root&&value.tree.frontier[level][word].0==frontier,\"complete payload word equals recorded reply\");
   if (h.next>>level)&1==0 {assert!(frontier==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level][word].0,\"success establishes source frontier guard\");}
   if h.next==0 {assert!(root==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[20][word].0,\"success establishes source terminal root guard\");}
  }
 }
 assert!(input.bytes[observer]==before,\"immutable input frame\");
}
"""
  text=text.replace('#[kani::proof] #[kani::unwind(35)]',prefix+'#[kani::proof] #[kani::unwind(35)]')
 if branch=='coverage':
  domains[branch]='true'
  text=text[:text.rfind('fn stage(){')]+"""fn stage(){
 let input=NMM_Input{bytes:kani::any(),args:UnsafeCell::new([0;768]),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768])};
 let observer:usize=kani::any();kani::assume(observer<768);let before=input.bytes[observer];
 let native=decode_lane_from_pool_release(&input.bytes);
 if native.is_ok(){
  let legal=observer>=96&&observer<=736&&(observer-96)%32==0;
  let tag=unsafe{(*input.flags.get())[observer]};
  assert!(tag==if legal{1}else{0},"success has exactly21 returning Ok child occurrences");
  if legal {let ptr=unsafe{input.args.get().cast::<u8>().add(observer).cast::<*const u8>().read()};assert!(ptr==unsafe{input.bytes.as_ptr().add(observer)},"success occurrence argument pointer");}
 }
 assert!(input.bytes[observer]==before,"immutable input frame");
}
"""
 if branch=='allok' or child_ok:
  domains[branch]='true'
  text=text.replace('let raw:[u32;8]=kani::any();let tag:u8=kani::any();kani::assume(tag<8);','let raw:[u32;8]=kani::any();let tag=0u8;')
  text=text.replace('if tag==0 {Ok(raw.map(M31))}else{Err(NMM_error(tag))}','Ok(raw.map(M31))')
  text=text.replace('if tag==1 {Ok(raw.map(M31))}else{Err(NMM_error(tag-1))}','Ok(raw.map(M31))')
 if branch=='observed':
  domains[branch]='true'
  text=text.replace('fn NMM_reference(log:&NMM_Input,\n    bytes: &[u8],\n) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError>', 'fn NMM_reference(log:&NMM_Input,\n    bytes: &[u8],\n) -> Result<PoolV1PairForestLaneStateV1, ProgramError>')
  text=text.replace('Ok(Box::new(PoolV1PairForestLaneStateV1 {','Ok(PoolV1PairForestLaneStateV1 {')
  text=text.replace('        },\n    }))','        },\n    })')
  text=text.replace('b:&Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>)->bool','b:&Result<PoolV1PairForestLaneStateV1,ProgramError>,level:usize)->bool')
  text=text.replace('x.tree.frontier==y.tree.frontier','x.tree.frontier[level]==y.tree.frontier[level]')
  text=text.replace('let before=input.bytes[observer];','let before=input.bytes[observer];let level:usize=kani::any();kani::assume(level<20);')
  text=text.replace('NMM_same(&native,&reference)','NMM_same(&native,&reference,level)')
 if branch=='rooterr':
  domains[branch]='true'
  text=text.replace('kani::assume(tag<8);','kani::assume(tag>0 && tag<8);')
  text=text.replace('if tag==0 {Ok(raw.map(M31))}else{Err(NMM_error(tag))}','Err(NMM_error(tag))')
  text=text.replace('if tag==1 {Ok(raw.map(M31))}else{Err(NMM_error(tag-1))}','Err(NMM_error(tag-1))')
 if branch=='headercut':
  domains[branch]=domains['header']
  start=text.index('fn NMM_digest_cut(');end=text.index('fn NMM_replay(',start)
  text=text[:start]+"fn NMM_digest_cut(_: &[u8;32])->Result<[M31;8],aspis_statement::AtomicStatementError>{panic!(\"unreachable child on header branch\")}\n"+text[end:]
  start=text.index('fn NMM_reference(');end=text.index('#[kani::proof]',start)
  text=text[:start]+"fn NMM_reference(_: &NMM_Input,_: &[u8])->Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>{Err(ProgramError::InvalidAccountData)}\n"+text[end:]
 if branch.startswith('stop'):

  k=int(branch[4:]);assert 0<=k<=20
  domains[branch]='true'
  text=text.replace('flags:UnsafeCell::new([0;768])','flags:UnsafeCell::new({let mut flags=[16;768];flags['+str(96+32*k)+']=17;flags})')
  text=text.replace('kani::assume(tag<8);','kani::assume(tag<8);let command=unsafe{*((bytes.as_ptr().add(2304) as *const UnsafeCell<u8>).as_ref().unwrap().get())};let tag=if command==17 {tag%7+1}else{tag};')
  text=text.replace('assert!(*(*flag).get()==0,','assert!(*(*flag).get()>=16,')
  text=text.replace('if tag==0 {Ok(raw.map(M31))}else{Err(NMM_error(tag))}','if command==17 {Err(NMM_error(tag))}else if tag==0 {Ok(raw.map(M31))}else{Err(NMM_error(tag))}')
 if scalar:
  assert branch=='observed'
  text=text.replace(',level:usize)->bool',',level:usize,word:usize,byte:usize)->bool')
  text=text.replace('x.master==y.master','x.master[byte]==y.master[byte]')
  text=text.replace('x.tree.root==y.tree.root','x.tree.root[word].0==y.tree.root[word].0')
  text=text.replace('x.tree.frontier[level]==y.tree.frontier[level]','x.tree.frontier[level][word].0==y.tree.frontier[level][word].0')
  text=text.replace('kani::assume(level<20);','kani::assume(level<20);let word:usize=kani::any();kani::assume(word<8);')
  text=text.replace('NMM_same(&native,&reference,level)','NMM_same(&native,&reference,level,word,observer%32)')
 if direct:
  assert branch=='observed' and scalar
  prefix=(E/'NMM_FROZEN_217.rs').read_text().split('    let mut frontier =',1)[0]
  prefix=prefix[prefix.index('{')+1:].replace('decode_digest_canonical(','NMM_replay(log,')
  projected="""struct NMM_Window{bump:u8,master:u8,lane:u8,next:u64,root:u32,frontier:u32}
fn NMM_reference(log:&NMM_Input,selected:usize,word:usize,byte:usize,bytes:&[u8])->Result<NMM_Window,ProgramError>{
"""+prefix+"""
 let mut frontier_word=0u32;
 for level in 0..POOL_V1_PAIR_TREE_DEPTH {
  let start=48+32*level;
  let node=NMM_replay(log,tree[start..start+32].try_into().map_err(|_|ProgramError::InvalidAccountData)?).map_err(|_|ProgramError::InvalidAccountData)?;
  if (next_leaf_index>>level)&1==0 && node!=V7_PAIR_EMPTY_ROOTS[level]{return Err(ProgramError::InvalidAccountData);}
  if level==selected {frontier_word=node[word].0;}
 }
 if next_leaf_index==0 && root!=V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]{return Err(ProgramError::InvalidAccountData);}
 Ok(NMM_Window{bump:bytes[72],master:master[byte],lane:bytes[5],next:next_leaf_index,root:root[word].0,frontier:frontier_word})
}
"""
  start=text.index('fn NMM_reference(');end=text.index('#[kani::proof]',start);text=text[:start]+projected+text[end:]
  text=text.replace('b:&Result<PoolV1PairForestLaneStateV1,ProgramError>','b:&Result<NMM_Window,ProgramError>')
  text=text.replace('x.master[byte]==y.master[byte]','x.master[byte]==y.master').replace('x.lane_id==y.lane_id','x.lane_id==y.lane').replace('x.tree.next_leaf_index==y.tree.next_leaf_index','x.tree.next_leaf_index==y.next').replace('x.tree.root[word].0==y.tree.root[word].0','x.tree.root[word].0==y.root').replace('x.tree.frontier[level][word].0==y.tree.frontier[level][word].0','x.tree.frontier[level][word].0==y.frontier')
  text=text.replace('NMM_reference(&input,&input.bytes)','NMM_reference(&input,level,word,observer%32,&input.bytes)')
 text=text.replace('raw.map(M31)','['+','.join('M31(raw['+str(i)+'])' for i in range(8))+']')
 text=text.replace('DOMAIN',domains[branch]);edits=None
 if outcome!='all':
  text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let native=decode_lane_from_pool_release(&input.bytes);kani::assume(native.is_'+outcome+'());')
 if outcome=='err':
  text=text.replace('x.bump==y.bump&&x.master[byte]==y.master[byte]&&x.lane_id==y.lane_id&&x.tree.next_leaf_index==y.tree.next_leaf_index&&x.tree.root[word].0==y.tree.root[word].0&&x.tree.frontier[level][word].0==y.tree.frontier[level][word].0','false')

 if pointer:
  text=text.replace('#[repr(C,align(4))]','#[repr(C,align(8))]')
  text=text.replace('(*args).get().write(*bytes);','(*args).get().cast::<*const u8>().write(bytes.as_ptr());')
  text=text.replace('for j in 0..32 {assert!((*log.args.get())[k+j]==bytes[j],"exact recorded callee argument");}','let ptr=log.args.get().cast::<u8>().add(k).cast::<*const u8>().read();assert!(ptr==bytes.as_ptr(),"exact recorded callee argument pointer");')

 if branch=='success':
  if mode=='reply':text=text.replace('let root=unsafe{(*input.replies.get())[24+word]};','let root=unsafe{(*input.replies.get())[24+word]}^1;')
  if mode=='argument':text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let other=NMM_Input{bytes:input.bytes,args:UnsafeCell::new([0;768]),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768])};let native=decode_lane_from_pool_release(&other.bytes);')
  if mode=='footprint':text=text.replace('(*reply).get().write(raw);','for j in 0..7 {(*(*reply).get())[j]=raw[j];}')
  if mode=='copy':text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let native=decode_lane_from_pool_release(&input.bytes);let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,"copy negative");')
 if branch=='coverage':
  if mode=='reply':text=text.replace('let tag=unsafe{(*input.flags.get())[observer]};','let tag=0;')
  if mode=='argument':
   text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let other=NMM_Input{bytes:input.bytes,args:UnsafeCell::new([0;768]),replies:UnsafeCell::new([0;192]),flags:UnsafeCell::new([0;768])};let native=decode_lane_from_pool_release(&other.bytes);')
  if mode=='footprint':text=text.replace('(*flag).get().write(tag+1);','(*flag).get().write(0);')
  if mode=='copy':text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','let native=decode_lane_from_pool_release(&input.bytes);let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,"copy negative");')
 if mode=='reply' and (branch=='allok' or outcome=='ok' or child_ok):
  text=text.replace('raw[j]=(*log.replies.get())[k/4+j]','raw[j]=if j==0 {0}else{(*log.replies.get())[k/4+j]}')
 if mode=='reply' and branch not in ['success','allok'] and outcome!='ok' and not child_ok:
  value='PoolV1PairForestLaneStateV1{bump:0,master:[0;32],lane_id:0,tree:IncrementalMerkleTreeV1{next_leaf_index:0,root:[M31::ZERO;8],frontier:[[M31::ZERO;8];20]}}'
  if branch!='observed':value='Box::new('+value+')'
  text=text.replace('let reference=NMM_reference(&input,&input.bytes);','let ignored_error=unsafe{(*input.flags.get())[96]>1 && (*input.flags.get())[96]<16};let reference=NMM_reference(&input,&input.bytes);let reference=if ignored_error {Ok('+value+')}else{reference};')
 if mode=='argument' and branch not in ['coverage','success']:
  if outcome=='ok':
   text=text.replace('let input=NMM_Input','let mut input=NMM_Input')
   text=text.replace('let native=decode_lane_from_pool_release(&input.bytes);','input.bytes[72]^=1;let native=decode_lane_from_pool_release(&input.bytes);input.bytes[72]^=1;')
  else:text=text.replace('decode_lane_from_pool_release(&input.bytes)','decode_lane_from_pool_release(&input.bytes[1..])')
 if mode=='footprint' and branch not in ['coverage','success']:
  if pointer:
   if outcome=='err':text=text.replace('(*args).get().cast::<*const u8>().write(bytes.as_ptr());','(*args).get().cast::<*const u8>().write(core::ptr::null());')
   else:text=text.replace('(*reply).get().write(raw);','for j in 0..7 {(*(*reply).get())[j]=raw[j];}')
  else:text=text.replace('(*args).get().write(*bytes);','for j in 0..31 {(*(*args).get())[j]=bytes[j];}')
 if mode=='result':text=text.replace('fn NMM_same(a:', 'fn NMM_same(a:').replace('(Err(x),Err(y))=>x==y','(Err(x),Err(y))=>x!=y')
 if mode=='copy' and branch not in ['coverage','success']:
  old='assert!(NMM_same(&native,&reference'+(',level,word,observer%32' if scalar else ',level' if branch=='observed' else '')+'),'
  assert old in text
  text=text.replace(old,'let src:[u32;8]=kani::any();let mut dst=[0u32;8];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),8)};assert!(dst!=src,')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/NMM_bl_lane.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::NMM_bl_lane::stage',P,'NMM_bl_lane',text,mode,solver=solver)
if __name__=='__main__':
 import sys
 r=attempt(*sys.argv[1:]);sys.exit(r['exit_status'])
