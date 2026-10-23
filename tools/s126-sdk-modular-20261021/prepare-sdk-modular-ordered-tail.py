#!/usr/bin/env python3
"""Exact ordered post-first tail candidate, composed from checked typed leaves.
No SDK/guard carrier replacement. Explicit typed drop_in_place/Drop calls follow
reply, proof guard, statement, public guard, checkpoint guard order. Their
replacement of compiler-inserted cleanup and frozen dealloc dispatch still need
source/runtime equivalence; this is not an adoption or whole S2 claim.
"""
from pathlib import Path
import subprocess,json,hashlib,sys,tempfile
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists();T=R/'tools/s126-sdk-modular-20261021'
subprocess.run(['python3',str(T/'prepare-sdk-native-finish-drop-chain.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('#[kani::requires(std::mem::size_of_val(&proof)');b=s.index('#[kani::proof_for_contract(native_finish_drop_chain)]',a)
contract_end=b
contract=s[a:b];heads=contract[:contract.index('fn native_finish_drop_chain(')]
# Preserve old guard preconditions/frame and strengthen the return/observed-byte contract.
heads=heads.replace('#[kani::modifies(destination,', '#[kani::requires(observed<1768)]\n#[kani::requires(expected_byte==match &reply {Ok(v) if v.len()==1768=>v[observed],_=>checkpoint[observed]})]\n#[kani::requires(expected_status==match &reply {Ok(v) if v.len()==1768=>0,Ok(_)=>1,Err(_)=>2})]\n#[kani::modifies(destination,')
heads += '''#[kani::ensures(|result:&Result<(),ProgramError>| matches!(result,Ok(()))==(expected_status==0) && matches!(result,Err(ProgramError::InvalidAccountData))==(expected_status==1) && matches!(result,Err(ProgramError::InvalidInstructionData))==(expected_status==2))]
#[kani::ensures(|_|unsafe{(*destination)[observed]}==expected_byte)]
'''
helpers='';guard_harnesses=''
for mode in ['shared','exclusive']:
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';subprocess.run(['python3',str(T/'prepare-sdk-drop-frame.py'),str(out),mode],check=True)
  leaf=(out/'src/lib.rs').read_text();a=leaf.index('#[cfg(kani)]\n#[kani::requires(std::mem::size_of_val');b=leaf.index('#[cfg(kani)] mod proofs',a)
  helpers+=leaf[a:b].replace('finish_guard(',f'finish_guard_{mode}(')+'\n'
  guard_harnesses+=leaf[b:].replace('mod proofs {',f'mod guard_{mode}_certificate {{',1).replace('finish_guard',f'finish_guard_{mode}')+'\n'
helpers+='''#[kani::modifies()]
fn destroy_owner(statement:*mut Box<PoolV1PairForestTerminalStatementV1>,bytes:*mut Vec<u8>,statement_only:bool){
 unsafe{if statement_only {std::ptr::drop_in_place(statement);}else{std::ptr::drop_in_place(bytes);}}
}
unsafe fn frozen_release_dealloc(pointer:*mut u8,layout:std::alloc::Layout){
 let allocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
 unsafe{std::alloc::GlobalAlloc::dealloc(&allocator,pointer,layout);}
}
'''
body='''fn native_finish_drop_chain(proof:std::cell::Ref<'_,&mut[u8]>,public:std::cell::Ref<'_,&mut[u8]>,mut checkpoint:std::cell::RefMut<'_,&mut[u8]>,counters:[*const Cell<isize>;3],statement:Box<PoolV1PairForestTerminalStatementV1>,candidate:[u8;688],reply:Result<Vec<u8>,ProgramError>,destination:*mut[u8;1768],observed:usize,expected_byte:u8,expected_status:u8)->Result<(),ProgramError>{
 let mut statement=std::mem::ManuallyDrop::new(statement);
 let result=match reply {
  Ok(bytes)=>{
   let mut bytes=std::mem::ManuallyDrop::new(bytes);
   let source=bytes.as_ptr().cast::<[u8;1768]>();
   let copied=encoded_finish(&mut checkpoint,&bytes,observed,destination,source,expected_byte);
   let result=if copied {Ok(())}else{Err(ProgramError::InvalidAccountData)};
   destroy_owner(std::ptr::null_mut(),&mut *bytes,false);
   result
  },
  Err(error)=>Err(error),
 };
 finish_guard_shared(proof,counters[0]);
 let _=candidate; // Fixed Copy array has no destructor.
 destroy_owner(&mut *statement,std::ptr::null_mut(),true);
 finish_guard_shared(public,counters[1]);
 finish_guard_exclusive(checkpoint,counters[2]);
 result
}
'''
s=s[:s.index('#[kani::requires(std::mem::size_of_val(&proof)')]+helpers+heads+body+s[contract_end:]
s=s.replace('#[kani::stub_verified(encoded_finish)]\nfn actual_sdk_finish_drop_chain()', '#[kani::stub_verified(encoded_finish)]\n#[kani::stub_verified(destroy_owner)]\n#[kani::stub_verified(finish_guard_shared)]\n#[kani::stub_verified(finish_guard_exclusive)]\n#[kani::stub(std::alloc::dealloc,frozen_release_dealloc)]\nfn actual_sdk_finish_drop_chain()')
needle=' native_finish_drop_chain(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply,destination);';assert s.count(needle)==1
s=s.replace(needle,''' let observed:usize=kani::any();kani::assume(observed<1768);
 let expected_byte=match &reply {Ok(v) if v.len()==1768=>v[observed],_=>checkpoint_data[observed]};
 let expected_status=match &reply {Ok(v) if v.len()==1768=>0,Ok(_)=>1,Err(_)=>2};
 let actual_result=native_finish_drop_chain(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply,destination,observed,expected_byte,expected_status);
 kani::cover!(actual_result.is_ok(),"ordered modular tail accepts exact checkpoint size");
 kani::cover!(matches!(actual_result,Err(ProgramError::InvalidAccountData)),"ordered modular tail preserves length rejection");
 kani::cover!(matches!(actual_result,Err(ProgramError::InvalidInstructionData)),"ordered modular tail preserves mapped first error");''')
# Add the prerequisite owner-step harness, independent of the caller/guard proof.
a=s.rfind('\n}')
owner='''
#[kani::proof_for_contract(destroy_owner)] #[kani::unwind(48)]
#[kani::stub(std::alloc::dealloc,frozen_release_dealloc)]
fn actual_owner_step_frame(){
 let mut statement=std::mem::ManuallyDrop::new(Box::new(statement()));
 let bytes:[u8;1769]=kani::any();let length:usize=kani::any();kani::assume(length<=1769);
 let mut bytes=std::mem::ManuallyDrop::new(bytes[..length].to_vec());let which:bool=kani::any();
 destroy_owner(&mut *statement,&mut *bytes,which);
 kani::cover!(which,"actual statement destruction step");
 kani::cover!(!which&&length==1768,"actual accepted reply destruction step");
 kani::cover!(!which&&length==0,"actual empty reply destruction step");
}
'''
s=s[:a]+guard_harnesses+owner+s[a:];p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('native-finish-drop-chain-v1','modular-ordered-tail-v3'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,order=['reply owner','proof guard','Copy candidate','statement owner','public guard','checkpoint guard'],remaining='First prove destroy_owner at every source owner kind/length. Outer proof consumes exact copy and original typed guard contracts; their old source/domain pins must match. Validate explicit cleanup/compiler-drop equivalence and global allocator dispatch/owner/runtime/ABI. Then compose first-entry with actual child/oracle/TX2 execution. No source adoption or whole S2.'),indent=2)+'\n')
