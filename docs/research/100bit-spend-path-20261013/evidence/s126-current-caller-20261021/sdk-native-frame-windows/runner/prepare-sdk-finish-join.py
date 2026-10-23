#!/usr/bin/env python3
"""Real RefMut post-child length/copy/drop block versus complete owned heap.
This is the source continuation after the child reply, with actual SDK guards.
It does not prove the earlier child-call/SDK-to-reference execution transport.
"""
from pathlib import Path
import sys,subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'wide';assert mode in ['wide','normalized']
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-heap-join.py'),str(O),'chain','1768'],check=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
frozen=subprocess.check_output(['git','-C',str(R),'show',freeze+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
def cut(s,name):
 a=s.index('fn '+name);i=s.index('{',a)+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
stage=cut(frozen,'stage1');native=stage[stage.index('    if checkpoint.len() != checkpoint_data.len()'):]
prior=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/src/lib.rs'
body=cut(prior.read_text(),'owned_stage1_body');owned=body[body.index(' if result.len()!=sdk.data_cells[checkpoint.data_slot].bytes.len()'):]
p=O/'src/lib.rs';s=p.read_text();oldNative=cut(s,'native_chain');oldModel=cut(s,'model_chain')
nativeHelper='''fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,checkpoint:Vec<u8>)->Result<(),ProgramError> {
'''+native
modelHelper='''fn owned_finish(sdk:&mut OwnedSdk,checkpoint:OwnedAccount,result:Vec<u8>)->Result<(),ProgramError> {
'''+owned
newNative='''fn native_chain(accounts:&[AccountInfo<'_>],reply:Vec<u8>,counters:&[*const std::cell::Cell<isize>;3],trace:&mut Vec<[isize;3]>)->Result<(),ProgramError> {
 let mut checkpoint_data=accounts[2].try_borrow_mut_data()?;
 trace.push(native_counts(counters));
 let public_data=accounts[1].try_borrow_data()?;
 trace.push(native_counts(counters));
 let proof_data=accounts[0].try_borrow_data()?;
 trace.push(native_counts(counters));
 let result=native_finish(&mut checkpoint_data,reply);
 let _=(public_data.len(),proof_data.len());
 result
}'''
newModel='''fn model_chain(model:&mut OwnedSdk,reply:Vec<u8>,trace:&mut Vec<[isize;3]>)->(Result<(),ProgramError>,LiveGuards) {
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 let status=(||{
  let checkpoint=model.accounts[2];
  owned_acquire_checkpoint(model,&mut guards,checkpoint.data_slot)?;
  trace.push(model_counts(model));
  let public_slot=model.accounts[1].data_slot;
  owned_acquire_shared(model,public_slot)?;guards.public=Some(public_slot);
  trace.push(model_counts(model));
  let proof_slot=model.accounts[0].data_slot;
  owned_acquire_shared(model,proof_slot)?;guards.proof=Some(proof_slot);
  trace.push(model_counts(model));
  owned_finish(model,checkpoint,reply)
 })();
 (status,guards)
}'''
s=s.replace(oldNative,nativeHelper+'\n'+modelHelper+'\n'+newNative).replace(oldModel,newModel)
s=s.replace('fn three_account_heap_chain_join()', 'fn actual_finish_join()')
s=s.replace(' let cut:u8=kani::any();kani::assume(cut<5);',' let reply_bytes:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let reply=reply_bytes[..reply_len].to_vec();')
s=s.replace('model_chain(&mut model,cut,','model_chain(&mut model,reply.clone(),').replace('native_chain(&accounts,cut,','native_chain(&accounts,reply,')
a=s.index(' kani::cover!(actual.is_ok(),');b=s.index(' for i in 0..3 {\n  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);',a)
s=s[:a]+''' kani::cover!(actual.is_ok()&&reply_len==1768,"complete SDK copy then guard drops");
 kani::cover!(matches!(actual,Err(ProgramError::InvalidAccountData)),"length rejection then guard drops");
 kani::cover!(actual.is_ok()&&data_slots[0]==data_slots[1],"shared readonly aliases with independent checkpoint");
 let observed_slot:usize=kani::any();kani::assume(observed_slot<3);
 if lengths[observed_slot]>0 {
  let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);
  // Obtain the pointer from the retained SDK cell after all source guards drop.
  let pointer=unsafe{(**data_roots[observed_slot].as_ptr()).as_ptr()};
  assert_eq!(unsafe{*pointer.add(observed)},model.data_cells[observed_slot].bytes[observed]);
 }
'''+s[b:]
if mode=='normalized':
 s=s.replace('let mut b0:[u8;1768]', 'let mut b0:[u8;58295]').replace('let mut b1:[u8;1768]', 'let mut b1:[u8;58295]').replace('let mut b2:[u8;1768]', 'let mut b2:[u8;58295]')
 s=s.replace('let lengths:[usize;3]=kani::any();for length in lengths {kani::assume(length<=1768);}', 'let lengths:[usize;3]=[58295,1880,1768];')
 s=s.replace('let data_slots:[usize;3]=kani::any();', 'let data_slots:[usize;3]=[0,1,2];')
 # Distinct data identities are part of the reached-entry normalization, not a cover claim here.
 s=s.replace(' kani::cover!(actual.is_ok()&&data_slots[0]==data_slots[1],"shared readonly aliases with independent checkpoint");','')
 s=s.replace(' kani::cover!(data_slots[0]==data_slots[1]&&data_slots[1]==data_slots[2],"all account data handles alias");','')
 p.write_text(s)
else:p.write_text(s)
c=O/'Cargo.toml';c.write_text(c.read_text().replace('aspis-s126-sdk-heap-chain-join','aspis-s126-sdk-finish-join'))
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',protocol_freeze=freeze,source_sha256=sha(s),mode=mode,native_finish_source=native,native_finish_sha256=sha(native),owned_finish_source=owned,owned_finish_sha256=sha(owned),max_buffer_bytes=1768,reply_max_bytes=1769,qualification=__doc__,domain='Three real AccountInfo values and complete owned accounts/data/lamport heaps, independent alias maps, every signed data/lamport counter, arbitrary metadata and buffer bytes/lengths0..1768. Source guards are acquired in order to construct the reached post-child state; actual source last block retains RefMut. Arbitrary reply bytes and lengths0..1769. Every reached guard count, return status, observed byte in an arbitrary heap cell, metadata/header/lamport field and final counter is compared. Empty cells are handled without assuming an observation exists.',remaining='Need earlier native source prefix/callee/returned-reply transport and embedding to instantiate this local post-child continuation in the whole source caller.'),indent=2)+'\n')

if mode=='normalized':
 p=O/'source-cut.json';m=json.loads(p.read_text());m['max_buffer_bytes']=58295
 m['domain']='Reached-entry normalized SDK domain: distinct proof/public/checkpoint data nodes with exact58295/1880/1768 descriptors; all corresponding bytes, arbitrary account metadata, independent lamport aliases, every signed initial data/lamport counter, arbitrary1769 reply bytes/length0..1769. Exact source post-child block retains RefMut; native/owned setup derives live guards and then compares all return/drop counters and an arbitrary byte in any data node. Arbitrary safe Rc headers are a separate frame boundary. This is not an unrestricted-input source theorem.'
 m['remaining']='Discharge this normalized-entry premise from the earlier native source metadata/decoder/proof framing/tx1-entry cuts, and compose the actual child returned-reply and SDK embedding transports. No global adversary restriction or whole S2 closure follows from this candidate.'
 p.write_text(json.dumps(m,indent=2)+'\n')
