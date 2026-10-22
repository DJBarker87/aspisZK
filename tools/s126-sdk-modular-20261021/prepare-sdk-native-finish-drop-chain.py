#!/usr/bin/env python3
"""Exact post-first finish and owner/guard destruction frame.
Actual SDK acquisitions and allocations happen outside the checked operation,
as in the source's first-call boundary. Real guards, full statement Box,
candidate and full mapped ProgramError retained. Only exact previously checked
encoded_finish is a verified stub. No SDK/Drop model substitutions.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-drop-chain.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('#[kani::requires(std::mem::size_of_val(&proof)');b=s.index('#[kani::proof_for_contract(native_drop_chain)]',a);contract=s[a:b]
contract=contract.replace('fn native_drop_chain(', 'fn native_finish_drop_chain(').replace('counters:[*const Cell<isize>;3]){\n drop(proof);drop(public);drop(checkpoint);\n}', '''counters:[*const Cell<isize>;3],statement:Box<PoolV1PairForestTerminalStatementV1>,candidate:[u8;688],reply:Result<Vec<u8>,ProgramError>,destination:*mut[u8;1768])->Result<(),ProgramError>{
 let result=(||{
  let bytes=reply?;
  let source=bytes.as_ptr().cast::<[u8;1768]>();
  let expected=if bytes.len()==1768 {bytes[0]} else {checkpoint[0]};
  let ok=encoded_finish(&mut checkpoint,&bytes,0,destination,source,expected);
  if ok {Ok(())} else {Err(ProgramError::InvalidAccountData)}
 })();
 drop(proof);drop(candidate);drop(statement);drop(public);drop(checkpoint);
 result
}''')
contract=contract.replace('checkpoint:std::cell::RefMut','mut checkpoint:std::cell::RefMut')
contract=contract.replace('#[kani::modifies(counters[0]', '#[kani::requires(checkpoint.len()==1768 && destination==checkpoint.as_ptr().cast_mut().cast::<[u8;1768]>())]\n#[kani::requires(match &reply {Ok(v)=>v.len()<=1769,Err(e)=>matches!(e,ProgramError::InvalidInstructionData)})]\n#[kani::modifies(destination,counters[0]')
s=s[:a]+contract+s[b:]
s=s.replace('#[kani::proof_for_contract(native_drop_chain)] #[kani::unwind(33)]','#[kani::proof_for_contract(native_finish_drop_chain)] #[kani::unwind(1772)]\n#[kani::stub_verified(encoded_finish)]')
s=s.replace('fn actual_sdk_drop_chain(){','fn actual_sdk_finish_drop_chain(){')
s=s.replace(' let checkpoint_data=accounts[2].try_borrow_mut_data().unwrap();',' let mut checkpoint_data=accounts[2].try_borrow_mut_data().unwrap();')
s=s.replace(' native_drop_chain(proof_data,public_data,checkpoint_data,counters);\n let actual:Result<(),ProgramError>=Ok(());',''' let statement=Box::new(statement());let candidate:[u8;688]=kani::any();
 let reply:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let first_ok:bool=kani::any();
 let reply=if first_ok {Ok(reply[..reply_len].to_vec())}else{Err(ProgramError::InvalidInstructionData)};
 let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();
 native_finish_drop_chain(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply,destination);
 let actual:Result<(),ProgramError>=Ok(());''')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('native-drop-chain-v3','native-finish-drop-chain-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All frame/contract properties must pass; join concrete entry/precondition certificates and owner/source/runtime interpretation, actual installed child/gate/scan/oracle/TX2 transport.'),indent=2)+'\n')
