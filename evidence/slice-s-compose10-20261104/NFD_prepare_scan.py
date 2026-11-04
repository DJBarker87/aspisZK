"""Scanner source cuts. Full equality association remains explicit until proved."""
from NFD_native_patch import E,frozen,program,helpers
from NFD_source_tools import calls
import sys,json,subprocess
shape,mode=sys.argv[1:3];slot=int(sys.argv[3]);assert shape in ['length','tag','prefix','finish','equality']
assert mode in ['positive','negative','allocation','reply','argument']
subprocess.run([sys.executable,str(E/'NFD_prepare_window.py'),'1','positive'],check=True)
f=frozen('programs/r1-cost-probe/src/r1_pool_adapter.rs');a=f.index('fn scan_proof_buffer(');original=f[a:f.index('\n}',a)+2]
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFD_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFD_KMX::KMX_copy_from_slice)]
'''
body=helpers();native=''
if shape=='length':
 native=original[original.index('    let proof_length'):original.index('    let candidate_start')].replace('bytes.len()','length')
 native='fn check(length:usize)->ProgramResult{\n'+native+'    Ok(())\n}\n'
 code='let length:usize=kani::any();let observed=matches!(check(length),Ok(()));assert!(observed=='+('!' if mode=='negative' else '')+'(length==verifier::PROOF_BYTES+688));'
elif shape=='tag':
 native='let proof_start=POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;let observed=bytes[proof_start+8]!=Variant::S2.tag();'
 code='let bytes:[u8;697]=kani::any();'+native+'assert!(observed=='+('!' if mode=='negative' else '')+'(bytes[696]!=2));'
 native=''
elif shape=='prefix':
 cut=original[original.index('    let candidate_start'):original.index('    if encode_pool_v1_pair_verified_afterstate_v1')]
 cut=calls(cut,'decode_pool_v1_pair_verified_afterstate_v1','decode','f')
 native='fn prefix(bytes:&[u8;688],f:&mut Frame)->Result<Box<PoolV1PairVerifiedAfterstateV1>,ProgramError>{\n'+cut+'    f.allocated=candidate.as_ref();\n    '+('Ok(Box::new(*candidate))' if mode=='allocation' else 'Ok(candidate)')+'\n}\n'
 left=['out.next_pair_index','out.next_root[i].0 as u64','out.next_frontier[k][i].0 as u64'][slot]
 right=['f.value.next_pair_index','f.value.next_root[i].0 as u64','f.value.next_frontier[k][i].0 as u64'][slot]
 body+='''struct Frame<'a>{header:&'a [u8;688],value:PoolV1PairVerifiedAfterstateV1,good:bool,allocated:*const PoolV1PairVerifiedAfterstateV1,calls:u8}
fn decode(b:&[u8],f:&mut Frame)->Result<PoolV1PairVerifiedAfterstateV1,PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==0&&b.len()==688&&core::ptr::eq(b.as_ptr(),f.header.as_ptr()));f.calls=1;if f.good{Ok(f.value)}else{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())}}
'''
 if mode=='reply':body=body.replace('Ok(f.value)','Err(NEE_any_PoolV1PairVerifierTransportErrorV1())')
 code='let header:[u8;688]=kani::any();let value=NEE_common().lane_transition.candidate_afterstate;let good:bool=kani::any();let i:usize=kani::any();let k:usize=kani::any();kani::assume(i<8&&k<20);let mut f=Frame{header:&header,value,good,allocated:core::ptr::null(),calls:0};let actual=prefix(&header,&mut f);assert!(f.calls==1);match actual{Ok(out)=>{assert!(good&&core::ptr::eq(out.as_ref(),f.allocated));assert!(('+left+')==('+right+')'+('^1' if mode=='negative' else '')+');},Err(ProgramError::InvalidAccountData)=>assert!(!good),Err(_)=>assert!(false)}'
elif shape=='finish':
 suffix=original[original.index('    if encode_pool_v1_pair_verified_afterstate_v1'):]
 expression='encode_pool_v1_pair_verified_afterstate_v1(&candidate)\n        .map_err(|_| ProgramError::InvalidAccountData)?\n        .as_ref()\n        != candidate_bytes'
 assert expression in suffix
 suffix=suffix.replace(expression,'different(&encode(&candidate,f).map_err(|_| ProgramError::InvalidAccountData)?,candidate_bytes,f)').replace('bytes[proof_start + 8]','tag')
 native='fn finish(candidate:Box<PoolV1PairVerifiedAfterstateV1>,candidate_bytes:&[u8;688],tag:u8,proof_length:usize,f:&mut Frame)->Result<ScannedAsqaProof,ProgramError>{\n'+suffix
 if mode=='negative':native=native.replace('candidate_afterstate: candidate','candidate_afterstate: Box::new(*candidate)')
 body+='''struct Frame<'a>{candidate:*const PoolV1PairVerifiedAfterstateV1,header:&'a [u8;688],calls:u8,good:bool,diff:bool,j:usize,byte:u8}
fn encode(c:&PoolV1PairVerifiedAfterstateV1,f:&mut Frame)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{assert!(f.calls==0&&core::ptr::eq(c,f.candidate));f.calls=1;if f.good{let out:[u8;688]=kani::any();f.byte=out[f.j];Ok(out)}else{Err(NEE_any_PoolV1PairVerifierTransportErrorV1())}}
fn different(b:&[u8;688],header:&[u8;688],f:&mut Frame)->bool{assert!(f.calls==1&&core::ptr::eq(header.as_ptr(),f.header.as_ptr())&&b[f.j]==f.byte);f.calls=2;f.diff}
'''
 code='let c=Box::new(NEE_common().lane_transition.candidate_afterstate);let ptr=c.as_ref() as *const _;let header:[u8;688]=kani::any();let tag:u8=kani::any();let proof_length:usize=kani::any();let j:usize=kani::any();kani::assume(j<688);let mut f=Frame{candidate:ptr,header:&header,calls:0,good:kani::any(),diff:kani::any(),j,byte:0};let actual=finish(c,&header,tag,proof_length,&mut f);match actual{Ok(out)=>assert!(f.good&&!f.diff&&tag==2&&f.calls==2&&out.proof_length==proof_length&&core::ptr::eq(out.candidate_afterstate.as_ref(),ptr)),Err(ProgramError::InvalidAccountData)=>assert!(!f.good||f.diff||tag!=2),Err(_)=>assert!(false)}'
else:
 code='let a:u8=kani::any();let b:u8=kani::any();let same:bool=kani::any();let left=[a];let right=[b];let ls:&[u8]=left.as_ref();let rs:&[u8]=right.as_ref();let unequal=ls!=rs;let step=same&&!unequal;assert!(step=='+('!' if mode=='negative' else '')+'(same&&(a==b)));'
 if mode=='argument':code=code.replace('let right=[b]','let right=[b^1]')
body+=native+attrs+'fn scan_cut(){'+code+'}\n';program(body,'NFD_scan')
(E/'NFD_SCAN_CURRENT.json').write_text(json.dumps(dict(shape=shape,mode=mode,slot=slot,source=body,native=native,frozen_body=original,classification='one source cut with arbitrary raw typed prestate; full688-byte equality-to-iteration association remains OPEN; no root credit'),indent=1)+'\n')
