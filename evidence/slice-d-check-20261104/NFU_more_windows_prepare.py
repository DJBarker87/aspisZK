from pathlib import Path
import json,subprocess,hashlib
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';inputs=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())
s=inputs[C+'NFU_compact.rs']
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
'''
s=s.replace('fn check_one()',attrs+'fn check_one()',1)
s+='''
#[kani::proof] #[kani::unwind(35)]
KMXL
fn copy4(){let source:[u8;4]=kani::any();let mut out:[u8;4]=kani::any();out.copy_from_slice(&source);let j:usize=kani::any();kani::assume(j<4);assert!((out[j]==source[j]) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn expand_iterator(){
 let input:[u8;1856]=kani::any();let mut output:[u8;3712]=kani::any();
 let n:usize=kani::any();kani::assume(n<=1856&&n%16==0);let m=2*n;
 let i:usize=kani::any();kani::assume(i<=n/16);let base=output.as_mut_ptr();
 let mut it=input[16*i..n].chunks_exact(16).zip(output[32*i..m].chunks_exact_mut(32));
 let mut exact=it.len()==n/16-i;
 match it.next(){None=>exact&=i==n/16,Some((c,o))=>{exact&=i<n/16&&c.len()==16&&o.len()==32&&core::ptr::eq(c.as_ptr(),input[16*i..].as_ptr())&&core::ptr::eq(o.as_ptr(),base.wrapping_add(32*i))&&it.len()==n/16-(i+1);}}
 assert!(exact != cfg!(NFU_invert));
}
'''.replace('KMXL',attrs)
src=subprocess.check_output(['git','show','4bb3b3f:'+C+'r1_wire.rs'],text=True)
start=src.index('    for (value, bytes) in payload.chunks_exact(32).enumerate() {')
lo=src.index('\n',start)+1;hi=src.index('\n    }\n    Ok(())',lo);body=src[lo:hi]
w=inputs[C+'NFU_wire.rs']
w+='\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
w+='fn frozen_validator_step(row:u8,value:usize,bytes:&[u8])->Result<(),Error>{\n'+body+'\nOk(())\n}\n'
w+='''
#[kani::proof] #[kani::unwind(35)]
KMXL
fn validate_step(){let b:[u8;32]=kani::any();let row:u8=kani::any();let value:usize=kani::any();kani::assume(value<116);let mut good=true;for j in 0..4{good&=u32::from_le_bytes([b[4*j],b[4*j+1],b[4*j+2],b[4*j+3]])<0x7fffffff;}for j in 16..32{good&=b[j]==0;}let actual=frozen_validator_step(row,value,&b);let exact=if good{matches!(actual,Ok(()))}else{matches!(actual,Err(Error::NonCanonical{row:r,value:v}) if r==row&&v==value)};assert!(exact != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn validate_iterator(){
 let b:[u8;3712]=kani::any();let n:usize=kani::any();kani::assume(n<=3712);let i:usize=kani::any();kani::assume(i<=n/32);
 let mut it=b[..n].chunks_exact(32).enumerate();if i>0{let _=it.nth(i-1);}
 let mut exact=it.len()==n/32-i;
 match it.next(){None=>exact&=i==n/32,Some((index,part))=>{exact&=index==i&&part.len()==32&&core::ptr::eq(part.as_ptr(),b[32*i..].as_ptr())&&it.len()==n/32-(i+1);}}
 assert!(exact != cfg!(NFU_invert));
}
'''.replace('KMXL',attrs)
update({C+'NFU_compact.rs':s,C+'NFU_wire.rs':w},'NFU_more_windows')
(E/'NFU_VALIDATOR_STEP_SOURCE.json').write_text(json.dumps(dict(source=C+'r1_wire.rs',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_file_sha256=hashlib.sha256(src.encode()).hexdigest(),frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),byte_range=[len(src[:lo].encode()),len(src[:hi].encode())],actual_iteration_body=body,transformation='Verbatim source loop body; row/value/arbitrary32byte window are independent function parameters; append Ok on continuation. Full root remains unchanged and byte-pinned.'),indent=1)+'\n')
