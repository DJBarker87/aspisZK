from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';I=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text());w=I[C+'NFU_wire.rs']
w=w.replace('fn parse_bad_header()', '#[kani::stub(validate_record_fields,unreachable_validation)]\nfn parse_bad_header()',1)
w+='''
fn unreachable_validation(_:u8,_:&[u8])->Result<(),Error>{assert!(false,"header guard must not call validation");Ok(())}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_record(){let b:[u8;3717]=kani::any();let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);&b[start..start+len]});let p=Prefix{c1_root:[0;32],records};let row:u8=kani::any();let r=p.record(row);let exact=if row>=27{matches!(r,Err(Error::InvalidRow))}else{match r{Ok(s)=>core::ptr::eq(s.as_ptr(),records[row as usize].as_ptr())&&s.len()==records[row as usize].len(),Err(_)=>false}};assert!(exact != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prefix_validated(){let b:[u8;3717]=kani::any();let records:[&[u8];27]=core::array::from_fn(|_|{let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=3717&&len<=3717-start);&b[start..start+len]});let p=Prefix{c1_root:[0;32],records};let row:u8=kani::any();let r=p.validated_record(row);let exact=if row>=27{matches!(r,Err(Error::InvalidRow))}else{match r{Ok(s)=>s.row==row&&core::ptr::eq(s.framed.as_ptr(),records[row as usize].as_ptr())&&s.framed.len()==records[row as usize].len(),Err(_)=>false}};assert!(exact != cfg!(NFU_invert));}
'''
p='programs/r1-cost-probe/src/NFU_owned.rs';a=I[p]
a+='''
// Source-shaped one iteration, retaining the original byte read and tail update.
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if remaining.is_empty(){return(0,remaining,Ok(()));}
 if remaining[0]!=0{return(1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
 remaining=&remaining[1..];(2,remaining,Ok(()))
}
#[kani::proof] #[kani::unwind(3)]
fn zero_full_step(){let b:[u8;4096]=kani::any();let start:usize=kani::any();let n:usize=kani::any();kani::assume(start<=4096&&n<=4096-start);let view=&b[start..start+n];let j:usize=kani::any();kani::assume(j<4096);let before=b[j];let(tag,rest,result)=zero_cut(view);let want=if n==0{0}else if b[start]!=0{1}else{2};let shift=if want==2{1}else{0};let exact=tag==want&&rest.len()==n-shift&&core::ptr::eq(rest.as_ptr(),view.as_ptr().wrapping_add(shift))&&b[j]==before&&if want==1{matches!(result,Err(ProgramError::AccountAlreadyInitialized))}else{matches!(result,Ok(()))};assert!(exact != cfg!(NFU_invert));}
'''
update({C+'NFU_wire.rs':w,p:a},'NFU_prefix_zero')
# Resume independently unchanged, unlaunched targets; do not launch K051.
items=[dict(attempt='NFU_K062',kind='kani',target='r1_wire::NFU_wire::parse_bad_header',exit=0),dict(attempt='NFU_K063',kind='kani',target='r1_wire::NFU_wire::parse_bad_header',exit=1,env={'NFU_INVERT':'1'})]
old=json.loads((E/'NFU_QUEUE11.json').read_text());items+= [x for x in old if int(x['attempt'][-3:])>=52]
for i,t,prog in [(64,'prefix_record',False),(66,'prefix_validated',False),(68,'zero_full_step',True)]:
 for j,e in [(i,0),(i+1,1)]:items.append(dict(attempt=f'NFU_K{j:03}',kind='kani',target=('r1_pool_adapter::owned::NFU_owned::' if prog else 'r1_wire::NFU_wire::')+t,exit=e,env={**({'NFU_PROGRAM':'1'}if prog else {}),**({'NFU_INVERT':'1'}if e else {})}))
(E/'NFU_QUEUE12.json').write_text(json.dumps(items,indent=1)+'\n')
