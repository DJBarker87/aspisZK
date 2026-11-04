from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';I=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())
s=I[C+'NFU_compact.rs'];s+='''
#[kani::proof] #[kani::unwind(2)]
fn semantic_reject(){let input:[u8;7015]=kani::any();let mut out:[u8;13831]=kani::any();let n:usize=kani::any();let m:usize=kani::any();kani::assume(n<=7015&&m<=13831);kani::assume(n!=7015||m!=13831);let j:usize=kani::any();kani::assume(j<13831);let old=out[j];let r=expand_semantic(&input[..n],&mut out[..m]);assert!((r==Err(CodecError::Length)&&out[j]==old) != cfg!(NFU_invert));}
'''
w=I[C+'NFU_wire.rs'];w+='''
#[kani::proof] #[kani::unwind(2)]
fn parse_invalid_row(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row>=27);let n:usize=kani::any();kani::assume(n<=3717);assert!(matches!(parse_record(row,&b[..n]),Err(Error::InvalidRow)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_bad_length(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let size=row_shape(row).unwrap().1;let n:usize=kani::any();kani::assume(n<=3717&&n!=5+size);assert!(matches!(parse_record(row,&b[..n]),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_bad_tag(){let b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let (tag,size)=row_shape(row).unwrap();kani::assume(b[0]!=tag);assert!(matches!(parse_record(row,&b[..5+size]),Err(Error::Tag{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn parse_bad_header(){let mut b:[u8;3717]=kani::any();let row:u8=kani::any();kani::assume(row<27);let (tag,size)=row_shape(row).unwrap();b[0]=tag;kani::assume(u32::from_le_bytes([b[1],b[2],b[3],b[4]]) as usize!=size);assert!(matches!(parse_record(row,&b[..5+size]),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(2)]
fn parse_at_short(){let b:[u8;13831]=kani::any();let row:u8=kani::any();kani::assume(row<27);let n:usize=kani::any();let offset:usize=kani::any();kani::assume(n<=13831&&offset<=13831);let length=5+row_shape(row).unwrap().1;kani::assume(offset+length>n);assert!(matches!(parse_record_at(&b[..n],row,offset),Err(Error::Length{row:r}) if r==row) != cfg!(NFU_invert));}
'''
p='programs/r1-cost-probe/src/NFU_owned.rs';a=I[p];a+='''
#[kani::proof] #[kani::unwind(3)]
fn stage1_empty(){let b:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);assert!(matches!(stage1(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage1_owned_empty(){let b:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);assert!(matches!(stage1_owned(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage2_empty(){let b:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);assert!(matches!(stage2(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage2_owned_empty(){let b:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);assert!(matches!(stage2_owned(&Pubkey::new_from_array([0;32]),&[],&b[..n],Ok(kani::any())),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
'''
update({C+'NFU_compact.rs':s,C+'NFU_wire.rs':w,p:a},'NFU_guard_fragments')
items=[]
for i,mod,t,program in [(42,'compact','semantic_reject',False),(44,'r1_wire','parse_invalid_row',False),(46,'r1_wire','parse_bad_length',False),(48,'r1_wire','parse_bad_tag',False),(50,'r1_wire','parse_bad_header',False),(52,'r1_wire','parse_at_short',False),(54,'r1_pool_adapter::owned','stage1_empty',True),(56,'r1_pool_adapter::owned','stage1_owned_empty',True),(58,'r1_pool_adapter::owned','stage2_empty',True),(60,'r1_pool_adapter::owned','stage2_owned_empty',True)]:
 for j,e in [(i,0),(i+1,1)]:items.append(dict(attempt=f'NFU_K{j:03}',kind='kani',target=mod+'::NFU_'+('owned' if program else 'wire' if mod=='r1_wire' else 'compact')+'::'+t,exit=e,env={**({'NFU_PROGRAM':'1'}if program else {}),**({'NFU_INVERT':'1'}if e else {})}))
(E/'NFU_QUEUE11.json').write_text(json.dumps(items,indent=1)+'\n')
