#[derive(Clone,Copy,PartialEq,Eq)]
pub enum NGGSpineError {InvalidInstructionData,NotEnoughAccountKeys,InvalidArgument,ArithmeticOverflow,Child(u64)}
#[derive(Clone,Copy)]
pub struct Hints {pub current_page:u8,pub next_page:u8,pub vault_authority:u8,pub vault_token_account:u8}
pub fn decode_prefix<R>(instruction_data:&[u8],decoded:Result<R,NGGSpineError>,account_count:usize)->Result<(R,[usize;3],Hints),NGGSpineError>{
let split=instruction_data.len().checked_sub(4).ok_or(NGGSpineError::InvalidInstructionData)?;
let (_body,hints)=instruction_data.split_at(split);
let hints=Hints{current_page:hints[0],next_page:hints[1],vault_authority:hints[2],vault_token_account:hints[3]};
let request=decoded?;
if account_count==0{return Err(NGGSpineError::NotEnoughAccountKeys);}
if account_count<2{return Err(NGGSpineError::NotEnoughAccountKeys);}
if account_count<3{return Err(NGGSpineError::NotEnoughAccountKeys);}
Ok((request,[0,1,2],hints))}
#[derive(Clone,Copy)]
pub struct Layout {pub marker_index:usize,pub payer_index:usize,pub system_program_index:usize,pub registry_start:usize,pub verifier_index:usize,pub proof_index:usize,pub verifier_checkpoint_index:usize,pub token_start:usize}
pub fn layout_tail(cursor:usize,withdrawal:bool,accounts_len:usize,unique:Result<(),NGGSpineError>)->Result<Layout,NGGSpineError>{
let marker_index=cursor;let payer_index=cursor+1;let system_program_index=cursor+2;let registry_start=cursor+3;let verifier_index=cursor+5;let proof_index=cursor+6;let token_start=cursor+7;
let expected=token_start.checked_add(if withdrawal{5}else{0}).ok_or(NGGSpineError::ArithmeticOverflow)?;
let verifier_checkpoint_index=expected;let expected=expected+1;
if accounts_len!=expected{return Err(if accounts_len<expected{NGGSpineError::NotEnoughAccountKeys}else{NGGSpineError::InvalidArgument});}
unique?;Ok(Layout{marker_index,payer_index,system_program_index,registry_start,verifier_index,proof_index,verifier_checkpoint_index,token_start})}
