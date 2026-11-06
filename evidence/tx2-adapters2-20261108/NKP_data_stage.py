"""Final native invocation: ordered data/decoder stage, partial until control.
No credit is claimed without its matched native failing control.
"""
from NKP_registry import *
TEXT=COMMON+ANN+'''fn data_stage(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let bytes:[u8;32]=kani::any();let selector:u8=kani::any();kani::assume(selector<3);
 let stored=match selector{0=>Ok(bytes.to_vec()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};
 let account=OwnedAccount{key,owner,is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(32),bytes:stored};
 let raw=registry1();let decoder_ok:bool=kani::any();let i:usize=kani::any();kani::assume(i<32);
 let mut calls=0u8;let mut length=0usize;let mut observed=0u8;
 let out=(||->Result<VerifierRegistryV1,ProgramError>{
  let data=account.data()?;
  calls+=1;length=data.len();observed=data[i];
  let result=if decoder_ok{Ok(raw)}else{Err(aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError::WrongLength)};
  result.map_err(|_|ProgramError::InvalidAccountData)
 })();
 let expected=if selector==1{Err(ProgramError::AccountBorrowFailed)}else if selector==2||!decoder_ok{Err(ProgramError::InvalidAccountData)}else{Ok(raw)};
 assert!(out==expected&&if selector==0{calls==1&&length==32&&observed==bytes[i]}else{calls==0},"registry data decoder ordered prefix and borrowed byte");
}
'''
if __name__=='__main__':
 a='NKP_K080';mod='NKP_data_stage'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(TEXT.splitlines()))+' @@\n'+''.join('+'+line for line in TEXT.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,stage='data then decoder; no decoder call after data Err',domain='OwnedAccount bytes carrying32-byte window, or the two snapshot-produced errors; full arbitrary registryV1 raw value and decoder success/error tag',missing='matched native failing control and general input-window frame; NO CREDIT',modifies='local call record only',error_payload='ignored by map_err in exact source'),indent=1)+'\n')
 submit(a,'r1_pool_adapter::owned::'+mod+'::data_stage',P,mod,TEXT,'positive_unpaired')
