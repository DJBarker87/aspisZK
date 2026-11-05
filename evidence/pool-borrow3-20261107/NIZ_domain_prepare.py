from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs,account_setup
from NIZ_frozen_identity import frozen
E=Path(__file__).resolve().parent
kind,mode=sys.argv[1:];negative=mode=='negative'
expr=' && '.join(f'a[{i}]==b[{i}]' for i in range(32))
stub='fn NIZ_eq(left:&solana_program::pubkey::Pubkey,right:&solana_program::pubkey::Pubkey)->bool{let a:&[u8]=left.as_ref();let b:&[u8]=right.as_ref();'+expr+'}\n'
attribute='#[kani::stub(solana_program::pubkey::Pubkey::eq,NIZ_eq)]\n'
extra={};path='programs/aspis-pool/src/processor.rs'
if kind=='keyview':
 body='use solana_program::pubkey::Pubkey;let input:[u8;32]=kani::any();let key=Pubkey::new_from_array(input);let bytes:&[u8]=key.as_ref();let index=usize::from(kani::any::<u8>());kani::assume(index<32);assert!(core::mem::size_of::<Pubkey>()==32);assert!(bytes.len()==32);let observed=bytes[index]'+('^1' if negative else '')+';assert!(observed==input[index]);'
 source=attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
 domain='Every native Pubkey byte array and one arbitrary index <32; fixed32 typed/readable domain, no canonicality restriction.'
elif kind=='prefix':
 path='programs/aspis-pool/src/pair_processor.rs';text=frozen()[path].decode();assert '.any(|previous| previous.key == account.key)' in text
 body=account_setup(2)+'let account=&a1;let same=a0.key==account.key;let found='+('false' if negative else 'core::iter::once(&a0).any(|previous| previous.key == account.key)')+';assert!(found==same);'
 source=stub+attrs()+'\n'+attribute+'#[kani::proof]\nfn certificate(){'+body+'}\n'
 domain='One arbitrary reached inner any-predicate iteration; two full arbitrary keys, exact source closure; prefix induction and actual iterator association separate.'
 extra['stub']='NIZ_eq; NIZ_KeyEquality value laws; full source association pending'
elif kind=='groups':
 path='programs/aspis-pool/src/deposit.rs';text=frozen()[path].decode();start=text.index('            if state_account.key == token_account.key {');end=text.index('            }',start)+len('            }');original=text[start:end]
 result='Ok(())' if negative else '(||->Result<(),ProgramError>{'+original+'\nOk(())})()'
 body=account_setup(2)+'let state_account=&a0;let token_account=&a1;let same=state_account.key==token_account.key;let result:Result<(),ProgramError>='+result+';assert!(result==if same{Err(ProgramError::InvalidArgument)}else{Ok(())});'
 source=stub+attrs()+'\n'+attribute+'#[kani::proof]\nfn certificate(){'+body+'}\n'
 domain='One original disjoint-groups inner comparison on arbitrary full key references; outer/inner induction and exact caller group mapping separate.'
 extra.update(stub='NIZ_eq; full source association pending',original_body_sha256=hashlib.sha256(original.encode()).hexdigest())
elif kind=='questionmark':
 forwarded='let _=reply;' if negative else 'reply?;'
 body='use solana_program::{entrypoint::ProgramResult,program_error::ProgramError};fn reached(reply:ProgramResult,seen:&mut bool)->ProgramResult{'+forwarded+'*seen=true;Ok(())}let ok:bool=kani::any();let reply=if ok{Ok(())}else{Err(ProgramError::InvalidArgument)};let mut seen=false;let result=reached(reply,&mut seen);assert!(seen==ok);assert!(result==if ok{Ok(())}else{Err(ProgramError::InvalidArgument)});'
 source=attrs()+'\n#[kani::proof]\nfn certificate(){'+body+'}\n'
 domain='Both and only the original uniqueness helper ProgramResult arms, explicit constructors; arbitrary pre-return reply, source ? dispatch and continuation marker.'
else:raise ValueError(kind)
stage(path,source,'source domain step '+kind,mode,domain,'Full parent source/callee/guard identity association remains separate; no owner ScopeRun supplied.',dict(expected_verdict='FAIL' if negative else 'PASS',member=kind,native_args=['--unwind','34'],**extra))
