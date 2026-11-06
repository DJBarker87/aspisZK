from NLK_native import *
import ast
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
FROZEN=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
s=subprocess.check_output(['git','show','HEAD:evidence/tx2-adapters3-20261109/NLA_registry.py'],text=True)
t=ast.parse(s)
HELPERS=next(ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='COMMON')
COMMON='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+HELPERS
ANN='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
def attempt(a,version,entry,mode):
 version=int(version);entry=entry=='entry';kind='entry' if entry else 'registry'
 typ='VerifierRegistry'+('Entry' if entry else '')+'V'+str(version)
 fun='decode_verifier_registry_'+('entry_' if entry else '')+'v'+str(version)
 ctor=kind+str(version)
 start=FROZEN.index('        let '+kind+' = '+fun+'(') if version==2 else FROZEN.index('    let '+kind+' = '+fun+'(')
 end=FROZEN.index(';',start)+1;segment=FROZEN[start:end]
 body=segment.replace(fun+'(', 'oracle(').replace(kind+'_account','account')
 length={(1,False):128,(1,True):192,(2,False):256,(2,True):320}[version,entry]
 text=COMMON+ANN+'''fn stage(){
 let mut data:[u8;SIZE]=kani::any();let coordinate:usize=kani::any();kani::assume(coordinate<SIZE);
 let expected=data[coordinate];let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut money:u64=kani::any();
 let account=AccountInfo::new(&key,false,false,&mut money,&mut data,&owner,false,0);
 let held:bool=kani::any();let exclusive=if held{Some(account.try_borrow_mut_data().unwrap())}else{None};
 let good:bool=kani::any();let raw=CTOR();let mut calls=0u8;let mut live=false;let mut byte=0u8;let mut length=0usize;
 let mut oracle=|input:&[u8]|->Result<TYP,aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError>{
 calls+=1;length=input.len();byte=input[coordinate];live=account.try_borrow_mut_data().is_err();
 if good{Ok(raw)}else{Err(aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError::WrongLength)}
 };
 let mut suffix=0u8;let mut out=(||->Result<TYP,ProgramError>{BODY suffix+=1;Ok(KIND)})();
 let mut released=if held{account.try_borrow_data().is_err()}else{account.try_borrow_mut_data().is_ok()};
 CORRUPT
 let reply=if held{out==Err(ProgramError::AccountBorrowFailed)}else if good{out==Ok(raw)}else{out==Err(ProgramError::InvalidAccountData)};
 assert!(reply&&released&&suffix==if !held&&good{1}else{0}&&if held{calls==0}else{calls==1&&live&&length==SIZE&&byte==expected},"native caller SAME data borrow decoder Result token lifetime and lexical Drop");
 drop(exclusive);
}
'''.replace('SIZE',str(length)).replace('CTOR',ctor).replace('TYP',typ).replace('BODY',body).replace('KIND',kind).replace('CORRUPT','released=!released;' if mode=='inverse' else '')
 mod='NLK_registry_borrow'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),version=version,entry=entry,mode=mode,domain=f'actual AccountInfo on {length} arbitrary bytes; selected coordinate; free or held-exclusive; full arbitrary child success; selected WrongLength error',borrow='actual SDK Ref; decoder observes live same data cell; every returned Err/Ok lexical cleanup; existing exclusive remains live',limits='child other errors parametric; arbitrary extent and abort prefix remain formal obligations; not complete registry invocation'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
