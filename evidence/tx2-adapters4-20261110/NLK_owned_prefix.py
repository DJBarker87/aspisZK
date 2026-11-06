from NLK_owned_chain import *
def attempt(a,mode,part="whole"):
 start=FROZEN.index('    let [proof_account, master_account',FROZEN.index('fn authenticate_asq8_accounts('))
 end=FROZEN.index('    let master =',start);segment=FROZEN[start:end]
 if part=='front':segment=segment[:segment.index('    require_readonly_account(master_account')]
 if part=='owners':
  segment=segment[segment.index('    require_readonly_account(master_account'):segment.index('    require_distinct_accounts(')]
  segment='let master_account=&accounts[1];let checkpoint_account=&accounts[2];let lane_account=&accounts[3];'+segment
 assert part in ['whole','front','owners']
 text=COMMON+HELPERS+ANN+'''fn stage(){
 let mut all=[account::<1>(),account::<1>(),account::<1>(),account::<1>(),account::<1>(),account::<1>(),account::<1>(),account::<1>()];for a in all.iter_mut(){let ok:bool=kani::any();a.length=if ok{Ok(kani::any())}else{Err(ProgramError::AccountBorrowFailed)};}let n:usize=kani::any();kani::assume(n<=8);let accounts=&all[..n];let pool=Pubkey::new_from_array(kani::any());let pool_program=&pool;let verifier=Pubkey::new_from_array(kani::any());let verifier_program=&verifier;let mut suffix=0u8;
 let mut out=(||->ProgramResult{SEGMENT suffix+=1;Ok(())})();
 let expected=if n<7{Err(ProgramError::NotEnoughAccountKeys)}else if n>7{Err(ProgramError::InvalidArgument)}else{
 require_readonly_buffer(&accounts[0]).and_then(|_|require_verifier_checkpoint(&accounts[6],verifier_program,false)).and_then(|_|require_readonly_account(&accounts[1],pool_program)).and_then(|_|require_readonly_account(&accounts[2],pool_program)).and_then(|_|require_readonly_account(&accounts[3],pool_program)).and_then(|_|require_distinct_accounts(&[&accounts[0],&accounts[1],&accounts[2],&accounts[3],&accounts[4],&accounts[5],&accounts[6]]))};
 CORRUPT assert!(out==expected&&suffix==if expected.is_ok(){1}else{0},"actual owned233 cardinality and complete ordered metadata rejection prefix");}
'''.replace('SEGMENT',segment).replace('CORRUPT','suffix^=1;' if mode=='inverse' else '')
 if part=='front':
  old='require_readonly_buffer(&accounts[0]).and_then('
  e_start=text.index(old)
  e_end=text.index('};',e_start)
  text=text[:e_start]+'require_readonly_buffer(&accounts[0]).and_then(|_|require_verifier_checkpoint(&accounts[6],verifier_program,false))'+text[e_end:]
 if part=='owners':
  e_start=text.index('let expected=')
  e_end=text.index(' CORRUPT',e_start) if ' CORRUPT' in text[e_start:] else text.index(' assert!',e_start)
  # Corruption already expanded in text; use source-unique Result boundary.
  e_end=text.index(';\n ',e_start)+1
  text=text[:e_start]+'let expected=require_readonly_account(&accounts[1],pool_program).and_then(|_|require_readonly_account(&accounts[2],pool_program)).and_then(|_|require_readonly_account(&accounts[3],pool_program));'+text[e_end:]
  text=text.replace('kani::assume(n<=8)','kani::assume(n==7)')
 mod='NLK_owned_prefix'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),mode=mode,part=part,domain='arbitrary owned records and length0..8; cardinality overflow case represented8; metadata prefix has no output-success premise',limits='intermediate233 prefix; decoder/authentication continuation remains'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
