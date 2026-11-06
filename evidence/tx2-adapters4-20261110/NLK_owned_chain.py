from NLK_native import *
import ast,re
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
FROZEN=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
def literal(path,aug=False):
 t=ast.parse(subprocess.check_output(['git','show','HEAD:'+path],text=True))
 for n in t.body:
  if aug and isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='COMMON':return ast.literal_eval(n.value)
  if not aug and isinstance(n,ast.Assign) and any(isinstance(a,ast.Name) and a.id=='COMMON' for a in n.targets):return ast.literal_eval(n.value)
COMMON=literal('evidence/tx2-adapters-20261108/NKF_wrappers.py')+literal('evidence/tx2-adapters3-20261109/NLA_registry.py',True)
ANN='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
def change_calls(s,name,new,extra):
 pos=0
 while True:
  i=s.find(name+'(',pos)
  if i<0:return s
  j=i+len(name)+1;depth=1
  while depth:
   if s[j]=='(':depth+=1
   if s[j]==')':depth-=1
   j+=1
  s=s[:i]+new+s[i+len(name):j-1].rstrip().removesuffix(',')+','+extra+s[j-1:]
  pos=j+len(new)-len(name)+len(extra)+1
HELPERS='''
#[derive(Clone,Copy,PartialEq,Eq)] struct Log{events:[u8;16],n:usize,pda:usize}
fn emit(log:&mut Log,e:u8){log.events[log.n]=e;log.n+=1;}
fn data<'a>(a:&'a OwnedAccount,log:&mut Log,tag:u8)->Result<&'a[u8],ProgramError>{emit(log,tag);a.data()}
fn ro(a:&OwnedAccount,p:&Pubkey,log:&mut Log)->ProgramResult{emit(log,13);require_readonly_account(a,p)}
fn pda(_seeds:&[&[u8]],_program:&Pubkey,log:&mut Log,replies:&[Result<Pubkey,solana_program::pubkey::PubkeyError>;4])->Result<Pubkey,solana_program::pubkey::PubkeyError>{emit(log,30+log.pda as u8);let r=replies[log.pda].clone();log.pda+=1;r}
fn account<const N:usize>()->OwnedAccount{let bytes:[u8;N]=kani::any();let boxed:Box<[u8]>=Box::new(bytes);let value=boxed.into_vec();let tag:u8=kani::any();kani::assume(tag<3);OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(N),bytes:match tag{0=>Ok(value),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)}}}
fn pda_reply()->Result<Pubkey,solana_program::pubkey::PubkeyError>{use solana_program::pubkey::PubkeyError;let s:u8=kani::any();kani::assume(s<4);match s{0=>Ok(Pubkey::new_from_array(kani::any())),1=>Err(PubkeyError::InvalidSeeds),2=>Err(PubkeyError::IllegalOwner),_=>Err(PubkeyError::MaxSeedLengthExceeded)}}
'''
def attempt(a,version,mode,part="whole"):
 version=int(version)
 if version==2:
  start=FROZEN.index('        let loader =',FROZEN.index('fn authenticate_invariant_release_registry'))
  end=FROZEN.index('        return Ok(());',start)+len('        return Ok(());')
 else:
  start=FROZEN.index('    let registry = decode_verifier_registry_v1(',FROZEN.index('fn authenticate_invariant_release_registry'))
  end=FROZEN.index('\n}',start)
 segment=FROZEN[start:end]
 if part=='registry':segment=segment[:segment.index('        require_readonly_account(entry_account')]+ '\nOk(())'
 if part=='entry':segment=segment[segment.index('        require_readonly_account(entry_account'):]
 assert part in ['whole','registry','entry']
 body=segment
 for kind in ['registry','entry']:
  fun='decode_verifier_registry_'+('entry_' if kind=='entry' else '')+'v'+str(version)
  body=change_calls(body,fun,'decode_'+kind,'&mut log,raw_'+kind)
  body=body.replace(kind+'_account.data()','data('+kind+'_account,&mut log,'+('10' if kind=='registry' else '12')+')')
 body=change_calls(body,'Pubkey::create_program_address','pda','&mut log,&pda_replies')
 body=change_calls(body,'require_readonly_account','ro','&mut log')
 defs=''
 for kind in ['registry','entry']:
  typ='VerifierRegistry'+('Entry' if kind=='entry' else '')+'V'+str(version)
  defs+='fn decode_'+kind+'(_bytes:&[u8],log:&mut Log,reply:Result<'+typ+',aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError>)->Result<'+typ+',aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError>{emit(log,'+('11' if kind=='registry' else '14')+');reply}\n'
 # Independent reference uses ordered stage gates; all Result arms propagate.
 expected=segment
 expected=expected.replace('let registry = decode_verifier_registry_v'+str(version)+'(registry_account.data()?)','emit(&mut expected_log,10);let _=registry_account.data()?;emit(&mut expected_log,11);let registry = raw_registry')
 expected=expected.replace('let entry = decode_verifier_registry_entry_v'+str(version)+'(entry_account.data()?)','emit(&mut expected_log,12);let _=entry_account.data()?;emit(&mut expected_log,14);let entry = raw_entry')
 expected=expected.replace('require_readonly_account(entry_account, &registry_program)?;','emit(&mut expected_log,13);require_readonly_account(entry_account, &registry_program)?;')
 # Replace each entire PDA expression with the SAME indexed arbitrary reply.
 pos=0;ordinal=0
 while True:
  i=expected.find('Pubkey::create_program_address(',pos)
  if i<0:break
  j=i+len('Pubkey::create_program_address(');depth=1
  while depth:
   if expected[j]=='(':depth+=1
   if expected[j]==')':depth-=1
   j+=1
  repl='{emit(&mut expected_log,'+str(30+ordinal)+');expected_log.pda+=1;pda_replies['+str(ordinal)+'].clone()}'
  expected=expected[:i]+repl+expected[j:];pos=i+len(repl);ordinal+=1
 size_r,size_e=(128,192) if version==1 else (256,320)
 setup='''let master=any_master();let master_account=&account::<1>();let registry_account=&account::<RS>();let entry_account=&account::<ES>();let verifier_program=&Pubkey::new_from_array(kani::any());let registry_program=Pubkey::new_from_array(registry_program_id());let current_slot:u64=kani::any();
 let rg=registryV();let en=entryV();let rok:bool=kani::any();let eok:bool=kani::any();
 let raw_registry=if rok{Ok(rg)}else{Err(aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError::WrongLength)};
 let raw_entry=if eok{Ok(en)}else{Err(aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError::WrongLength)};
 let pda_replies=[pda_reply(),pda_reply(),pda_reply(),pda_reply()];let mut log=Log{events:[0;16],n:0,pda:0};let mut expected_log=log;
'''.replace('RS',str(size_r)).replace('ES',str(size_e)).replace('registryV','registry'+str(version)).replace('entryV','entry'+str(version))
 if part=='entry':setup+='let loader=bpf_loader_upgradeable::id();'
 text=COMMON+HELPERS+defs+ANN+'fn stage(){'+setup+'let mut out=(||->ProgramResult{'+body+'})();let expected=(||->ProgramResult{'+expected+'})();'+('log.events[0]^=1;' if mode=='inverse' else '')+'assert!(out==expected&&log==expected_log,"complete versioned source-order branch all Result and error prefixes");}'
 mod='NLK_owned_chain'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),version=version,part=part,mode=mode,domain='arbitrary owned account/master records, all data errors, unconstrained full typed decoder success or WrongLength, all typed PDA replies and arbitrary slot; post-policy versioned branch',modifies='local output and full chronological call log; input accounts unchanged',limits='expected gate ordering transcribed from same source; native branch certificate only; child domains/full invocation not yet composed'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
