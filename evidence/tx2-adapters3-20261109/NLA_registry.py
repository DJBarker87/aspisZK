from NLA_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
# Native source-ordered comparison segments from the frozen parent, not probes.
FROZEN=subprocess.check_output(['git','show','4bb3b3f5:'+P],text=True)
WRAPPER=subprocess.check_output(['git','show','4bb3b3f5:programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
import ast,re
old=E.parent/'tx2-adapters-20261108/NKF_wrappers.py';tree=ast.parse(old.read_text())
COMMON=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMON' for t in n.targets))
COMMON+='''
use aspis_statement::pool_v1::{VerifierRegistryV1,VerifierRegistryV2,VerifierRegistryEntryV1,VerifierRegistryEntryV2,VerifierEntryStatusV1};
fn status()->VerifierEntryStatusV1{let s:u8=kani::any();kani::assume(s<4);match s{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}
fn registry1()->VerifierRegistryV1{VerifierRegistryV1{flags:kani::any(),bump:kani::any(),pool:kani::any(),authority:kani::any(),policy_binding:kani::any(),generation:kani::any(),minimum_activation_delay_slots:kani::any()}}
fn registry2()->VerifierRegistryV2{VerifierRegistryV2{flags:kani::any(),bump:kani::any(),pool:kani::any(),authority:kani::any(),policy_binding:kani::any(),generation:kani::any(),minimum_activation_delay_slots:kani::any(),registry_program:kani::any(),loader_program:kani::any(),programdata_address:kani::any(),programdata_bump:kani::any(),executable_hash:kani::any()}}
fn entry1()->VerifierRegistryEntryV1{VerifierRegistryEntryV1{status:status(),statement_version:kani::any(),bump:kani::any(),pool:kani::any(),verifier_program:kani::any(),profile_binding:kani::any(),release_binding:kani::any(),activation_slot:kani::any(),retirement_slot:kani::any(),policy_binding:kani::any()}}
fn entry2()->VerifierRegistryEntryV2{VerifierRegistryEntryV2{status:status(),statement_version:kani::any(),bump:kani::any(),pool:kani::any(),verifier_program:kani::any(),profile_binding:kani::any(),release_binding:kani::any(),loader_program:kani::any(),programdata_address:kani::any(),programdata_bump:kani::any(),executable_hash:kani::any(),expected_upgrade_authority:kani::any(),activation_slot:kani::any(),retirement_slot:kani::any(),policy_binding:kani::any()}}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
def block(condition_start,occ=0):
 matches=[m.start() for m in re.finditer(re.escape(condition_start),FROZEN)]
 start=matches[occ];opening=FROZEN.index('{',start);depth=1;end=opening+1
 while depth:
  if FROZEN[end]=='{':depth+=1
  if FROZEN[end]=='}':depth-=1
  end+=1
 return FROZEN[start:end]
def prefix(mode):
 start=FROZEN.index('    validate_verifier_policy_v1(',FROZEN.index('fn authenticate_invariant_release_registry'))
 end=FROZEN.index('    if immutable_deployment {',start)
 segment=FROZEN[start:end]
 setup="""let master=any_master();let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let registry_account=OwnedAccount{key,owner,is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Ok(Vec::new())};
 let registry_account=&registry_account;let mut suffix=0u8;
 """
 text=COMMON+ANN+'fn stage(){'+setup+'let mut result=(||->Result<bool,ProgramError>{'+segment+'suffix+=1;Ok(immutable_deployment)})();'
 text+=('result=if result.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(false)};' if mode=='inverse' else '')
 text+="""let policy=validate_verifier_policy_v1(&master.verifier_policy).map_err(|_|ProgramError::InvalidAccountData);
 let owner=Pubkey::new_from_array(registry_program_id());
 let expected=policy.and_then(|_|require_readonly_account(registry_account,&owner)).map(|_|master.verifier_policy.flags&POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT!=0);
 assert!(result==expected&&suffix==if expected.is_ok(){1}else{0},"ordered policy readonly choice Result and prefix");}"""
 return text,segment

def address(mode):
 # Common comparison at all four source sites. SAME typed account/reply; no value law for op38.
 segment=block('if registry_account.key() != &expected_registry',0)
 text=COMMON+ANN+"""fn stage(){
 let registry_account=OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Ok(Vec::new())};
 let expected_registry=Pubkey::new_from_array(kani::any());let mut suffix=0u8;
 let mut out=(||->ProgramResult{SEGMENT suffix+=1;Ok(())})();CORRUPT
 assert!(out==if registry_account.key()==&expected_registry{Ok(())}else{Err(ProgramError::InvalidAccountData)}&&suffix==if registry_account.key()==&expected_registry{1}else{0},"PDA address reply comparison and exact rejection prefix");}
 """.replace('SEGMENT',segment).replace('CORRUPT','out=if out.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};' if mode=='inverse' else '')
 return text,segment

def data(version,entry,field,mode):
 kind='entry' if entry else 'registry';ctor=kind+str(version);typ='VerifierRegistry'+('Entry' if entry else '')+'V'+str(version)
 function='decode_verifier_registry_'+('entry_' if entry else '')+'v'+str(version)
 receiver='entry_account' if entry else 'registry_account'
 start=FROZEN.index('let '+kind+' = '+function+'(')
 end=FROZEN.index(';',start)+1;segment=FROZEN[start:end]
 # Full unconstrained typed decoder reply via explicit constructors, all twelve errors.
 call=segment.replace(function+'(', 'oracle(').replace('.data()?)','.data()?,&mut log,coordinate,reply)')
 call=call.replace(receiver+'.data()', 'account.data()')
 text=COMMON+"""
 use aspis_statement::pool_v1::PoolV1VerifierRegistryFormatError as RF;
 fn error()->RF{let i:u8=kani::any();kani::assume(i<12);match i{0=>RF::WrongLength,1=>RF::WrongMagic,2=>RF::WrongVersion,3=>RF::NonZeroReserved,4=>RF::UnsupportedFlags,5=>RF::InvalidStatus,6=>RF::InvalidAuthorityMode,7=>RF::ZeroRequiredBinding,8=>RF::InvalidActivationDelay,9=>RF::InvalidStatementVersion,10=>RF::InvalidRetirementSlot,_=>RF::InvalidDeploymentMode}}
 struct Log{calls:u8,length:usize,byte:u8}
 fn oracle(bytes:&[u8],log:&mut Log,i:usize,reply:Result<TYP,RF>)->Result<TYP,RF>{log.calls+=1;log.length=bytes.len();log.byte=bytes[i];reply}
 """.replace('TYP',typ)+ANN+"""fn stage(){
 let bytes:[u8;32]=kani::any();let which:u8=kani::any();kani::assume(which<3);let coordinate:usize=kani::any();kani::assume(coordinate<32);
 let account=OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(32),bytes:match which{0=>Ok(bytes.to_vec()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)}};
 let raw=CTOR();let ok:bool=kani::any();let reply=if ok{Ok(raw)}else{Err(error())};let mut log=Log{calls:0,length:0,byte:0};let mut suffix=0u8;
 let mut out=(||->Result<TYP,ProgramError>{SEGMENT suffix+=1;Ok(KIND)})();CORRUPT
 let expected=if which==1{Err(ProgramError::AccountBorrowFailed)}else if which==2||!ok{Err(ProgramError::InvalidAccountData)}else{Ok(raw)};
 assert!(PROPERTY,"ordered data decoder field and exact error prefix");}
 """.replace('TYP',typ).replace('CTOR',ctor).replace('SEGMENT',call).replace('KIND',kind)
 props=['out==expected&&suffix==if which==0&&ok{1}else{0}','if which==0{log.calls==1&&log.length==32&&log.byte==bytes[coordinate]}else{log.calls==0}']
 corrupt=['out=if out.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(raw)};','log.calls^=1;']
 return text.replace('PROPERTY',props[field]).replace('CORRUPT',corrupt[field] if mode=='inverse' else ''),segment

def readonly_data(mode):
 segment='require_readonly_account(&account,&owner)?;\nlet data=account.data()?;'
 text=COMMON+ANN+"""fn stage(){let bytes:[u8;32]=kani::any();let coordinate:usize=kani::any();kani::assume(coordinate<32);let tag:u8=kani::any();kani::assume(tag<3);
 let account=OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(32),bytes:match tag{0=>Ok(bytes.to_vec()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)}};
 let owner=Pubkey::new_from_array(kani::any());let mut data_entered=0u8;let mut suffix=0u8;
 let mut out=(||->Result<u8,ProgramError>{require_readonly_account(&account,&owner)?;data_entered+=1;let data=account.data()?;suffix+=1;Ok(data[coordinate])})();CORRUPT
 let readonly=require_readonly_account(&account,&owner);let readonly_ok=readonly.is_ok();let expected=readonly.and_then(|_|account.data()).map(|data|data[coordinate]);
 assert!(out==expected&&data_entered==if readonly_ok{1}else{0}&&suffix==if expected.is_ok(){1}else{0},"readonly precedes data; each error stops exact suffix");}
 """.replace('CORRUPT','data_entered^=1;' if mode=='inverse' else '')
 return text,segment

def attempt(a,part,mode,version=1,entry=False,field=0):
 text,segment= data(version,entry,field,mode) if part=='data' else globals()[part](mode)
 mod='NLA_registry'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(part=part,source=P,segment=segment,segment_sha256=sha(segment.encode()),version=version,entry=entry,field=field,mode=mode,domain='arbitrary typed prestate; data shape observes a32-byte allocation window only, general byte-window frame remains required',modifies='local record only',status='support only until complete chain and same-call domains'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
