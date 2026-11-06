from NKP_native import *
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
def shape(part,mode):
 setup='''let master=any_master();let pool_program=Pubkey::new_from_array(kani::any());let verifier_program=Pubkey::new_from_array(kani::any());
 let master_key=Pubkey::new_from_array(kani::any());let master_account=OwnedAccount{key:master_key,owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Ok(Vec::new())};
 let registry_program=Pubkey::new_from_array(kani::any());let loader=Pubkey::new_from_array(kani::any());let registry_programdata=Pubkey::new_from_array(kani::any());let verifier_programdata=Pubkey::new_from_array(kani::any());let current_slot:u64=kani::any();
'''
 if part=='metadata':
  segment=block('if pool_program.to_bytes()')
  condition=segment[3:segment.index('{')].strip()
  # Policy and readonly are kept in the NEXT native cut, not silently asserted here.
 elif part.startswith('registry'):
  v=int(part[-1]);setup+=f'let registry=registry{v}();\n'
  segment=block('if registry.pool != master_account.key().to_bytes()',0 if v==2 else 1)
  condition=segment[3:segment.index('{')].strip()
 elif part.startswith('entry'):
  v=int(part[-1]);setup+=f'let entry=entry{v}();\n'
  segment=block('if entry.pool != master_account.key().to_bytes()',0 if v==2 else 1)
  condition=segment[3:segment.index('{')].strip()
 else:raise ValueError(part)
 # Extracted segment's indentation/closing brace are preserved exactly;
 # the rest is local harness setup/observation, all payloads unrestricted.
 text=COMMON+ANN+'fn stage(){\n'+setup+'let mut result=(||->ProgramResult{\n'+segment+'\nOk(())})();\n'
 if mode=='inverse':text+='result=if result.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};\n'
 text+='let expected=!('+condition+');\nassert!(if expected{matches!(result,Ok(()))}else{matches!(result,Err(ProgramError::InvalidAccountData))},"registry ordered comparison stage exact Result");\n}\n'
 return text,segment

def attempt(a,part,mode):
 text,segment=shape(part,mode);mod='NKP_registry'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(part=part,source=P,segment=segment,segment_sha256=sha(segment.encode()),exact_frozen_substring=segment in FROZEN,mode=mode,domain='arbitrary complete typed prestate at named comparison boundary; no success premise',modifies=[],next='source-ordered data/decoder/PDA relay still required; op38 value free'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
