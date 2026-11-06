"""Source-ordered exact frozen segments; generated manifests fix every byte range."""
from NJY_native import *
import sys,re
F='PoolV1VerifierRegistryFormatError'
P='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
def arr(off,n=32):return '['+','.join('bytes['+str(i)+']' for i in range(off,off+n))+']'
def word(off):return 'u64::from_le_bytes('+arr(off,8)+')'
def body(f):
 st=raw.index('pub fn '+f+'(');start=raw.index('{',st)+1;level=1;i=start
 while level:
  level+=(raw[i]=='{')-(raw[i]=='}');i+=1
 return raw[start:i-1]
def make(family,kind):
 entry=family=='entry';width=192 if entry else 128;record='VerifierRegistryEntryV1' if entry else 'VerifierRegistryV1';func='decode_verifier_registry_entry_v1' if entry else 'decode_verifier_registry_v1';local='entry' if entry else 'registry'
 b=body(func);cut=b.index('    let '+local+' = ');end=b.index('    validate_verifier_registry',cut)
 head=b[:cut];ctor=b[cut:end]
 fields={'flags':'bytes[5]','bump':'bytes[6]','pool':arr(8),'authority':arr(40),'policy_binding':arr(72),'generation':word(104),'minimum_activation_delay_slots':word(112)}
 if entry:fields={'status':'status','statement_version':'bytes[6]','bump':'bytes[7]','pool':arr(8),'verifier_program':arr(40),'profile_binding':arr(72),'release_binding':arr(104),'activation_slot':word(136),'retirement_slot':word(144),'policy_binding':arr(152)}
 vals=','.join(k+':'+v for k,v in fields.items())
 pre=''
 if entry:pre='let status=match bytes[5]{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,3=>VerifierEntryStatusV1::Retired,_=>return Err(F::InvalidStatus)};'
 h_ref='''if bytes[..4]!=MAGIC{return Err(F::WrongMagic)}if bytes[4]!=2{return Err(F::WrongVersion)}if RESERVED{return Err(F::NonZeroReserved)}Ok(())'''.replace('MAGIC','POOL_V1_VERIFIER_ENTRY_MAGIC' if entry else 'POOL_V1_VERIFIER_REGISTRY_MAGIC').replace('RESERVED','bytes[184..192]!=[0;8]' if entry else 'bytes[7]!=0||bytes[120..128]!=[0;8]')
 if kind=='head':
  native=head+'    Ok(())\n';reference=h_ref;ret='Result<(),F>';params='bytes:&[u8]';req='bytes.len()=='+str(width);args='bytes';harness='let bytes:[u8;'+str(width)+']=kani::any();let _=segment(&bytes);'
 elif kind=='constructor':
  native=ctor+'    Ok('+local+')\n';reference=pre+'Ok('+record+'{'+vals+'})';ret='Result<'+record+',F>';params='bytes:&[u8]';req='bytes.len()=='+str(width);args='bytes';harness='let bytes:[u8;'+str(width)+']=kani::any();let _=segment(&bytes);'
 elif kind=='suffix':
  native='    reply?;\n    Ok('+local+')\n';reference='match reply{Ok(())=>Ok('+local+'),Err(e)=>Err(e)}';ret='Result<'+record+',F>';params=local+':'+record+',reply:Result<(),F>';req='true';args=local+',reply'
  arbs=','.join(k+':'+('match kani::any::<u8>()%4{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}' if k=='status' else 'kani::any()') for k in fields)
  harness='let '+local+'='+record+'{'+arbs+'};let t:u8=kani::any();kani::assume(t<13);let reply=reply(t);let _=segment('+args+');'
 elif kind=='length':
  native=head[:head.index('    if bytes[..4]')].replace('bytes.len()','n')+'    Ok(())\n';reference='if n=='+str(width)+'{Ok(())}else{Err(F::WrongLength)}';ret='Result<(),F>';params='n:usize';req='true';args='n';harness='let n:usize=kani::any();let _=segment(n);'
 else:raise ValueError(kind)
 errors=['WrongLength','WrongMagic','WrongVersion','NonZeroReserved','UnsupportedFlags','InvalidStatus','InvalidAuthorityMode','ZeroRequiredBinding','InvalidActivationDelay','InvalidStatementVersion','InvalidRetirementSlot','InvalidDeploymentMode']
 text='use super::*;\ntype F='+F+';\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
 text+='fn reply(t:u8)->Result<(),F>{match t{'+','.join(str(i)+'=>Err(F::'+e+')' for i,e in enumerate(errors))+',_=>Ok(())}}\n'
 text+='fn reference('+params+')->'+ret+'{'+reference+'}\n'
 text+='#[kani::requires('+req+')]\n#[kani::ensures(|r| (*r==reference('+args+'))!=cfg!(NJY_invert))]\n#[kani::modifies()]\nfn segment('+params+')->'+ret+'{'+native+'}\n'
 text+='#[kani::proof_for_contract(segment)]\n#[kani::unwind(193)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn segment_contract(){'+harness+'}\n'
 module='NJY_'+family+'_'+kind
 manifest=dict(parent=P,frozen_function=func,frozen_function_body_sha256=sha(b.encode()),kind=kind,native_segment_sha256=sha(native.encode()),source_prefix_sha256=sha(head.encode()),source_constructor_sha256=sha(ctor.encode()),source_suffix=b[end:],transformations={'head':'append Ok(()), requires fixed width (separate length segment covers every usize)','constructor':'exact let record source; append Ok(record); requires fixed width (no header success needed)','suffix':'child invocation replaced by universally quantified full Result reply, instantiated by CLOSED child; remaining question-mark and Ok(record) literal','length':'first guard only, bytes.len() replaced by scalar n; append Ok(())'}[kind])
 (E/(module+'_SOURCE.json')).write_text(json.dumps(manifest,indent=1)+'\n')
 return module,text
if __name__=='__main__':
 a,f,k,mode=sys.argv[1:];module,text=make(f,k)
 (E/(module+'_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/'+str(Path(P).parent/(module+'.rs'))+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines()))
 submit(a,'pool_v1::verifier_registry::'+module+'::segment_contract',P,module,text,mode)
