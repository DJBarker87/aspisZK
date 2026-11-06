from NJY_native import *
from NJY_segments import arr,word
import sys,re
P='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'
raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
def body(f):
 st=raw.index('pub fn '+f+'(');start=raw.index('{',st)+1;level=1;i=start
 while level:level+=(raw[i]=='{')-(raw[i]=='}');i+=1
 return raw[start:i-1]
q=''.join(l[1:]+'\n' for l in (Q/'NJQ_constructors.patch').read_text().splitlines() if l.startswith('+') and not l.startswith('+++'))
helpers=q[q.index('use crate::pool_v1::format'):q.index('fn view_i')]
helpers+='''fn digest()->[aspis_core::field::M31;8]{let r:[u32;8]=kani::any();[aspis_core::field::M31(r[0]),aspis_core::field::M31(r[1]),aspis_core::field::M31(r[2]),aspis_core::field::M31(r[3]),aspis_core::field::M31(r[4]),aspis_core::field::M31(r[5]),aspis_core::field::M31(r[6]),aspis_core::field::M31(r[7])]}
fn digest_reply()->Result<[aspis_core::field::M31;8],crate::atomic_statement::AtomicStatementError>{use crate::atomic_statement::AtomicStatementError as A;let t:u8=kani::any();kani::assume(t<8);match t{0=>Err(A::NonCanonicalDigest),1=>Err(A::NonCanonicalAssetId),2=>Err(A::FeeOutOfRange),3=>Err(A::PathDepthMismatch),4=>Err(A::InsertionIndexOutOfRange),5=>Err(A::CurrentAnchorMismatch),6=>Err(A::OutputAnchorMismatch),_=>Ok(digest())}}
'''
def make(family,kind):
 cp=family=='checkpoint';width=192 if cp else 384;func='decode_pool_v1_pair_forest_'+family+'_v1';b=body(func)
 params='bytes:&[u8]';args='bytes';req='bytes.len()=='+str(width);harness='let bytes:[u8;'+str(width)+']=kani::any();let _=segment(&bytes);';trans=[]
 if kind=='length':
  native=b[:b.index('    if bytes[..4]')].replace('bytes.len()','n')+'Ok(())';reference='if n=='+str(width)+'{Ok(())}else{Err(F::WrongLength)}';params='n:usize';args='n';req='true';ret='Result<(),F>';harness='let n:usize=kani::any();let _=segment(n);';trans=['bytes.len() -> scalar n, first guard only']
 elif kind=='head':
  end=b.index('    let global_root =') if cp else b.index('    let identity =')
  native=b[:end].replace('bytes[176..].iter().any(|byte| *byte != 0)' if cp else 'bytes[50..64].iter().any(|byte| *byte != 0)','any_reply')
  native+='Ok((master,deployment_domain))' if cp else 'Ok(has_checkpoint)'
  ret='Result<([u8;32],[u8;32]),F>' if cp else 'Result<bool,F>'
  params+=',any_reply:bool';args+=',any_reply';harness='let bytes:[u8;'+str(width)+']=kani::any();let any_reply:bool=kani::any();let _=segment(&bytes,any_reply);'
  reference='if bytes[..4]!='+('POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC' if cp else 'POOL_V1_PAIR_FOREST_MASTER_MAGIC')+'{return Err(F::WrongMagic)}if bytes[4]!=2{return Err(F::WrongVersion)}if bytes[5]!=8{return Err(F::WrongLaneCount)}if bytes[6]!=1{return Err(F::WrongDigestEncoding)}'
  if cp:reference+='if any_reply{return Err(F::NonZeroReserved)}let master='+arr(8)+';let domain='+arr(40)+';if master==[0;32]||domain==[0;32]{Err(F::ZeroRequiredBinding)}else{Ok((master,domain))}'
  else:reference+='if any_reply||bytes[312..320]!=[0;8]{return Err(F::NonZeroReserved)}if bytes[8..40]!=POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING{return Err(F::WrongFormatBinding)}match bytes[49]{0=>Ok(false),1=>Ok(true),_=>Err(F::InvalidBoolean)}'
  trans=['Iterator.any cut reply; NJQ rule-3 any law instantiated on exact finite immutable window; append exact live values']
 elif kind.endswith('_arg'):
  start,n={'digest_arg':(80,32),'identity_arg':(64,144),'policy_arg':(208,104)}[kind]
  expr={'digest_arg':'bytes[CHECKPOINT_GLOBAL_ROOT_OFFSET..CHECKPOINT_LANE_SEQUENCES_OFFSET]','identity_arg':'&bytes[MASTER_IDENTITY_OFFSET..MASTER_POLICY_OFFSET]','policy_arg':'&bytes[MASTER_POLICY_OFFSET..312]'}[kind]
  # Fixed-array view of the exact source argument slice. The original call borrows
  # identity/policy slices; the 144/104-byte arrays express their values only.
  native='('+expr+').try_into().unwrap()';reference=arr(start,n);ret='[u8;'+str(n)+']';trans=['exact child input range, fixed-array value port; immutable borrowing frame retained']
 elif kind.endswith('_map'):
  if kind=='digest_map':rtype='[aspis_core::field::M31;8]';err='crate::atomic_statement::AtomicStatementError';mapper='NonCanonicalDigest';maker='digest_reply()'
  elif kind=='identity_map':rtype='I';err='E';mapper='Identity';maker='id_reply()'
  else:rtype='P';err='E';mapper='Policy';maker='policy_reply()'
  ret='Result<'+rtype+',F>';params='reply:Result<'+rtype+','+err+'>';args='reply';req='true';native='let value=reply.map_err(|_|PoolV1PairForestAccountErrorV1::'+mapper+')?;Ok(value)';reference='match reply{Ok(v)=>Ok(v),Err(_)=>Err(F::'+mapper+')}';harness='let reply='+maker+';let _=segment(reply);';trans=['child call replaced by universally quantified complete Result; source map_err and ? retained']
 elif kind=='step':
  offset='CHECKPOINT_LANE_SEQUENCES_OFFSET' if cp else 'MASTER_LAST_SEQUENCES_OFFSET';start=112 if cp else 320
  loop_start=b.index('        let start = '+offset);loop_end=b.index('\n    }',loop_start);snippet=b[loop_start:loop_end]
  native='let mut lanes=before;let sequence=&mut lanes[lane];\n'+snippet+'\nOk(lanes)'
  values=','.join('(if lane=='+str(i)+'{'+word(start+8*i)+'}else{before['+str(i)+']})' for i in range(8))
  reference=('let value='+word(start)+';' if False else '')
  val='u64::from_le_bytes([bytes['+str(start)+'+8*lane],bytes['+str(start+1)+'+8*lane],bytes['+str(start+2)+'+8*lane],bytes['+str(start+3)+'+8*lane],bytes['+str(start+4)+'+8*lane],bytes['+str(start+5)+'+8*lane],bytes['+str(start+6)+'+8*lane],bytes['+str(start+7)+'+8*lane]])'
  reference='let value='+val+';'+('if value>POOL_V1_PAIR_CAPACITY{return Err(F::InvalidMasterState)}' if cp else '')+'Ok(['+','.join('if lane=='+str(i)+'{value}else{before['+str(i)+']}' for i in range(8))+'])'
  ret='Result<[u64;8],F>';params='bytes:&[u8],lane:usize,before:[u64;8]';args='bytes,lane,before';req+='&&lane<8';harness='let bytes:[u8;'+str(width)+']=kani::any();let lane:usize=kani::any();kani::assume(lane<8);let before:[u64;8]=kani::any();let _=segment(&bytes,lane,before);';trans=['one exact native iteration; arbitrary pre-state, exclusive head lens; no whole-buffer loop']
 elif kind=='constructor':
  if cp:
   native=b[b.index('    Ok(PoolV1PairForestCheckpointV1 {'):]
   ret='Result<PoolV1PairForestCheckpointV1,F>';params+=',master:[u8;32],deployment_domain:[u8;32],global_root:[aspis_core::field::M31;8],lane_sequences:[u64;8]';args+=',master,deployment_domain,global_root,lane_sequences';reference='Ok(PoolV1PairForestCheckpointV1{bump:bytes[7],master,deployment_domain,checkpoint_sequence:'+word(72)+',global_root,lane_sequences})';harness='let bytes:[u8;192]=kani::any();let master:[u8;32]=kani::any();let deployment_domain:[u8;32]=kani::any();let global_root=digest();let lane_sequences:[u64;8]=kani::any();let _=segment(&bytes,master,deployment_domain,global_root,lane_sequences);'
  else:
   native=b[b.index('    let master = PoolV1PairForestMasterV1 {'):].replace('validate_master(&master)?;','reply?;')
   ret='Result<PoolV1PairForestMasterV1,F>';params+=',identity:I,verifier_policy:P,has_checkpoint:bool,last_checkpoint_lane_sequences:[u64;8],reply:Result<(),F>';args+=',identity,verifier_policy,has_checkpoint,last_checkpoint_lane_sequences,reply';reference='let master=PoolV1PairForestMasterV1{bump:bytes[7],identity,verifier_policy,initialized_lane_mask:bytes[48],has_checkpoint,next_checkpoint_sequence:'+word(40)+',last_checkpoint_lane_sequences};match reply{Ok(())=>Ok(master),Err(e)=>Err(e)}';harness='let bytes:[u8;384]=kani::any();let identity=identity();let verifier_policy=policy();let has_checkpoint:bool=kani::any();let last_checkpoint_lane_sequences:[u64;8]=kani::any();let reply=account_reply();let _=segment(&bytes,identity,verifier_policy,has_checkpoint,last_checkpoint_lane_sequences,reply);'
  trans=['exact complete constructor; parameters are prior live values; master validator full Result cut at same record' if not cp else 'exact complete constructor; arbitrary prior values and unchanged source sequence read']
 else:raise ValueError(kind)
 module='NJY_'+family+'_'+kind
 text='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'+helpers
 text+='fn reference('+params+')->'+ret+'{'+reference+'}\n#[kani::requires('+req+')]\n#[kani::ensures(|r| (*r==reference('+args+'))!=cfg!(NJY_invert))]\n#[kani::modifies()]\nfn segment('+params+')->'+ret+'{'+native+'}\n#[kani::proof_for_contract(segment)]\n#[kani::unwind(193)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn segment_contract(){'+harness+'}\n'
 (E/(module+'_SOURCE.json')).write_text(json.dumps(dict(parent=P,frozen_function=func,frozen_body_sha256=sha(b.encode()),kind=kind,native_segment_sha256=sha(native.encode()),transformations=trans),indent=1)+'\n')
 return module,text
if __name__=='__main__':
 a,f,k,mode=sys.argv[1:];module,text=make(f,k)
 (E/(module+'_'+mode+'.patch')).write_text('--- /dev/null\n+++ b/'+str(Path(P).parent/(module+'.rs'))+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines()))
 submit(a,'pool_v1::pair_forest_accounts::'+module+'::segment_contract',P,module,text,mode)
