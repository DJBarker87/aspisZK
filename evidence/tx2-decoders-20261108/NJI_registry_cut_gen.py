from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/verifier_registry.rs'],text=True)
errors=['WrongLength','WrongMagic','WrongVersion','NonZeroReserved','UnsupportedFlags','InvalidStatus','InvalidAuthorityMode','ZeroRequiredBinding','InvalidActivationDelay','InvalidStatementVersion','InvalidRetirementSlot','InvalidDeploymentMode']
for name,size,record in [('registry',128,'VerifierRegistryV1'),('entry',192,'VerifierRegistryEntryV1')]:
 f='decode_verifier_registry_'+('v1' if name=='registry' else 'entry_v1');a=s.index('pub fn '+f+'(');start=s.index('{',a);depth=1;end=start+1
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 body=s[start:end];v=name;old='validate_verifier_registry_'+('v1' if name=='registry' else 'entry_v1')+'(&'+v+')?;';assert body.count(old)==1
 replacement='*log=Some('+v+'); reply?;';stage=body.replace(old,replacement)
 text='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\ntype F=PoolV1VerifierRegistryFormatError;\n'
 text+='fn stage(bytes:&[u8],reply:Result<(),F>,log:&mut Option<'+record+'>)->Result<'+record+',F> '+stage+'\n'
 text+='fn oracle()->Result<(),F>{let t:u8=kani::any();kani::assume(t<13);match t{0=>Ok(()),'+','.join(str(i+1)+'=>Err(F::'+e+')' for i,e in enumerate(errors[:-1]))+',_=>Err(F::'+errors[-1]+')}}\n'
 text+='#[derive(Debug,PartialEq,Eq)] enum Obs{Byte(u8),Word(u64),Status(VerifierEntryStatusV1)}\n'
 fields=([('flags','b[5]','Byte'),('bump','b[6]','Byte'),('pool[i]','b[8+i]','Byte'),('authority[i]','b[40+i]','Byte'),('policy_binding[i]','b[72+i]','Byte'),('generation','word(b,104)','Word'),('minimum_activation_delay_slots','word(b,112)','Word')] if name=='registry' else [('status','status(b[5])','Status'),('statement_version','b[6]','Byte'),('bump','b[7]','Byte'),('pool[i]','b[8+i]','Byte'),('verifier_program[i]','b[40+i]','Byte'),('profile_binding[i]','b[72+i]','Byte'),('release_binding[i]','b[104+i]','Byte'),('activation_slot','word(b,136)','Word'),('retirement_slot','word(b,144)','Word'),('policy_binding[i]','b[152+i]','Byte')])
 text+='fn view(p:&'+record+',f:usize,i:usize)->Obs{match f{'+','.join(str(j)+'=>Obs::'+kind+'(p.'+field+')' for j,(field,expected,kind) in enumerate(fields[:-1]))+',_=>Obs::'+fields[-1][2]+'(p.'+fields[-1][0]+')}}\n'
 text+='fn expected(b:&[u8],f:usize,i:usize)->Obs{match f{'+','.join(str(j)+'=>Obs::'+kind+'('+expected+')' for j,(field,expected,kind) in enumerate(fields[:-1]))+',_=>Obs::'+fields[-1][2]+'('+fields[-1][1]+')}}\n'
 text+='fn word(b:&[u8],a:usize)->u64{u64::from_le_bytes([b[a],b[a+1],b[a+2],b[a+3],b[a+4],b[a+5],b[a+6],b[a+7]])}\n'
 text+='fn status(t:u8)->VerifierEntryStatusV1{match t{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}\n'
 magic='POOL_V1_VERIFIER_'+('REGISTRY_MAGIC' if name=='registry' else 'ENTRY_MAGIC');version=magic.replace('MAGIC','VERSION')
 reserved='b[7]!=0||b[120..128]!=[0;8]' if name=='registry' else 'b[184..192]!=[0;8]'
 error='if b[..4]!='+magic+'{Some(F::WrongMagic)}else if b[4]!='+version+'{Some(F::WrongVersion)}else if '+reserved+'{Some(F::NonZeroReserved)}'+('else if b[5]>3{Some(F::InvalidStatus)}' if name=='entry' else '')+'else{None}'
 text+='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){let b:[u8;SIZE]=kani::any();let reply=oracle();let mut log=None;let out=stage(&b,reply,&mut log);let i:usize=kani::any();kani::assume(i<32);let f:usize=kani::any();kani::assume(f<FIELDS);
 let error=ERROR;
 match error{Some(e)=>{assert!(log.is_none());assert!(matches!(out,Err(a) if a==e));},None=>{let p=log.expect("child entered");assert!((view(&p,f,i)==expected(&b,f,i))!=cfg!(NJI_invert));match reply{Err(e)=>assert!(matches!(out,Err(a) if a==e)),Ok(())=>{let p=out.expect("child success");assert!(view(&p,f,i)==expected(&b,f,i));}}}}
}
'''.replace('SIZE',str(size)).replace('FIELDS',str(len(fields))).replace('ERROR',error)
 (E/('NJI_'+name+'_cut.rs')).write_text(text)
 (E/('NJI_'+name.upper()+'_CUT_FIDELITY.json')).write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',function=f,frozen_file='crates/aspis-statement/src/pool_v1/verifier_registry.rs',source_file_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),stage_sha256=hashlib.sha256(text.encode()).hexdigest(),replacement=dict(old=old,new=replacement),erasure_restores_exact_body=stage.replace(replacement,old)==body,fields=fields),indent=2))
