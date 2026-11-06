from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/format.rs'],text=True)
a=s.index('pub fn decode_verifier_policy_v1(');start=s.index('{',a);depth=1;end=start+1
while depth:
 depth += (s[end]=='{')-(s[end]=='}');end+=1
body=s[start:end];old='validate_verifier_policy_v1(&policy)?;';assert body.count(old)==1
modified=body.replace(old,'*log=Some(policy); reply?;')
head='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\ntype F=PoolV1FormatError;\nfn stage(bytes:&[u8],reply:Result<(),F>,log:&mut Option<VerifierPolicyV1>)->Result<VerifierPolicyV1,F> '
source=head+modified+"\n"+r'''fn oracle()->Result<(),F>{let t:u8=kani::any();kani::assume(t<9);match t{0=>Ok(()),1=>Err(F::WrongLength),2=>Err(F::WrongMagic),3=>Err(F::WrongVersion),4=>Err(F::NonZeroReserved),5=>Err(F::NonCanonicalAssetId),6=>Err(F::UnsupportedFlags),7=>Err(F::ZeroRequiredBinding),_=>Err(F::InvalidAuthorityMode)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){
 let b:[u8;104]=kani::any();let reply=oracle();let mut log=None;
 let out=stage(&b,reply,&mut log);let i:usize=kani::any();kani::assume(i<32);
 let live=b[..4]==POOL_V1_VERIFIER_POLICY_MAGIC && b[4]==POOL_V1_VERIFIER_POLICY_VERSION && b[6]==0 && b[7]==0;
 if live{
  let p=log.expect("child entered");
  assert!((p.flags==b[5])!=cfg!(NJI_invert));
  assert!(p.registry_program[i]==b[8+i]);assert!(p.registry_authority[i]==b[40+i]);assert!(p.policy_binding[i]==b[72+i]);
  match reply{Err(e)=>assert!(matches!(out,Err(a) if a==e)),Ok(())=>{
   let p=out.expect("child success");assert!(p.flags==b[5]);assert!(p.registry_program[i]==b[8+i]);assert!(p.registry_authority[i]==b[40+i]);assert!(p.policy_binding[i]==b[72+i]);
  }}
 }else{
  assert!(log.is_none());
  let e=if b[..4]!=POOL_V1_VERIFIER_POLICY_MAGIC{F::WrongMagic}else if b[4]!=POOL_V1_VERIFIER_POLICY_VERSION{F::WrongVersion}else{F::NonZeroReserved};
  assert!(matches!(out,Err(a) if a==e));
 }
}
'''
(E/'NJI_policy_cut.rs').write_text(source)
(E/'NJI_POLICY_CUT_FIDELITY.json').write_text(json.dumps(dict(frozen_file='crates/aspis-statement/src/pool_v1/format.rs',frozen_body_sha256=hashlib.sha256(s[a:end].encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),stage_sha256=hashlib.sha256(source.encode()).hexdigest(),replacement=dict(old=old,new='*log=Some(policy); reply?;'),erasure_restores_exact_body=modified.replace('*log=Some(policy); reply?;',old)==body),indent=2))
