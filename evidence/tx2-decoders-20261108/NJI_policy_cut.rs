use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type F=PoolV1FormatError;
fn stage(bytes:&[u8],reply:Result<(),F>,log:&mut Option<VerifierPolicyV1>)->Result<VerifierPolicyV1,F> {
    if bytes.len() != POOL_V1_VERIFIER_POLICY_BYTES {
        return Err(PoolV1FormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_POLICY_MAGIC {
        return Err(PoolV1FormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_POLICY_VERSION {
        return Err(PoolV1FormatError::WrongVersion);
    }
    if bytes[6..8] != [0u8; 2] {
        return Err(PoolV1FormatError::NonZeroReserved);
    }
    let policy = VerifierPolicyV1 {
        flags: bytes[5],
        registry_program: bytes[8..40].try_into().unwrap(),
        registry_authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
    };
    *log=Some(policy); reply?;
    Ok(policy)
}
fn oracle()->Result<(),F>{let t:u8=kani::any();kani::assume(t<9);match t{0=>Ok(()),1=>Err(F::WrongLength),2=>Err(F::WrongMagic),3=>Err(F::WrongVersion),4=>Err(F::NonZeroReserved),5=>Err(F::NonCanonicalAssetId),6=>Err(F::UnsupportedFlags),7=>Err(F::ZeroRequiredBinding),_=>Err(F::InvalidAuthorityMode)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){
 let b:[u8;104]=kani::any();let frame_i:usize=kani::any();kani::assume(frame_i<104);let original=b[frame_i];let reply=oracle();let mut log=None;
 let out=stage(&b,reply,&mut log);assert!(b[frame_i]==original);let i:usize=kani::any();kani::assume(i<32);
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
