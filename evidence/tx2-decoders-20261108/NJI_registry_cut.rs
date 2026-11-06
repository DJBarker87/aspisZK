use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type F=PoolV1VerifierRegistryFormatError;
fn stage(bytes:&[u8],reply:Result<(),F>,log:&mut Option<VerifierRegistryV1>)->Result<VerifierRegistryV1,F> {
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != 0 || bytes[120..128] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV1 {
        flags: bytes[5],
        bump: bytes[6],
        pool: bytes[8..40].try_into().unwrap(),
        authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
        generation: u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
        minimum_activation_delay_slots: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
    };
    *log=Some(registry); reply?;
    Ok(registry)
}
fn oracle()->Result<(),F>{let t:u8=kani::any();kani::assume(t<13);match t{0=>Ok(()),1=>Err(F::WrongLength),2=>Err(F::WrongMagic),3=>Err(F::WrongVersion),4=>Err(F::NonZeroReserved),5=>Err(F::UnsupportedFlags),6=>Err(F::InvalidStatus),7=>Err(F::InvalidAuthorityMode),8=>Err(F::ZeroRequiredBinding),9=>Err(F::InvalidActivationDelay),10=>Err(F::InvalidStatementVersion),11=>Err(F::InvalidRetirementSlot),_=>Err(F::InvalidDeploymentMode)}}
#[derive(Debug,PartialEq,Eq)] enum Obs{Byte(u8),Word(u64),Status(VerifierEntryStatusV1)}
fn view(p:&VerifierRegistryV1,f:usize,i:usize)->Obs{match f{0=>Obs::Byte(p.flags),1=>Obs::Byte(p.bump),2=>Obs::Byte(p.pool[i]),3=>Obs::Byte(p.authority[i]),4=>Obs::Byte(p.policy_binding[i]),5=>Obs::Word(p.generation),_=>Obs::Word(p.minimum_activation_delay_slots)}}
fn expected(b:&[u8],f:usize,i:usize)->Obs{match f{0=>Obs::Byte(b[5]),1=>Obs::Byte(b[6]),2=>Obs::Byte(b[8+i]),3=>Obs::Byte(b[40+i]),4=>Obs::Byte(b[72+i]),5=>Obs::Word(word(b,104)),_=>Obs::Word(word(b,112))}}
fn word(b:&[u8],a:usize)->u64{u64::from_le_bytes([b[a],b[a+1],b[a+2],b[a+3],b[a+4],b[a+5],b[a+6],b[a+7]])}
fn status(t:u8)->VerifierEntryStatusV1{match t{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){let b:[u8;128]=kani::any();let frame_i:usize=kani::any();kani::assume(frame_i<128);let original=b[frame_i];let reply=oracle();let mut log=None;let out=stage(&b,reply,&mut log);assert!(b[frame_i]==original);let i:usize=kani::any();kani::assume(i<32);let f:usize=kani::any();kani::assume(f<7);
 let error=if b[..4]!=POOL_V1_VERIFIER_REGISTRY_MAGIC{Some(F::WrongMagic)}else if b[4]!=POOL_V1_VERIFIER_REGISTRY_VERSION{Some(F::WrongVersion)}else if b[7]!=0||b[120..128]!=[0;8]{Some(F::NonZeroReserved)}else{None};
 match error{Some(e)=>{assert!(log.is_none());assert!(matches!(out,Err(a) if a==e));},None=>{let p=log.expect("child entered");assert!((view(&p,f,i)==expected(&b,f,i))!=cfg!(NJI_invert));match reply{Err(e)=>assert!(matches!(out,Err(a) if a==e)),Ok(())=>{let p=out.expect("child success");assert!(view(&p,f,i)==expected(&b,f,i));}}}}
}
