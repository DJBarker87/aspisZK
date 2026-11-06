use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type F=PoolV1VerifierRegistryFormatError;
fn stage(bytes:&[u8],reply:Result<(),F>,log:&mut Option<VerifierRegistryEntryV1>)->Result<VerifierRegistryEntryV1,F> {
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[184..192] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::try_from(bytes[5])?,
        statement_version: bytes[6],
        bump: bytes[7],
        pool: bytes[8..40].try_into().unwrap(),
        verifier_program: bytes[40..72].try_into().unwrap(),
        profile_binding: bytes[72..104].try_into().unwrap(),
        release_binding: bytes[104..136].try_into().unwrap(),
        activation_slot: u64::from_le_bytes(bytes[136..144].try_into().unwrap()),
        retirement_slot: u64::from_le_bytes(bytes[144..152].try_into().unwrap()),
        policy_binding: bytes[152..184].try_into().unwrap(),
    };
    *log=Some(entry); reply?;
    Ok(entry)
}
fn oracle()->Result<(),F>{let t:u8=kani::any();kani::assume(t<13);match t{0=>Ok(()),1=>Err(F::WrongLength),2=>Err(F::WrongMagic),3=>Err(F::WrongVersion),4=>Err(F::NonZeroReserved),5=>Err(F::UnsupportedFlags),6=>Err(F::InvalidStatus),7=>Err(F::InvalidAuthorityMode),8=>Err(F::ZeroRequiredBinding),9=>Err(F::InvalidActivationDelay),10=>Err(F::InvalidStatementVersion),11=>Err(F::InvalidRetirementSlot),_=>Err(F::InvalidDeploymentMode)}}
#[derive(Debug,PartialEq,Eq)] enum Obs{Byte(u8),Word(u64),Status(VerifierEntryStatusV1)}
fn view(p:&VerifierRegistryEntryV1,f:usize,i:usize)->Obs{match f{0=>Obs::Status(p.status),1=>Obs::Byte(p.statement_version),2=>Obs::Byte(p.bump),3=>Obs::Byte(p.pool[i]),4=>Obs::Byte(p.verifier_program[i]),5=>Obs::Byte(p.profile_binding[i]),6=>Obs::Byte(p.release_binding[i]),7=>Obs::Word(p.activation_slot),8=>Obs::Word(p.retirement_slot),_=>Obs::Byte(p.policy_binding[i])}}
fn expected(b:&[u8],f:usize,i:usize)->Obs{match f{0=>Obs::Status(status(b[5])),1=>Obs::Byte(b[6]),2=>Obs::Byte(b[7]),3=>Obs::Byte(b[8+i]),4=>Obs::Byte(b[40+i]),5=>Obs::Byte(b[72+i]),6=>Obs::Byte(b[104+i]),7=>Obs::Word(word(b,136)),8=>Obs::Word(word(b,144)),_=>Obs::Byte(b[152+i])}}
fn word(b:&[u8],a:usize)->u64{u64::from_le_bytes([b[a],b[a+1],b[a+2],b[a+3],b[a+4],b[a+5],b[a+6],b[a+7]])}
fn status(t:u8)->VerifierEntryStatusV1{match t{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cut(){let b:[u8;192]=kani::any();let reply=oracle();let mut log=None;let out=stage(&b,reply,&mut log);let i:usize=kani::any();kani::assume(i<32);let f:usize=kani::any();kani::assume(f<10);
 let error=if b[..4]!=POOL_V1_VERIFIER_ENTRY_MAGIC{Some(F::WrongMagic)}else if b[4]!=POOL_V1_VERIFIER_ENTRY_VERSION{Some(F::WrongVersion)}else if b[184..192]!=[0;8]{Some(F::NonZeroReserved)}else if b[5]>3{Some(F::InvalidStatus)}else{None};
 match error{Some(e)=>{assert!(log.is_none());assert!(matches!(out,Err(a) if a==e));},None=>{let p=log.expect("child entered");assert!((view(&p,f,i)==expected(&b,f,i))!=cfg!(NJI_invert));match reply{Err(e)=>assert!(matches!(out,Err(a) if a==e)),Ok(())=>{let p=out.expect("child success");assert!(view(&p,f,i)==expected(&b,f,i));}}}}
}
