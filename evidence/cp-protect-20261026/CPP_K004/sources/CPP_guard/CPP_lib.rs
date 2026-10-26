use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,pubkey::Pubkey,program_error::ProgramError};
use aspis_r1_cost_probe::{verifier,transport::Variant};

struct OwnedAccount {
    key: Pubkey,
    owner: Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
    length: Result<usize, ProgramError>,
    bytes: Result<Vec<u8>, ProgramError>,
}

impl OwnedAccount {
    fn key(&self) -> &Pubkey { &self.key }
    fn owner(&self) -> &Pubkey { &self.owner }
    fn data(&self) -> Result<&[u8], ProgramError> {
        match &self.bytes { Ok(bytes) => Ok(bytes), Err(error) => Err(error.clone()) }
    }
    fn data_len(&self) -> Result<usize, ProgramError> { self.length.clone() }
}

fn require_verifier_checkpoint(account: &OwnedAccount, program_id: &Pubkey, writable: bool) -> ProgramResult {
    if account.owner() != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.data_len()? != verifier::checkpoint_size(Variant::S2) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
    }
    Ok(())
}

#[cfg(kani)]
mod CPP_harnesses {
    use super::*;
    #[kani::proof]
    fn CPP_checkpoint_guard_acceptance() {
        let owner=Pubkey::new_from_array(kani::any());
        let program=Pubkey::new_from_array(kani::any());
        let signer:bool=kani::any(); let executable:bool=kani::any();
        let writable:bool=kani::any(); let expected:bool=kani::any();
        let length:usize=kani::any();
        let account=OwnedAccount { key:Pubkey::new_from_array(kani::any()),owner,
            is_signer:signer,is_writable:writable,executable,length:Ok(length),
            bytes:Err(ProgramError::InvalidAccountData) };
        let result=require_verifier_checkpoint(&account,&program,expected);
        assert_eq!(result.is_ok(),owner==program && !signer && !executable && writable==expected && length==1768);
    }
    #[kani::proof]
    fn CPP_guard_error_payload() {
        let program=Pubkey::new_from_array(kani::any());
        let writable:bool=kani::any(); let expected:u32=kani::any();
        let account=OwnedAccount { key:Pubkey::new_from_array(kani::any()),owner:program,
            is_signer:false,is_writable:writable,executable:false,
            length:Err(ProgramError::Custom(expected)),bytes:Err(ProgramError::InvalidAccountData) };
        match require_verifier_checkpoint(&account,&program,writable) {
            Err(ProgramError::Custom(actual)) => assert!(actual==expected),
            _ => panic!("wrong native error"),
        }
    }
    #[kani::proof]
    #[kani::unwind(2)]
    fn CPP_initialized_rejects() {
        let mut bytes:[u8;1768]=kani::any(); bytes[0]=82;
        let coordinate:usize=kani::any(); kani::assume(coordinate<1768);
        let before=bytes[coordinate];
        assert!(matches!(require_zero(&bytes),Err(ProgramError::AccountAlreadyInitialized)));
        assert!(bytes[coordinate]==before);
    }
    #[kani::proof]
    fn CPP_pubkey_full_eq() {
        let left:[u8;32]=kani::any(); let right:[u8;32]=kani::any();
        assert_eq!(Pubkey::new_from_array(left)==Pubkey::new_from_array(right),left==right);
    }
}
