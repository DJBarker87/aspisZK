
#[cfg(kani)]
mod PoolN_guards {
    use super::*;
    struct NoEffects;
    impl PoolCpiRuntimeV1 for NoEffects {
        fn invoke<'a>(&mut self, _: &Instruction, _: &[AccountInfo<'a>]) -> ProgramResult {
            panic!("unexpected CPI")
        }
        fn invoke_signed<'a>(&mut self, _: &Instruction, _: &[AccountInfo<'a>], _: &[&[&[u8]]]) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
        fn close_program_account<'a>(&mut self, _: &AccountInfo<'a>, _: &AccountInfo<'a>, _: &Pubkey, _: usize) -> ProgramResult {
            panic!("unexpected close")
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolN_ASDI_primary_192() {
        let id = Pubkey::new_from_array([7;32]);
        let key = Pubkey::new_from_array([8;32]);
        let mut bytes: [u8;192] = kani::any();
        let before=bytes;
        let mut balance: u64 = kani::any();
        let initial_balance=balance;
        let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
        let mut instruction=[0u8;80];
        instruction[..4].copy_from_slice(b"ASDI"); instruction[4]=1; instruction[40]=1;
        assert!(decode_deposit_top_level_v1(&instruction).is_ok());
        let result=process_deposit_with_runtime_v1(&id,&[account.clone()],&instruction,&mut NoEffects);
        assert_eq!(result, Err(PoolV1ProgramError::InvalidAccountType.into()));
        drop(account); assert!(bytes==before); assert!(balance==initial_balance);
    }
}
