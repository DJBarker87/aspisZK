
#[cfg(kani)]
mod Hir_checkpoint_guards {
    use super::*;

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_occupied_guard_rejects() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array([8; 32]);
        let mut bytes: [u8; 192] = kani::any();
        kani::assume(bytes[0] != 0);
        let original = bytes;
        let mut lamports = u64::MAX;
        let account = AccountInfo::new(&address, false, true, &mut lamports,
            &mut bytes, &id, false, 0);
        let result = require_program_owned_zeroed(&account, &id, 192, &Rent::default());
        assert!(result.is_err());
        drop(account);
        assert!(bytes == original);
    }

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_occupied_plan_rejects() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array([8; 32]);
        let mut bytes: [u8; 192] = kani::any();
        kani::assume(bytes[0] != 0);
        let original = bytes;
        let mut lamports = u64::MAX;
        let account = AccountInfo::new(&address, false, true, &mut lamports,
            &mut bytes, &id, false, 0);
        let result = crate::processor::plan_fresh_program_pda(&account, &id, &address, 192);
        assert!(result.is_err());
        drop(account);
        assert!(bytes == original);
    }
}
