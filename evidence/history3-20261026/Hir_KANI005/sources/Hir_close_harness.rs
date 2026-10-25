
#[cfg(kani)]
mod Hir_checkpoint_close {
    use super::*;

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_checkpoint_cannot_close_as_plan() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array([8; 32]);
        let refund_key = Pubkey::new_from_array([9; 32]);
        let mut bytes: [u8; 192] = kani::any();
        let original = bytes;
        let mut lamports: u64 = kani::any();
        let original_balance = lamports;
        let mut refund_balance: u64 = kani::any();
        let original_refund = refund_balance;
        let mut refund_data = [];
        let account = AccountInfo::new(&address, false, true, &mut lamports,
            &mut bytes, &id, false, 0);
        let refund = AccountInfo::new(&refund_key, true, true, &mut refund_balance,
            &mut refund_data, &id, false, 0);
        let size = if kani::any() { POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES }
            else { POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES };
        assert!(close_program_account_v1(&account, &refund, &id, size).is_err());
        drop((account, refund));
        assert!(bytes == original);
        assert!(lamports == original_balance);
        assert!(refund_balance == original_refund);
    }
}
