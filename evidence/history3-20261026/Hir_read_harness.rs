
#[cfg(kani)]
mod Hir_retained_reader {
    use super::*;

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_retained_reader_wrong_owner() {
        let id_bytes = [7; 32];
        let id = Pubkey::new_from_array(id_bytes);
        let owner_bytes: [u8; 32] = kani::any();
        kani::assume(owner_bytes != id_bytes);
        let owner = Pubkey::new_from_array(owner_bytes);
        let address = Pubkey::new_from_array(kani::any());
        let master = Pubkey::new_from_array(kani::any());
        let mut bytes: [u8; 192] = kani::any();
        let original = bytes;
        let mut lamports: u64 = kani::any();
        let account = AccountInfo::new(&address, kani::any(), kani::any(), &mut lamports,
            &mut bytes, &owner, kani::any(), 0);
        assert!(decode_retained_pair_forest_checkpoint_account_v1(&id, &master, &account).is_err());
        drop(account);
        assert!(bytes == original);
    }

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_retained_reader_signer() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array(kani::any());
        let master = Pubkey::new_from_array(kani::any());
        let mut bytes: [u8; 192] = kani::any();
        let original = bytes;
        let mut lamports: u64 = kani::any();
        let account = AccountInfo::new(&address, true, false, &mut lamports,
            &mut bytes, &id, false, 0);
        assert!(decode_retained_pair_forest_checkpoint_account_v1(&id, &master, &account).is_err());
        drop(account);
        assert!(bytes == original);
    }
}
