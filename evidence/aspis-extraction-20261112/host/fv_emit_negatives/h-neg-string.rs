impl aspis_core::Digest32 for SolanaDigest {
    #[inline(always)]
    fn digest_into(&self, parts: &[&[u8]], out: &mut [u8; 32]) {
        #[cfg(target_os = "solana")]
        #[allow(deprecated)]
        unsafe {
            solana_program::syscalls::sol_sha256(parts as *const _ as *const u8, parts.len() as u64, out.as_mut_ptr());
        }
        #[cfg(not(target_os = "solana"))]
        {
            msg!("h"); *out = hashv(parts).to_bytes();
        }
    }
}
