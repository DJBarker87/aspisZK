impl DurableStateOnlyMaskNonceStore {
pub fn reserve_fallible(
        &mut self,
        statement_digest: [u8; 32],
        mask_nonce: [u8; 32],
    ) -> io::Result<bool> {
        self.last_error = None;
        let path = self.reservation_path(&mask_nonce);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        let mut file = match options.open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error),
        };

        // A partially written file is still a burned nonce. Never remove it
        // on failure.
        file.write_all(RESERVATION_MAGIC)?;
        file.write_all(&statement_digest)?;
        file.write_all(&mask_nonce)?;
        file.sync_all()?;
        sync_directory(&self.directory)?;
        Ok(true)
    }
}
impl StateOnlyMaskNonceStore for DurableStateOnlyMaskNonceStore {
fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        match self.reserve_fallible(statement_digest, mask_nonce) {
            Ok(reserved) => reserved,
            Err(error) => {
                self.last_error = Some(error.kind());
                false
            }
        }
    }
}
