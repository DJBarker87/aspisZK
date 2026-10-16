    pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
        if row >= 27 {
            return Err(Error::InvalidRow);
        }
        Ok(self.records[row as usize])
    }