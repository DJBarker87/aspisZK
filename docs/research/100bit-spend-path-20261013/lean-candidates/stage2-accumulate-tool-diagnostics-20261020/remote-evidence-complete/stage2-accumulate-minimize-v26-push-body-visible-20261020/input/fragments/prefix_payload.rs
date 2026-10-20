    pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
        let framed = self.record(row)?;
        Ok(&framed[5..])
    }