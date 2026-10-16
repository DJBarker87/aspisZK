    pub(crate) fn validated_record(&self, row: u8) -> Result<ValidatedRecord<'a>, Error> {
        Ok(ValidatedRecord {
            row,
            framed: self.record(row)?,
        })
    }