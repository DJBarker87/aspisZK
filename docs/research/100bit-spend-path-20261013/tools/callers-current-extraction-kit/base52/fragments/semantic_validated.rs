    pub(crate) fn semantic_validated(
        &mut self,
        record: ValidatedRecord<'_>,
    ) -> Result<QM31, Error> {
        let row = record.row();
        if row > 24 {
            return Err(Error::InvalidRow);
        }
        Ok(qm31_sample(
            &self.sample_block_validated(row, record.framed())?,
        ))
    }