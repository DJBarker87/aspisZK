    pub(crate) fn circle_validated(
        &mut self,
        record: ValidatedRecord<'_>,
    ) -> Result<SecureCirclePoint, Error> {
        let row = record.row();
        let circle_row = match row {
            25 => CircleRow::First,
            26 => CircleRow::Second,
            _ => return Err(Error::InvalidRow),
        };
        Ok(circle_sample(
            &self.sample_block_validated(row, record.framed())?,
            circle_row,
        ))
    }