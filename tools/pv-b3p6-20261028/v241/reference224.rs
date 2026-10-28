//! Owned V241 helper continuation. Full trace/registry composition remains open.
use aspis_core::field::{M31,QM31};
use aspis_statement::logup::CopyLogUpRow;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { CopyImbalance }

pub fn endpoint(value: QM31, operand: QM31, weight: M31, chi: QM31, consumer: bool) -> Result<QM31,Error> {
    if weight == M31::ZERO { return Ok(value); }
    let inv = match chi.sub(operand).try_inv() {
        Some(v) => v,
        None => return Err(Error::CopyImbalance),
    };
    let term = inv.mul_m31(weight);
    Ok(if consumer { value.sub(term) } else { value.add(term) })
}

pub fn one_row(row: CopyLogUpRow, chi: QM31) -> Result<QM31,Error> {
    let v0=endpoint(QM31::ZERO,row.producer_values[0],row.producer_weights[0],chi,false)?;
    let v1=endpoint(v0,row.producer_values[1],row.producer_weights[1],chi,false)?;
    let v2=endpoint(v1,row.consumer_values[0],row.consumer_weights[0],chi,true)?;
    endpoint(v2,row.consumer_values[1],row.consumer_weights[1],chi,true)
}

#[inline(never)]
pub fn row_at(rows: [CopyLogUpRow;1024], r: usize) -> CopyLogUpRow { rows[r] }

pub fn from_rows(rows: [CopyLogUpRow;1024], chi: QM31) -> Result<[QM31;1024],Error> {
    let mut helper = [QM31::ZERO;1024];
    let mut r = 0usize;
    while r < 1024 {
        let row = row_at(rows,r);
        let value = one_row(row,chi)?;
        helper[r] = value;
        r += 1;
    }
    Ok(helper)
}
