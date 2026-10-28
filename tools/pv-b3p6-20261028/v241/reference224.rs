//! Owned V241 helper continuation. Full trace/registry composition remains open.
use aspis_core::field::{M31,QM31};
use aspis_statement::logup::CopyLogUpRow;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { CopyImbalance }

pub fn from_rows(rows: [CopyLogUpRow;1024], chi: QM31) -> Result<[QM31;1024],Error> {
    let mut helper = [QM31::ZERO;1024];
    let mut r = 0usize;
    while r < 1024 {
        let row = rows[r];
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 2 {
            let weight = row.producer_weights[slot];
            if weight != M31::ZERO {
                let inv = match chi.sub(row.producer_values[slot]).try_inv() {
                    Some(v) => v,
                    None => return Err(Error::CopyImbalance),
                };
                value = value.add(inv.mul_m31(weight));
            }
            slot += 1;
        }
        slot = 0;
        while slot < 2 {
            let weight = row.consumer_weights[slot];
            if weight != M31::ZERO {
                let inv = match chi.sub(row.consumer_values[slot]).try_inv() {
                    Some(v) => v,
                    None => return Err(Error::CopyImbalance),
                };
                value = value.sub(inv.mul_m31(weight));
            }
            slot += 1;
        }
        helper[r] = value;
        r += 1;
    }
    Ok(helper)
}
