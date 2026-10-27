mod field;use field::M31;
const MERKLE_NODE_COMPRESSION_V3_TWEAK:M31=M31(0x4153_1005);
#[derive(Clone,Copy,Debug)]
pub enum PoolV1PairTraceBankV1 {
    Stable,
    Late,
}
#[derive(Clone,Copy,Debug)]
pub struct PoolV1PairTraceCellV1 {
    pub bank: PoolV1PairTraceBankV1,
    pub cell: TraceCell,
}
#[derive(Clone,Copy,Debug)]
pub enum PoolV1PairTupleLimbV1 {
    Zero,
    Cell {
        source: PoolV1PairTraceCellV1,
        offset: M31,
    },
}
#[derive(Clone,Copy,Debug)]
pub struct PoolV1PairCopyTupleV1 {
    pub row: u16,
    pub limbs: [PoolV1PairTupleLimbV1; 16],
}
#[derive(Clone,Copy,Debug)]
pub struct TraceCell {
    pub row: u16,
    pub column: u8,
}
fn bank_for_row(row: usize) -> PoolV1PairTraceBankV1 {
    if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    }
}
fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = bank_for_row(row);
    let mut limbs = [PoolV1PairTupleLimbV1::Zero; 16];
    for lane in 0..count {
        let column = start + lane;
        let offset = if tweak_right && lane + 1 == count {
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            M31::ZERO
        };
        limbs[lane] = PoolV1PairTupleLimbV1::Cell {
            source: PoolV1PairTraceCellV1 {
                bank,
                cell: TraceCell {
                    row: row as u16,
                    column: column as u8,
                },
            },
            offset,
        };
    }
    PoolV1PairCopyTupleV1 {
        row: row as u16,
        limbs,
    }
}
mod forest{use super::*;pub fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    };
    let mut limbs = [PoolV1PairTupleLimbV1::Zero; 16];
    for lane in 0..count {
        let column = start + lane;
        let offset = if tweak_right && lane + 1 == count {
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            M31::ZERO
        };
        limbs[lane] = PoolV1PairTupleLimbV1::Cell {
            source: PoolV1PairTraceCellV1 {
                bank,
                cell: TraceCell {
                    row: row as u16,
                    column: column as u8,
                },
            },
            offset,
        };
    }
    PoolV1PairCopyTupleV1 {
        row: row as u16,
        limbs,
    }
}}
fn flatten(v:PoolV1PairCopyTupleV1)->Vec<Vec<u32>> {v.limbs.into_iter().map(|l|match l{PoolV1PairTupleLimbV1::Zero=>vec![],PoolV1PairTupleLimbV1::Cell{source,offset}=>vec![source.cell.row as u32,source.cell.column as u32,offset.0,match source.bank{PoolV1PairTraceBankV1::Stable=>0,PoolV1PairTraceBankV1::Late=>1}]}).collect()}
fn main(){println!("tuple {:?}",flatten(tuple_cells(550,3,3,true)));println!("forest {:?}",flatten(forest::tuple_cells(550,3,3,true)));}
