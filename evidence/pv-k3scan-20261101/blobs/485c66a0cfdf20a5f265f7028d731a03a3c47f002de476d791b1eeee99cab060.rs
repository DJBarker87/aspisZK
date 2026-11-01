//! Owned prefix candidate. Registry construction and full source refinement are pending.
use aspis_core::field::{M31,CM31,QM31};
use aspis_statement::logup::CopyLogUpRow;
use aspis_statement::pool_v1::pair_trace::*;

#[derive(Clone,Copy)]
pub struct View {
    pub stable: [[Option<M31>;1024];16],
    pub late: [[Option<M31>;1024];16],
    pub withdrawal: bool,
}
#[inline(never)]
pub fn limb_at(tuple: PoolV1PairCopyTupleV1, i: usize) -> PoolV1PairTupleLimbV1 { tuple.limbs[i] }
#[inline(never)]
pub fn column_at(columns:[[Option<M31>;1024];16],c:usize) -> [Option<M31>;1024] {columns[c]}
#[inline(never)]
pub fn option_at(column:[Option<M31>;1024],r:usize) -> Option<M31> {column[r]}
#[inline(never)]
pub fn cell_at(view: View, source: PoolV1PairTraceCellV1) -> M31 {
    let column=match source.bank {
        PoolV1PairTraceBankV1::Stable => column_at(view.stable,source.cell.column as usize),
        PoolV1PairTraceBankV1::Late => column_at(view.late,source.cell.column as usize),
    };
    match option_at(column,source.cell.row as usize) {
        Some(v)=>v, None=>panic!("source vector index out of bounds")
    }
}
#[inline(never)]
pub fn value_at(values: [M31;16],i:usize) -> M31 {values[i]}
#[inline(never)]
pub fn row_at(rows: [CopyLogUpRow;1024],i:usize) -> CopyLogUpRow {rows[i]}
#[inline(never)]
pub fn link_at(links: [PoolV1PairCopyLinkV1;136],i:usize) -> PoolV1PairCopyLinkV1 {links[i]}

pub fn tuple_value(view: View, tuple: PoolV1PairCopyTupleV1) -> [M31;16] {
    let mut out=[M31::ZERO;16];
    let mut i=0usize;
    while i<16 {
        out[i]=match limb_at(tuple,i) {
            PoolV1PairTupleLimbV1::Zero => M31::ZERO,
            PoolV1PairTupleLimbV1::Cell {source,offset} => cell_at(view,source).add(offset),
        };
        i+=1;
    }
    out
}
pub fn compress(tag:M31,values:[M31;16],lambda:QM31) -> QM31 {
    let mut value=QM31::from_cm31(CM31::from_m31(tag));
    let mut power=lambda;
    let mut i=0usize;
    while i<16 {
        value=value.add(power.mul_m31(value_at(values,i)));
        power=power.mul(lambda);
        i+=1;
    }
    value
}
pub fn weight(weight:PoolV1PairCopyWeightV1,append_index:u64,withdrawal:bool) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(!withdrawal)),
        PoolV1PairCopyWeightV1::WithdrawalOnly => M31(u32::from(withdrawal)),
        PoolV1PairCopyWeightV1::AppendCurrentLeft {level} => M31(1-((append_index>>level)&1) as u32),
        PoolV1PairCopyWeightV1::AppendCurrentRight {level} => M31(((append_index>>level)&1) as u32),
    }
}
pub fn side(mut rows:[CopyLogUpRow;1024],view:View,tuple:PoolV1PairCopyTupleV1,
    tag:M31,weight:M31,lambda:QM31,consumer:bool) -> Result<[CopyLogUpRow;1024],PoolV1PairTraceErrorV1> {
    let row_index=tuple.row as usize;
    let mut row=row_at(rows,row_index);
    let mut weights=if consumer {row.consumer_weights} else {row.producer_weights};
    let mut values=if consumer {row.consumer_values} else {row.producer_values};
    let slot=if weights[0]==M31::ZERO {0} else if weights[1]==M31::ZERO {1} else {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    };
    values[slot]=compress(tag,tuple_value(view,tuple),lambda);
    weights[slot]=weight;
    if consumer {row.consumer_values=values;row.consumer_weights=weights;}
    else {row.producer_values=values;row.producer_weights=weights;}
    rows[row_index]=row;
    Ok(rows)
}
pub fn copy_rows(view:View,registry:[PoolV1PairCopyLinkV1;136],append_index:u64,lambda:QM31)
    -> Result<[CopyLogUpRow;1024],PoolV1PairTraceErrorV1> {
    let empty=CopyLogUpRow {producer_values:[QM31::ZERO;2],producer_weights:[M31::ZERO;2],
        consumer_values:[QM31::ZERO;2],consumer_weights:[M31::ZERO;2]};
    let mut rows=[empty;1024];
    let mut i=0usize;
    while i<136 {
        let link=link_at(registry,i);
        let w=weight(link.weight,append_index,view.withdrawal);
        rows=side(rows,view,link.producer,link.tag,w,lambda,false)?;
        rows=side(rows,view,link.consumer,link.tag,w,lambda,true)?;
        i+=1;
    }
    Ok(rows)
}
