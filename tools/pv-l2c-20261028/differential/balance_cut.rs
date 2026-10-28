use aspis_core::field::{M31,QM31};

pub const STATE_ONLY_POSEIDON_TRACE_ROWS: usize = 1 << 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateOnlyMaskBuildError {
    ZeroPrivateEntropy,
    ReusedMaskNonce,
    MaskSampleExhausted,
    TraceShape,
    Layout,
}

fn balance_m31_copy_inactive(
    table: &mut [M31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum=sum_m31_copy_inactive(table,dependent,active);
    let value=M31::ZERO.sub(sum);
    table[dependent]=value;
    Ok(())
}

fn sum_m31_copy_inactive(table:&[M31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->M31 {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut sum=M31::ZERO;
    let mut row=0;
    while row<rows {
        sum=inactive_m31_step(sum,table,dependent,active,row);
        row+=1;
    }
    sum
}

fn inactive_m31_step(sum:M31,table:&[M31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],row:usize)->M31 {
    if !active[row] && row!=dependent {sum.add(table[row])} else {sum}
}

fn balance_qm31_copy_inactive(
    table: &mut [QM31],
    dependent: usize,
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<(), StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    if table.len() != STATE_ONLY_POSEIDON_TRACE_ROWS || active[dependent] {
        return Err(StateOnlyMaskBuildError::TraceShape);
    }
    let sum=sum_qm31_copy_inactive(table,dependent,active);
    let value=QM31::ZERO.sub(sum);
    table[dependent]=value;
    Ok(())
}

fn sum_qm31_copy_inactive(table:&[QM31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->QM31 {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut sum=QM31::ZERO;
    let mut row=0;
    while row<rows {
        sum=inactive_qm31_step(sum,table,dependent,active,row);
        row+=1;
    }
    sum
}

fn inactive_qm31_step(sum:QM31,table:&[QM31],dependent:usize,active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],row:usize)->QM31 {
    if !active[row] && row!=dependent {sum.add(table[row])} else {sum}
}

pub(crate) fn balance_m31_owned(mut table: Vec<M31>, dependent: usize,
    active: &[bool; 1024]) -> (Result<(), StateOnlyMaskBuildError>, Vec<M31>)
{
    if table.len() != 1024 || active[dependent] {
        return (Err(StateOnlyMaskBuildError::TraceShape), table);
    }
    let sum = balance_m31_rows(&table, dependent, active, 0, M31::ZERO);
    table[dependent] = M31::ZERO.sub(sum);
    (Ok(()), table)
}

pub(crate) fn balance_m31_rows(table: &[M31], dependent: usize,
    active: &[bool; 1024], row: usize, sum: M31) -> M31
{
    if row < 1024 {
        let after = balance_m31_step(sum, table[row], active[row], row, dependent);
        balance_m31_rows(table, dependent, active, row + 1, after)
    } else { sum }
}

pub(crate) fn balance_m31_step(sum: M31, value: M31, active: bool,
    row: usize, dependent: usize) -> M31 {
    if !active && row != dependent { sum.add(value) } else { sum }
}

pub(crate) fn balance_qm31_owned(mut table: Vec<aspis_core::field::QM31>, dependent: usize,
    active: &[bool; 1024]) -> (Result<(), StateOnlyMaskBuildError>, Vec<aspis_core::field::QM31>)
{
    if table.len() != 1024 || active[dependent] {
        return (Err(StateOnlyMaskBuildError::TraceShape), table);
    }
    let sum = balance_qm31_rows(&table, dependent, active, 0, aspis_core::field::QM31::ZERO);
    table[dependent] = aspis_core::field::QM31::ZERO.sub(sum);
    (Ok(()), table)
}

pub(crate) fn balance_qm31_rows(table: &[aspis_core::field::QM31], dependent: usize,
    active: &[bool; 1024], row: usize, sum: aspis_core::field::QM31) -> aspis_core::field::QM31
{
    if row < 1024 {
        let after = balance_qm31_step(sum, table[row], active[row], row, dependent);
        balance_qm31_rows(table, dependent, active, row + 1, after)
    } else { sum }
}

pub(crate) fn balance_qm31_step(sum: aspis_core::field::QM31,
    value: aspis_core::field::QM31, active: bool, row: usize, dependent: usize)
    -> aspis_core::field::QM31 {
    if !active && row != dependent { sum.add(value) } else { sum }
}
