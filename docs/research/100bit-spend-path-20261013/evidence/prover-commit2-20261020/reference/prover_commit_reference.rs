use super::*;

pub(super) fn reference_build_mask_material_for_layout(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
    nonce_store: &mut impl StateOnlyMaskNonceStore,
    cells: &[aspis_statement::TraceCell],
    active: &[bool; STATE_ONLY_POSEIDON_TRACE_ROWS],
) -> Result<StateOnlyMaskMaterial, StateOnlyMaskBuildError> {
    if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
        return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
    }
    let seed = derive_state_only_mask_seed_from_entropy_ref(
        hash,
        precommit_binding,
        context,
        private_entropy,
    )?;
    let mut expander = SeedExpander::new(hash, seed);
    let inactive_dependent = reference_first_inactive(active);
    let c1 = sample_m31_mask_cells(&mut expander, Vec::with_capacity(cells.len()), cells.len())?;
    let columns: [Vec<M31>; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
        core::array::from_fn(|_| Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
    let mut result = Ok(columns);
    for index in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        result = match result {
            Ok(columns) => sample_mask_only_column(&mut expander, columns, index, inactive_dependent, active),
            Err(error) => Err(error),
        };
    }
    let mask_only_c1 = result?;
    let mut result = Ok(Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
    for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        result = match result {
            Ok(values) => append_qm31_mask_cell(&mut expander, values),
            Err(error) => Err(error),
        };
    }
    let mut g = result?;
    reference_balance_qm31(&mut g, inactive_dependent, active)?;
    let mut result = Ok(vec![QM31::ZERO; STATE_ONLY_POSEIDON_TRACE_ROWS]);
    for row in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
        result = match result {
            Ok(values) => write_qm31_padding_cell(&mut expander, values, row, inactive_dependent, active),
            Err(error) => Err(error),
        };
    }
    let mut h1_padding = result?;
    reference_balance_qm31(&mut h1_padding, inactive_dependent, active)?;
    Ok(StateOnlyMaskMaterial {
        c1,
        mask_only_c1,
        g,
        h1_padding,
        mask_nonce: context.mask_nonce,
    })
}

fn append_qm31_mask_cell(expander: &mut SeedExpander, mut values: Vec<QM31>) -> Result<Vec<QM31>, StateOnlyMaskBuildError> {
    let value = expander.qm31()?;
    values.push(value);
    Ok(values)
}

fn write_qm31_padding_cell(expander: &mut SeedExpander, mut values: Vec<QM31>, row: usize, dependent: usize, active: &[bool;STATE_ONLY_POSEIDON_TRACE_ROWS]) -> Result<Vec<QM31>, StateOnlyMaskBuildError> {
    if !active[row] && row != dependent {
        let value = expander.qm31()?;
        values[row] = value;
    }
    Ok(values)
}

fn append_m31_mask_cell(expander: &mut SeedExpander, mut values: Vec<M31>) -> Result<Vec<M31>, StateOnlyMaskBuildError> {
    let value = expander.m31()?;
    values.push(value);
    Ok(values)
}

fn sample_m31_mask_cells(expander: &mut SeedExpander, values: Vec<M31>, count: usize) -> Result<Vec<M31>, StateOnlyMaskBuildError> {
    let mut result = Ok(values);
    for _ in 0..count {
        result = match result {
            Ok(values) => append_m31_mask_cell(expander, values),
            Err(error) => Err(error),
        };
    }
    result
}

fn sample_mask_only_column(expander: &mut SeedExpander, mut columns: [Vec<M31>;STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], index: usize, dependent: usize, active: &[bool;STATE_ONLY_POSEIDON_TRACE_ROWS]) -> Result<[Vec<M31>;STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], StateOnlyMaskBuildError> {
    let previous = core::mem::take(&mut columns[index]);
    let mut column = sample_m31_mask_cells(expander, previous, STATE_ONLY_POSEIDON_TRACE_ROWS)?;
    reference_balance_m31(&mut column, dependent, active)?;
    columns[index] = column;
    Ok(columns)
}
fn reference_first_inactive(active: &[bool;1024]) -> usize {
    let mut row=0;
    while row<1024 {
        if !active[row] { return row; }
        row+=1;
    }
    panic!("generated layout has an inactive row")
}
fn reference_balance_m31(table: &mut [M31], dependent: usize, active: &[bool;1024]) -> Result<(),StateOnlyMaskBuildError> {
    if table.len()!=1024 || active[dependent] {return Err(StateOnlyMaskBuildError::TraceShape);}
    let mut sum=M31::ZERO;
    for row in 0..1024 {
        if !active[row] && row!=dependent {sum=sum.add(table[row]);}
    }
    table[dependent]=M31::ZERO.sub(sum);
    Ok(())
}
fn reference_balance_qm31(table: &mut [QM31], dependent: usize, active: &[bool;1024]) -> Result<(),StateOnlyMaskBuildError> {
    if table.len()!=1024 || active[dependent] {return Err(StateOnlyMaskBuildError::TraceShape);}
    let mut sum=QM31::ZERO;
    for row in 0..1024 {
        if !active[row] && row!=dependent {sum=sum.add(table[row]);}
    }
    table[dependent]=QM31::ZERO.sub(sum);
    Ok(())
}
#[cfg(kani)]
mod proofs {
    use super::*;
    struct Store(bool);
    impl StateOnlyMaskNonceStore for Store {
        fn reserve(&mut self, _: [u8;32], _: [u8;32])->bool {self.0}
    }
    #[kani::proof]
    fn shipped_vs_reference_fixed_sizes() {
        let hash: HashFn=kani::any();
        let binding: [u8;32]=kani::any();
        let entropy: [u8;32]=kani::any();
        let context=StateOnlyHidingContext {
            statement_digest:kani::any(),mask_nonce:kani::any(),
            mask_layout_fingerprint:kani::any(),layout_factor_fingerprint:kani::any(),
        };
        let active: [bool;1024]=kani::any();
        kani::assume(active.iter().any(|b| !*b));
        let cells: Vec<aspis_statement::TraceCell>=(0..3803).map(|i|aspis_statement::TraceCell{row:(i%1024) as u16,column:(i/1024) as u8}).collect();
        let reservation: bool=kani::any();
        let left=super::super::build_mask_material_for_layout(hash,binding,context,&entropy,&mut Store(reservation),&cells,&active);
        let right=reference_build_mask_material_for_layout(hash,binding,context,&entropy,&mut Store(reservation),&cells,&active);
        match (left,right) {
            (Ok(l),Ok(r))=>{
                assert_eq!(l.c1,r.c1);assert_eq!(l.mask_only_c1,r.mask_only_c1);
                assert_eq!(l.g,r.g);assert_eq!(l.h1_padding,r.h1_padding);
                assert_eq!(l.mask_nonce,r.mask_nonce);
            },
            (Err(l),Err(r))=>assert_eq!(l,r),
            _=>assert!(false),
        }
    }
}
