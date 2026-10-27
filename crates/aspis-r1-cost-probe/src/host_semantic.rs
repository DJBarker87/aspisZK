//! UNPROVED COST PROBE. Own D14 semantic prover; original prover unchanged.
use crate::host_multilinear::multilinear_evaluate_qm31;
use alloc::vec::Vec;
use crate::host_forest::materialize_copy_helper as build_pool_v1_pair_forest_copy_helper_v1;
use aspis_core::{field::{WideExact, M31, QM31, P},Digest32,r0::{domain::Point,encoder::eval_message}};
use crate::host_wire::{self as wire,Challenges,Error,SemanticTranscript};
use aspis_statement::{state_only_copy_helper_sum,StateOnlyTraceFoundation,pool_v1::{pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1}};
    /// Backend errors abort. Inputs are borrowed only during each call;
    /// no array of column loans survives the call boundary.
    pub trait Commitments {
        fn c1(&mut self,columns:&[Vec<M31>;26],d:&[QM31;1024])->Result<[u8;32],Error>;
        fn c2(&mut self,h1:&[QM31],g:&[QM31;1024])->Result<[u8;32],Error>;
    }
    pub struct BuiltSemantics<H: Digest32> {
        pub bytes: Vec<u8>,
        pub transcript: SemanticTranscript<H>,
        pub challenges: Challenges,
        pub alpha: [QM31; 10],
        /// Opening integration starts with this row-25 state, bound roots,
        /// and the 25 challenges (not the later diagnostic row-27 state).
        pub state_before_z0: [u8; 32],
        pub roots: [[u8; 32]; 2],
        pub columns: [Vec<QM31>; 29],
        pub z: [aspis_core::circle::SecureCirclePoint; 2],
    }
    fn lift(x: M31) -> QM31 {
        QM31::from_cm31(aspis_core::field::CM31::from_m31(x))
    }
    pub fn point_claims(
        columns: &[Vec<QM31>; 29],
        point: &[QM31; 10],
    ) -> Result<[[QM31; 29]; 3], Error> {
        let points=wire::statement_points(point);
        let first=claims_at_point(columns,&points[0])?;
        let second=claims_at_point(columns,&points[1])?;
        let third=claims_at_point(columns,&points[2])?;
        Ok([first,second,third])
    }
#[inline(always)]
fn claims_at_point(columns:&[Vec<QM31>;29],point:&[QM31;10])->Result<[QM31;29],Error> {
    let mut claims=[QM31::ZERO;29];let mut lane=0;
    while lane<29 {
        let value=multilinear_evaluate_qm31(&columns[lane],point).ok_or(Error::Public)?;
        claims[lane]=value;lane+=1;
    }
    Ok(claims)
}

    #[allow(clippy::too_many_arguments)]
    fn build_with_helper_mode<H: Digest32>(
        public: Public<'_>,
        c1: &[Vec<M31>; 26],
        d: &[QM31; 1024],
        g: &[QM31; 1024],
        h1_padding: &[QM31; 1024],
        helper: impl FnOnce(QM31, QM31) -> Result<Vec<QM31>, Error>,
        commitments: &mut impl Commitments,
        hash: H,
        variant: crate::transport::Variant,
    ) -> Result<BuiltSemantics<H>, Error> {
        // Reject raw noncanonical constructors rather than normalize their
        // commitment representation. D is supplied before any challenge.
        check_semantic_columns(c1,d,g)?;
        let c1_root=commitments.c1(c1,d)?;
        let mut transcript = SemanticTranscript::new(hash, &crate::host_public::materialize_public_bytes(public).map_err(|_|Error::Public)?, &c1_root)?;
        let mut bytes = c1_root.to_vec();
        let lambda = semantic_row(0, &[], &mut transcript, &mut bytes)?;
        let chi = semantic_row(1, &[], &mut transcript, &mut bytes)?;
        let mut h1 = helper(lambda, chi)?;
        aspis_prover::state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(
            &mut h1,
            h1_padding,
        )
        .map_err(|_| Error::Public)?;
        if h1.len()!=1024 {return Err(Error::Public);}
        if state_only_copy_helper_sum(&h1) != Some(QM31::ZERO) {
            return Err(Error::Public);
        }
        let c2_root=commitments.c2(&h1,g)?;
        let theta = semantic_row(2, &c2_root, &mut transcript, &mut bytes)?;
        let zc=zc_rows(&mut transcript,&mut bytes)?;
        let mu = semantic_row(13, &[], &mut transcript, &mut bytes)?;
        let columns=lift_columns(c1,h1,g,d);
        let dc=variant.coefficients(d);
        let mut mask_sum=initial_mask_sum(&columns);
        mask_sum=add_d_tail(mask_sum,&dc);
        let eta = semantic_row(
            14,
            &WideExact::from_qm31(mask_sum).to_le_bytes(),
            &mut transcript,
            &mut bytes,
        )?;
        let challenges = Challenges {
            lambda,
            chi,
            theta,
            zc,
            mu,
            eta,
        };
        let oracle=SemanticOracle{public:&public,columns:&columns,challenges:&challenges,eta,d:&dc};
        let (alpha, _) = crate::host_sumcheck::prove_sumcheck(
            &mut transcript,&mut bytes,mask_sum,&oracle,
        )?;
        let claims = point_claims(&columns, &alpha)?;
        let state_before_z0 = transcript.state();
        let extras=extra_claims(&columns,variant,alpha[8],alpha[9]);
        let before_z0=wire::record(25,&claim_bytes(claims,extras))?;
        let z0=transcript.challenge_reference_circle_point(25,&before_z0)?;
        bytes.extend_from_slice(&before_z0);
        let before_z1=wire::record(26,&endpoint_bytes(&columns,variant,z0))?;
        let z1 = transcript.challenge_reference_circle_point(26, &before_z1)?;
        bytes.extend_from_slice(&before_z1);
        if z0 == z1 {
            return Err(Error::EqualCirclePoints);
        }
        Ok(BuiltSemantics {
            bytes,
            transcript,
            challenges,
            alpha,
            state_before_z0,
            roots: [c1_root, c2_root],
            columns,
            z: [z0, z1],
        })
    }


struct SemanticOracle<'a,'p> {
    public:&'a Public<'p>,
    columns:&'a[Vec<QM31>;29],
    challenges:&'a Challenges,
    eta:QM31,
    d:&'a[QM31;1024],
}
impl crate::host_sumcheck::Oracle for SemanticOracle<'_,'_> {
    fn evaluate(&self,point:&[QM31;10])->Result<QM31,Error> {
        let claims=point_claims(self.columns,point)?;
        let terminal=crate::host_public::terminal_qm31(*self.public,&claims,point,self.challenges).map_err(|_|Error::Public)?;
        let mask=claim_mask_value(claims[0],point);
        Ok(mask.add(self.eta.mul(terminal)).add(extra(self.d,point[8],point[9])))
    }
}

fn check_semantic_columns(c1:&[Vec<M31>;26],d:&[QM31;1024],g:&[QM31;1024])->Result<(),Error> {
    check_base_columns(c1)?;
    check_secure_column(d)?;
    check_secure_column(g)
}
fn check_base_columns(c1:&[Vec<M31>;26])->Result<(),Error> {
    let mut lane=0;
    while lane<26 {check_base_column(&c1[lane])?;lane+=1;}
    Ok(())
}
fn check_base_column(column:&[M31])->Result<(),Error> {
    if column.len()!=1024 {return Err(Error::Public);}
    let mut row=0;
    while row<1024 {
        if column[row].0>=P {return Err(Error::Public);}
        row+=1;
    }
    Ok(())
}
fn check_secure_column(column:&[QM31;1024])->Result<(),Error> {
    let mut row=0;
    while row<1024 {
        let mut b=[0;16];
        column[row].write_le_bytes(&mut b);
        if QM31::from_le_bytes(&b).is_none() {return Err(Error::Public);}
        row+=1;
    }
    Ok(())
}
fn zc_rows<H:Digest32>(transcript:&mut SemanticTranscript<H>,bytes:&mut Vec<u8>)->Result<[QM31;10],Error> {
    let mut zc=[QM31::ZERO;10];let mut i=0;
    while i<10 {zc[i]=semantic_row(3+i as u8,&[],transcript,bytes)?;i+=1;}
    Ok(zc)
}
fn add_d_tail(mask_sum:QM31,dc:&[QM31;1024])->QM31 {
    let first=d_tail_side(dc,0).mul_m31(M31(512));
    let mask_sum=mask_sum.add(first);
    let second=d_tail_side(dc,28).mul_m31(M31(512));
    mask_sum.add(second)
}
fn d_tail_side(dc:&[QM31;1024],offset:usize)->QM31 {
    // Preserve the shipped h0 term in addition to the j=0 summand.
    d_tail_sum(dc,offset,0,dc[offset])
}
fn d_tail_sum(dc:&[QM31;1024],offset:usize,j:usize,sum:QM31)->QM31 {
    if j==28 {return sum;}
    let next=sum.add(dc[offset+j]);
    d_tail_sum(dc,offset,j+1,next)
}
fn lift_columns(c1:&[Vec<M31>;26],h1:Vec<QM31>,g:&[QM31;1024],d:&[QM31;1024])->[Vec<QM31>;29] {
    let mut columns:[Vec<QM31>;29]=Default::default();
    let mut lane=0;
    while lane<26 {
        let mut column=Vec::with_capacity(1024);
        let mut row=0;
        while row<1024 {column.push(lift(c1[lane][row]));row+=1;}
        columns[lane]=column;lane+=1;
    }
    columns[26]=h1;columns[27]=g.to_vec();columns[28]=d.to_vec();
    columns
}
fn boolean_point(row:usize)->[QM31;10] {
    let mut point=[QM31::ZERO;10];let mut i=0;
    while i<10 {point[i]=if (row>>(9-i))&1==0 {QM31::ZERO} else {QM31::ONE};i+=1;}
    point
}
fn initial_mask_sum(columns:&[Vec<QM31>;29])->QM31 {
    let mut sum=QM31::ZERO;let mut row=0;
    while row<1024 {
        let value=initial_mask_value(columns,row);
        sum=sum.add(value);row+=1;
    }
    sum
}
fn initial_mask_value(columns:&[Vec<QM31>;29],row:usize)->QM31 {
    let point=boolean_point(row);
    let mut semantic=[QM31::ZERO;16];let mut mask_only=[QM31::ZERO;10];
    let mut i=0;
    while i<16 {let value=columns[i][row];semantic[i]=value;i+=1;}
    i=0;while i<10 {let value=columns[16+i][row];mask_only[i]=value;i+=1;}
    aspis_prover::host_arithmetic::state_only_selected_mask_value(&semantic,&mask_only,columns[27][row],&point)
}
fn claim_mask_value(claims:[QM31;29],point:&[QM31;10])->QM31 {
    let mut semantic=[QM31::ZERO;16];let mut mask_only=[QM31::ZERO;10];
    semantic.copy_from_slice(&claims[..16]);
    mask_only.copy_from_slice(&claims[16..26]);
    aspis_prover::host_arithmetic::state_only_selected_mask_value(&semantic,&mask_only,claims[27],point)
}

fn column_coefficients(column:&[QM31],variant:crate::transport::Variant)->[QM31;1024] {
    let rows:&[QM31;1024]=column.try_into().unwrap();
    variant.coefficients(rows)
}
fn extra_claims(columns:&[Vec<QM31>;29],variant:crate::transport::Variant,a:QM31,b:QM31)->[QM31;29] {
    let mut extras=[QM31::ZERO;29];let mut lane=0;
    while lane<29 {let coefficients=column_coefficients(&columns[lane],variant);let value=extra(&coefficients,a,b);extras[lane]=value;lane+=1;}
    extras
}
fn claim_bytes(claims:[[QM31;29];3],extras:[QM31;29])->Vec<u8> {
    let bytes=Vec::with_capacity(3712);
    let bytes=append_claim_bytes(bytes,&claims[0]);
    let bytes=append_claim_bytes(bytes,&claims[1]);
    let bytes=append_claim_bytes(bytes,&claims[2]);
    append_claim_bytes(bytes,&extras)
}
fn append_claim_bytes(mut bytes:Vec<u8>,claims:&[QM31;29])->Vec<u8> {
    let mut lane=0;
    while lane<29 {
        let encoded=WideExact::from_qm31(claims[lane]).to_le_bytes();
        bytes.extend_from_slice(&encoded);lane+=1;
    }
    bytes
}
fn endpoint_bytes(columns:&[Vec<QM31>;29],variant:crate::transport::Variant,z:aspis_core::circle::SecureCirclePoint)->Vec<u8> {
    let mut bytes=Vec::with_capacity(928);let mut lane=0;
    while lane<29 {
        let coefficients=column_coefficients(&columns[lane],variant);
        let value=eval_message(&coefficients,Point{x:z.x,y:z.y});
        bytes.extend_from_slice(&WideExact::from_qm31(value).to_le_bytes());lane+=1;
    }
    bytes
}

pub fn extra(coefficients:&[QM31;1024],a:QM31,b:QM31)->QM31 {
    let mut sum=QM31::ZERO;
    let mut side=0;
    while side<2 {
        let mut value=QM31::ZERO;
        let x=if side==0 {a} else {b};
        let mut j=28;
        while j>0 {j-=1;value=value.mul(x).add(coefficients[28*side+j]);}
        sum=sum.add(value);
        side+=1;
    }
    sum
}

/// One transcript transition, with no captured mutable state.
fn semantic_row<H:Digest32>(row:u8,payload:&[u8],transcript:&mut SemanticTranscript<H>,bytes:&mut Vec<u8>)->Result<QM31,Error> {
    let framed=wire::record(row,payload)?;
    let value=transcript.semantic(row,&framed)?;
    bytes.extend_from_slice(&framed);
    Ok(value)
}


pub fn build<H: Digest32>(public:Public<'_>,compiled:&PoolV1PairForestMergedC1CompilationV1,mask_only:&[Vec<M31>;10],d:&[QM31;1024],g:&[QM31;1024],commitments:&mut impl Commitments,hash:H,variant:crate::transport::Variant)->Result<BuiltSemantics<H>,Error> {
    if compiled.semantic_c1.c1.len()!=16 || &compiled.public_statement!=public.transition(){return Err(Error::Public);}
    let c1=core::array::from_fn(|i| if i<16 {compiled.semantic_c1.c1[i].clone()}else{mask_only[i-16].clone()});
    build_with_helper_mode(public,&c1,d,g,&[QM31::ZERO;1024],|lambda,chi|build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,public.transition().live_snapshot.next_pair_index,lambda,chi).map_err(|_|Error::Public),commitments,hash,variant)
}

/// Real and fixture entry for C1/H1 material from the state-only mask
/// APIs. The compiled trace remains the helper source; only the semantic C1
/// input is replaced with its independently masked clone.
pub fn build_with_material<H: Digest32>(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    noised_semantic_c1: &StateOnlyTraceFoundation,
    mask_only: &[Vec<M31>; 10],
    d: &[QM31; 1024],
    g: &[QM31; 1024],
    h1_padding: &[QM31; 1024],
    commitments: &mut impl Commitments,
    hash: H,
    variant: crate::transport::Variant,
) -> Result<BuiltSemantics<H>, Error> {
    if noised_semantic_c1.c1.len() != 16
        || compiled.semantic_c1.c1.len() != 16
        || &compiled.public_statement != public.transition()
    {
        return Err(Error::Public);
    }
    let c1=clone_semantic_columns(&noised_semantic_c1.c1,mask_only);
    build_with_helper_mode(
        public,
        &c1,
        d,
        g,
        h1_padding,
        |lambda, chi| {
            #[cfg(feature = "r1p-check")]
            if !no_pole(compiled, lambda, chi)? {
                return Err(Error::ActivePole);
            }
            build_pool_v1_pair_forest_copy_helper_v1(
                &compiled.trace,
                public.transition().live_snapshot.next_pair_index,
                lambda,
                chi,
            )
            .map_err(|_| Error::Public)
        },
        commitments,
        hash,
        variant,
    )
}

fn clone_semantic_columns(noised:&[Vec<M31>],mask_only:&[Vec<M31>;10])->[Vec<M31>;26] {
    let mut c1:[Vec<M31>;26]=Default::default();
    let mut i=0;
    while i<16 {c1[i]=noised[i].clone();i+=1;}
    while i<26 {c1[i]=mask_only[i-16].clone();i+=1;}
    c1
}

/// Lean `NoPole (h.build w) λ χ` (R0Z/HonestValidity.lean:97–99), the `VR1`
/// conjunct of `realGameP` (R1Z/GamesR1P.lean:184): on every copy-active row,
/// chi differs from all four slot values (producer and consumer, slots 0 and
/// 1), whatever the slot's weight; an unused slot has value 0. The weighted
/// slots `build_copy_logup_helper` inverts are a subset, so this check is
/// stronger than its `ActivePole`. Only the verdict leaves this function.
#[cfg(feature = "r1p-check")]
pub(crate) fn no_pole(
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    lambda: QM31,
    chi: QM31,
) -> Result<bool, Error> {
    #[cfg(test)]
    if crate::prover::test_hooks::forced_pole() {
        return Ok(false);
    }
    let values = lean_copy_row_values(&compiled.trace, lambda)?;
    let masks = crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1()
        .map_err(|_| Error::Public)?;
    #[cfg(feature = "ct-host-prover")]
    return Ok(crate::ct_pole::all_slots_clear(&values, &masks, chi));
    #[cfg(not(feature = "ct-host-prover"))]
    {
    let mut clear = true;
    for (row, sides) in values.iter().enumerate() {
        if masks[row >> 4] & (1 << (row & 15)) == 0 {
            continue;
        }
        for value in sides.iter().flatten() {
            // No early exit: the work done does not depend on where a pole is.
            clear &= chi != *value;
        }
    }
    Ok(clear)
    }
}

/// Lean `copyRowValues t λ b endpoint slot` (v8-r0-sem-proof-20261008
/// lean/R0P/Copy.lean:449–452) for every row b, side (0 producer, 1 consumer)
/// and slot: the sum of the compressed tuples of the registry endpoints at
/// that row, side and static slot, weights ignored. The static slot is the
/// endpoint's position among the registry endpoints on the same row and side,
/// which is the slot of the generated terminal constants that the Lean
/// `copyLinks` transcribe (`retry_tests::static_slots_are_the_terminal_constants`).
/// The prover's `pool_v1_pair_forest_copy_rows_v1` cannot be used here: it
/// places an endpoint in the first slot whose weight is zero, so a zero-weight
/// endpoint followed by another on the same row and side is overwritten.
#[cfg(feature = "r1p-check")]
pub(crate) fn lean_copy_row_values(
    trace: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
    lambda: QM31,
) -> Result<Vec<[[QM31; 2]; 2]>, Error> {
    let registry = crate::host_forest::build_pool_v1_pair_forest_copy_registry_v1()
        .map_err(|_| Error::Public)?;
    let mut values = alloc::vec![[[QM31::ZERO; 2]; 2]; 1024];
    let mut arity = alloc::vec![[0usize; 2]; 1024];
    let count=registry.len;let mut index=0;
    while index<count {
        let link=registry.data[index];
        (values,arity)=copy_endpoint_values(trace,link.producer,link.tag,lambda,0,values,arity)?;
        (values,arity)=copy_endpoint_values(trace,link.consumer,link.tag,lambda,1,values,arity)?;
        index+=1;
    }
    Ok(values)
}

#[cfg(feature="r1p-check")]
fn copy_endpoint_values(trace:&aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,tuple:aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1,tag:M31,lambda:QM31,side:usize,mut values:Vec<[[QM31;2];2]>,mut arity:Vec<[usize;2]>)->Result<(Vec<[[QM31;2];2]>,Vec<[usize;2]>),Error> {
    let row=usize::from(tuple.row);
    if row>=1024 || arity[row][side]>=2 {return Err(Error::Public);}
    let slot=arity[row][side];arity[row][side]+=1;
    let limbs=copy_tuple_values(trace,tuple)?;
    let compressed=crate::prover_shared::compress_tagged_tuple(tag,&limbs,lambda);
    let next=values[row][side][slot].add(compressed);
    values[row][side][slot]=next;
    Ok((values,arity))
}

#[cfg(feature="r1p-check")]
fn copy_tuple_values(trace:&aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,tuple:aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1)->Result<[M31;16],Error> {
    Ok([
        copy_tuple_limb(trace,tuple.limbs[0])?,
        copy_tuple_limb(trace,tuple.limbs[1])?,
        copy_tuple_limb(trace,tuple.limbs[2])?,
        copy_tuple_limb(trace,tuple.limbs[3])?,
        copy_tuple_limb(trace,tuple.limbs[4])?,
        copy_tuple_limb(trace,tuple.limbs[5])?,
        copy_tuple_limb(trace,tuple.limbs[6])?,
        copy_tuple_limb(trace,tuple.limbs[7])?,
        copy_tuple_limb(trace,tuple.limbs[8])?,
        copy_tuple_limb(trace,tuple.limbs[9])?,
        copy_tuple_limb(trace,tuple.limbs[10])?,
        copy_tuple_limb(trace,tuple.limbs[11])?,
        copy_tuple_limb(trace,tuple.limbs[12])?,
        copy_tuple_limb(trace,tuple.limbs[13])?,
        copy_tuple_limb(trace,tuple.limbs[14])?,
        copy_tuple_limb(trace,tuple.limbs[15])?,
    ])
}

#[cfg(feature="r1p-check")]
fn copy_tuple_limb(trace:&aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,limb:aspis_statement::pool_v1::pair_trace::PoolV1PairTupleLimbV1)->Result<M31,Error> {
    use aspis_statement::pool_v1::pair_trace::{PoolV1PairTraceBankV1,PoolV1PairTupleLimbV1};
    match limb {
        PoolV1PairTupleLimbV1::Zero=>Ok(M31::ZERO),
        PoolV1PairTupleLimbV1::Cell{source,offset}=>{
            let column=source.cell.column as usize;
            let row=source.cell.row as usize;
            match source.bank {
                PoolV1PairTraceBankV1::Stable=>copy_cell(&trace.stable.c1,column,row,offset),
                PoolV1PairTraceBankV1::Late=>copy_cell(&trace.late,column,row,offset),
            }
        }
    }
}
#[cfg(feature="r1p-check")]
fn copy_cell(columns:&[Vec<M31>],column:usize,row:usize,offset:M31)->Result<M31,Error> {
    if column>=columns.len() || row>=columns[column].len() {return Err(Error::Public);}
    Ok(columns[column][row].add(offset))
}
