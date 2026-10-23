//! UNPROVED COST PROBE. Own D14 semantic prover; original prover unchanged.
use alloc::vec::Vec;
use aspis_core::{field::{WideExact, M31, QM31, P},Digest32,r0::{domain::Point,encoder::eval_message}};
use crate::host_wire::{self as wire,Challenges,Error,SemanticTranscript};
use aspis_statement::{multilinear_evaluate_qm31,state_only_copy_helper_sum,StateOnlyTraceFoundation,pool_v1::{pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1,pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1}};
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
        let mut claims = [[QM31::ZERO; 29]; 3];
        let points=wire::statement_points(point);
        let mut p=0;
        while p<3 {
            let mut lane=0;
            while lane<29 {
                claims[p][lane]=multilinear_evaluate_qm31(&columns[lane],&points[p]).ok_or(Error::Public)?;
                lane+=1;
            }
            p+=1;
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
        let mut transcript = SemanticTranscript::new(hash, &public.public_bytes().map_err(|_|Error::Public)?, &c1_root)?;
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
        let (alpha, _) = crate::host_sumcheck::prove_sumcheck(
            &mut transcript,
            &mut bytes,
            mask_sum,
            |point| {
                let claims = point_claims(&columns, point)?;
                let terminal = public.terminal_qm31(&claims, point, &challenges).map_err(|_|Error::Public)?;
                let mask=claim_mask_value(claims[0],point);
                Ok(mask.add(eta.mul(terminal)).add(extra(&dc,point[8],point[9])))
            },
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


fn check_semantic_columns(c1:&[Vec<M31>;26],d:&[QM31;1024],g:&[QM31;1024])->Result<(),Error> {
        let mut lane=0;
        while lane<26 {
            if c1[lane].len()!=1024 {return Err(Error::Public);}
            let mut row=0;
            while row<1024 {
                if c1[lane][row].0>=P {return Err(Error::Public);}
                row+=1;
            }
            lane+=1;
        }
        let mut at=0;
        while at<2048 {
            let x=if at<1024 {d[at]} else {g[at-1024]};
            let mut b=[0;16];
            x.write_le_bytes(&mut b);
            if QM31::from_le_bytes(&b).is_none() {return Err(Error::Public);}
            at+=1;
        }
    Ok(())
}
fn zc_rows<H:Digest32>(transcript:&mut SemanticTranscript<H>,bytes:&mut Vec<u8>)->Result<[QM31;10],Error> {
    let mut zc=[QM31::ZERO;10];let mut i=0;
    while i<10 {zc[i]=semantic_row(3+i as u8,&[],transcript,bytes)?;i+=1;}
    Ok(zc)
}
fn add_d_tail(mut mask_sum:QM31,dc:&[QM31;1024])->QM31 {
        let mut side=0;
        while side<2 {
            let mut sum=dc[28*side];
            let mut j=0;
            while j<28 {sum=sum.add(dc[28*side+j]);j+=1;}
            mask_sum=mask_sum.add(sum.mul_m31(M31(512)));
            side+=1;
        }
    mask_sum
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
        let point=boolean_point(row);
        let mut semantic=[QM31::ZERO;16];let mut mask_only=[QM31::ZERO;10];
        let mut i=0;
        while i<16 {semantic[i]=columns[i][row];i+=1;}
        i=0;while i<10 {mask_only[i]=columns[16+i][row];i+=1;}
        sum=sum.add(aspis_core::state_only_hiding::state_only_selected_mask_value(&semantic,&mask_only,columns[27][row],&point));
        row+=1;
    }
    sum
}
fn claim_mask_value(claims:[QM31;29],point:&[QM31;10])->QM31 {
    let mut semantic=[QM31::ZERO;16];let mut mask_only=[QM31::ZERO;10];
    let mut i=0;
    while i<16 {semantic[i]=claims[i];i+=1;}
    i=0;while i<10 {mask_only[i]=claims[16+i];i+=1;}
    aspis_core::state_only_hiding::state_only_selected_mask_value(&semantic,&mask_only,claims[27],point)
}
fn column_coefficients(column:&[QM31],variant:crate::transport::Variant)->[QM31;1024] {
    let rows:&[QM31;1024]=column.try_into().unwrap();
    variant.coefficients(rows)
}
fn extra_claims(columns:&[Vec<QM31>;29],variant:crate::transport::Variant,a:QM31,b:QM31)->[QM31;29] {
    let mut extras=[QM31::ZERO;29];let mut lane=0;
    while lane<29 {extras[lane]=extra(&column_coefficients(&columns[lane],variant),a,b);lane+=1;}
    extras
}
fn claim_bytes(claims:[[QM31;29];3],extras:[QM31;29])->Vec<u8> {
    let mut bytes=Vec::with_capacity(3712);let mut p=0;
    while p<3 {
        let mut lane=0;
        while lane<29 {bytes.extend_from_slice(&WideExact::from_qm31(claims[p][lane]).to_le_bytes());lane+=1;}
        p+=1;
    }
    let mut lane=0;
    while lane<29 {bytes.extend_from_slice(&WideExact::from_qm31(extras[lane]).to_le_bytes());lane+=1;}
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
    let masks = aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1()
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
    let registry = aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1()
        .map_err(|_| Error::Public)?;
    let mut values = alloc::vec![[[QM31::ZERO; 2]; 2]; 1024];
    let mut arity = alloc::vec![[0usize; 2]; 1024];
    let mut index=0;
    while index<registry.len() {
        let link=registry[index];
        let mut side=0;
        while side<2 {
            let tuple=if side==0 {link.producer} else {link.consumer};
            let row=usize::from(tuple.row);
            if row>=1024 || arity[row][side]>=2 {return Err(Error::Public);}
            let slot=arity[row][side];arity[row][side]+=1;
            let mut limbs=[M31::ZERO;16];
            let mut i=0;
            while i<16 {limbs[i]=copy_tuple_limb(trace,tuple.limbs[i])?;i+=1;}
            values[row][side][slot]=values[row][side][slot]
                .add(aspis_statement::compress_tagged_tuple(link.tag,&limbs,lambda));
            side+=1;
        }
        index+=1;
    }
    Ok(values)
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
