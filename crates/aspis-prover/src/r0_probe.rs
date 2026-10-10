//! Unproved COST PROBE; separate matching prover, no claims.
//! Host R0 prover: real C1/C2 commitments at the semantic callback times,
//! then R-G's transported opening. Inputs remain semantic row indexed.
use crate::state_only_candidate_prefix::r0::{build_pair_forest_transported, Column, Commitments};
use aspis_core::r0::CodeField;
use aspis_core::{
    field::{WideExact as E, CM31, M31, QM31},
    r0_probe::{
        basis::{BasisSize, NaturalBasis},
        prover::{self, Commitment, CommitmentTime, EncodingDomain},
        transcript::SemanticBoundary,
        Error as OpeningError, Message,
    },
    state_only_prefix::r0::{Error as SemanticError, Prefix},
    HashFn,
};
use aspis_statement::{
    pool_v1::{
        pair_forest_semantic_terminal::r0::Public,
        pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
    },
    r0_probe::{Error, OPENING_OFFSET, PROOF_BYTES},
};

struct Backend {
    hash: HashFn,
    domain: EncodingDomain,
    messages: Vec<Message<E>>,
    c1: Option<Commitment>,
    c2: Option<Commitment>,
    error: Option<OpeningError>,
}
impl Backend {
    fn commit(&mut self, time: CommitmentTime) -> Result<[u8; 32], SemanticError> {
        match Commitment::new(self.hash, &self.domain, time, &self.messages) {
            Ok(c) => {
                let root = c.root();
                match time {
                    CommitmentTime::C1 => self.c1 = Some(c),
                    CommitmentTime::C2 => self.c2 = Some(c),
                }
                Ok(root)
            }
            Err(e) => {
                self.error = Some(e);
                Err(SemanticError::Public)
            }
        }
    }
}
impl Commitments for Backend {
    fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], SemanticError> {
        for (i, col) in columns.into_iter().enumerate() {
            self.messages[if i < 26 { i } else { 28 }] = match col {
                Column::Base(v) => v.map(E::from_m31),
                Column::Extension(v) => v.map(E::from_qm31),
            };
        }
        self.commit(CommitmentTime::C1)
    }
    fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], SemanticError> {
        for (i, col) in columns.into_iter().enumerate() {
            self.messages[26 + i] = col.map(E::from_qm31);
        }
        self.commit(CommitmentTime::C2)
    }
}

/// One P1 proof for either supported PF public variant. Mask material is
/// supplied by the caller; this function does not certify its distribution.
pub fn r0_prove(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    mask_only: &[Vec<M31>; 10],
    d: &[QM31; 1024],
    g: &[QM31; 1024],
    hash: HashFn,
) -> Result<Vec<u8>, Error> {
    let mut backend = Backend {
        hash,
        domain: EncodingDomain::new()?,
        messages: vec![[E::ZERO; 1024]; 29],
        c1: None,
        c2: None,
        error: None,
    };
    let semantic = match build_pair_forest_transported(
        public,
        compiled,
        mask_only,
        d,
        g,
        &mut backend,
        hash,
    ) {
        Ok(s) => s,
        Err(e) => {
            return Err(backend
                .error
                .map(Error::Opening)
                .unwrap_or(Error::Semantic(e)))
        }
    };
    let boundary = SemanticBoundary::from_verified_parts(
        semantic.state_before_z0,
        semantic.roots,
        semantic.challenges.with_alphas(&semantic.alpha),
        Prefix::parse(&semantic.bytes)?.point_claims()?,
        true,
    )?;
    let basis = NaturalBasis::new(BasisSize::Initial)?;
    let opening = prover::prove(
        hash,
        &basis,
        &boundary,
        &backend.messages,
        backend.c1.as_ref().ok_or(OpeningError::Commitment)?,
        backend.c2.as_ref().ok_or(OpeningError::Commitment)?,
    )?
    .encode()?;
    // One shared row-26 record; both prover layers must use exactly D13.
    if semantic.bytes[OPENING_OFFSET..] != opening[..semantic.bytes.len() - OPENING_OFFSET] {
        return Err(OpeningError::Schedule.into());
    }
    let mut bytes = Vec::with_capacity(PROOF_BYTES);
    bytes.extend_from_slice(&semantic.bytes[..OPENING_OFFSET]);
    bytes.extend_from_slice(&opening);
    Ok(bytes)
}

pub fn prove_fixture(
    fixture: &crate::r0_fixture::Fixture,
) -> Result<Vec<u8>, aspis_statement::r0_probe::Error> {
    let masks = core::array::from_fn(|lane| {
        (0..1024)
            .map(|r| M31(((lane + 16) * 103 + r * 7 + 19) as u32))
            .collect()
    });
    let d = core::array::from_fn(|row| QM31 {
        c0: CM31::new(M31(row as u32 + 3), M31(11)),
        c1: CM31::new(M31(17), M31(19)),
    });
    let g = core::array::from_fn(|row| QM31::from_cm31(CM31::from_m31(M31(row as u32 + 5))));
    r0_prove(
        fixture.public(),
        &fixture.compiled,
        &masks,
        &d,
        &g,
        crate::HOST_HASH,
    )
}
