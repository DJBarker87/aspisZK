//! UNPROVED COST PROBE. Isolated semantic interpolation prover.

    use alloc::vec::Vec;
    use aspis_core::field::{WideExact, CM31, M31, QM31};
    use crate::host_wire::{self as wire, Error, SemanticTranscript};
    use aspis_core::state_only_sumcheck::{
        evaluate_state_only_polynomial, state_only_boundary_sum,
    };

    /// R0 keeps all 28 coefficients on the wire, embedded in E. This is the
    /// same interpolation used by the legacy prover, with a new row driver.
    pub(crate) fn interpolate(values: &[QM31; 28]) -> [QM31; 28] {
        let mut out = [QM31::ZERO; 28];
        let mut i=0;
        while i<28 {
            let mut basis = [M31::ZERO; 28];
            basis[0] = M31::ONE;
            let mut degree = 0;
            let mut denominator = M31::ONE;
            let mut j=0;
            while j<28 {
                if i!=j {
                    let mut k=degree+2;
                    while k>0 {
                        k-=1;
                        let shifted=if k==0 {M31::ZERO} else {basis[k-1]};
                        basis[k]=shifted.sub(basis[k].mul(M31(j as u32)));
                    }
                    degree+=1;
                    denominator=denominator.mul(M31(i as u32).sub(M31(j as u32)));
                }
                j+=1;
            }
            let scale = values[i].mul_m31(denominator.inv());
            let mut k=0;
            while k<28 {out[k]=out[k].add(scale.mul_m31(basis[k]));k+=1;}
            i+=1;
        }
        out
    }

pub(crate) trait Oracle:Sync {
    fn evaluate(&self,point:&[QM31;10])->Result<QM31,Error>;
}

    pub fn prove_sumcheck<H: aspis_core::Digest32>(
        transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>,
        initial_claim: QM31,
        oracle: &impl Oracle,
    ) -> Result<([QM31; 10], QM31), Error> {
        prove_sumcheck_rounds(transcript,output,[QM31::ZERO;10],initial_claim,0,oracle)
    }

fn prove_sumcheck_rounds<H:aspis_core::Digest32,F:Oracle>(transcript:&mut SemanticTranscript<H>,output:&mut Vec<u8>,point:[QM31;10],running:QM31,round:usize,oracle:&F)->Result<([QM31;10],QM31),Error> {
    if round==10 {
        if oracle.evaluate(&point)?!=running {return Err(Error::Terminal);}
        return Ok((point,running));
    }
    let (point,running)=prove_sumcheck_round(transcript,output,point,running,round,oracle)?;
    prove_sumcheck_rounds(transcript,output,point,running,round+1,oracle)
}
fn prove_sumcheck_round<H:aspis_core::Digest32,F:Oracle>(transcript:&mut SemanticTranscript<H>,output:&mut Vec<u8>,mut point:[QM31;10],mut running:QM31,round:usize,oracle:&F)->Result<([QM31;10],QM31),Error> {
            let remaining = 9 - round;
            let mut values = [QM31::ZERO; 28];
            #[cfg(feature="ct-host-prover")]
            {
                let assignments=1usize<<remaining;
                let evaluations=crate::host_work::map(100+round,28*assignments,|i| {
                    evaluate_assignment(oracle,point,round,assignments,i)
                });
                // Same sample and assignment order, including error selection.
                let mut i=0;
                while i<evaluations.len() {
                    values[i/assignments]=values[i/assignments].add(evaluations[i]?);
                    i+=1;
                }
            }
            #[cfg(not(feature="ct-host-prover"))]
            {
            for (sample, value) in values.iter_mut().enumerate() {
                point[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                for assignment in 0..1usize << remaining {
                    for offset in 0..remaining {
                        point[round + 1 + offset] =
                            if (assignment >> (remaining - 1 - offset)) & 1 == 0 {
                                QM31::ZERO
                            } else {
                                QM31::ONE
                            };
                    }
                    *value = value.add(oracle.evaluate(&point)?);
                }
            }
            }
            let polynomial = interpolate(&values);
            if state_only_boundary_sum(&polynomial) != running {
                return Err(Error::Boundary { round });
            }
            let polynomial_bytes=encode_polynomial(&polynomial);
            let framed=wire::record(15+round as u8,&polynomial_bytes)?;
            point[round] = transcript.semantic(15 + round as u8, &framed)?;
            output.extend_from_slice(&framed);
            running = evaluate_state_only_polynomial(&polynomial, point[round]);
    Ok((point,running))
}

fn evaluate_assignment<F:Oracle>(oracle:&F,point:[QM31;10],round:usize,assignments:usize,i:usize)->Result<QM31,Error> {
    let remaining=9-round;
                    let sample=i/assignments;let assignment=i%assignments;
                    let mut at=point;
                    at[round]=QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
                    let mut offset=0;
                    while offset<remaining {
                        at[round+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {QM31::ZERO}else{QM31::ONE};
                        offset+=1;
                    }
                    oracle.evaluate(&at)
}

fn encode_polynomial(polynomial:&[QM31;28])->Vec<u8> {
    let mut bytes=Vec::with_capacity(896);let mut i=0;
    while i<28 {
        let encoded=WideExact::from_qm31(polynomial[i]).to_le_bytes();
        bytes.extend_from_slice(&encoded);i+=1;
    }
    bytes
}
