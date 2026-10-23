//! Host semantic transcript and record owner. Verifier wire remains frozen.
use alloc::vec::Vec;
use aspis_core::{Digest32,circle::SecureCirclePoint,field::{WideExact,QM31}};
use crate::sampler::{circle_sample,qm31_sample,CircleRow};
pub use crate::r1_wire::{Error,Challenges,DOMAIN,row_shape,statement_points};

fn validate_record_fields(row:u8,payload:&[u8])->Result<(),Error> {
    let mut value=0;
    while value<payload.len()/32 {
        let start=32*value;
        let x=WideExact::from_le_bytes(&payload[start..start+32]).ok_or(Error::NonCanonical{row,value})?;
        if x.c1()!=QM31::ZERO {return Err(Error::NonCanonical{row,value});}
        value+=1;
    }
    Ok(())
}

pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if record.len() != 5 + size {
        return Err(Error::Length { row });
    }
    if record[0] != tag {
        return Err(Error::Tag { row });
    }
    if u32::from_le_bytes([record[1], record[2], record[3], record[4]]) as usize != size {
        return Err(Error::Length { row });
    }
    let payload = &record[5..];
    if row >= 14 {
        validate_record_fields(row, payload)?;
    }
    Ok(payload)
}

pub fn record(row: u8, payload: &[u8]) -> Result<Vec<u8>, Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if payload.len() != size {
        return Err(Error::Length { row });
    }
    let mut out = Vec::with_capacity(5 + size);
    out.push(tag);
    out.extend_from_slice(&(size as u32).to_le_bytes());
    out.extend_from_slice(payload);
    parse_record(row, &out)?;
    Ok(out)
}

#[derive(Clone)]
pub struct SemanticTranscript<H: Digest32> {
    state: [u8; 32],
    hash: H,
    next_row: u8,
}

impl<H: Digest32> SemanticTranscript<H> {
    pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32]) -> Result<Self, Error> {
        let length = u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
        Ok(Self {
            state: hash.digest(&[DOMAIN, &[0], &length.to_le_bytes(), public_bytes, c1_root]),
            hash,
            next_row: 0,
        })
    }
    pub fn state(&self) -> [u8; 32] {
        self.state
    }
    pub fn next_row(&self) -> u8 {
        self.next_row
    }

    fn sample_block_validated(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
        if row != self.next_row {
            return Err(Error::RowOrder {
                expected: self.next_row,
                actual: row,
            });
        }
        // Exactly one absorb, one squeeze and one advance. Both reads
        // use s_abs; advancing from the challenge block would be wrong.
        let absorbed = self.hash.digest(&[&self.state, &[0, 0xa0 + row], framed]);
        let block = self.hash.digest(&[&absorbed, &[1]]);
        self.state = self.hash.digest(&[&absorbed, &[2]]);
        self.next_row += 1;
        Ok(block)
    }
    fn sample_block(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
        if row != self.next_row {
            return Err(Error::RowOrder {
                expected: self.next_row,
                actual: row,
            });
        }
        parse_record(row, framed)?;
        self.sample_block_validated(row, framed)
    }

    pub fn semantic(&mut self, row: u8, framed: &[u8]) -> Result<QM31, Error> {
        if row > 24 {
            return Err(Error::InvalidRow);
        }
        Ok(qm31_sample(&self.sample_block(row, framed)?))
    }
    /// R-B's one-block reference-circle map, including fixed fallback.
    /// The legacy Transcript method has a different parameter sampler.
    pub fn challenge_reference_circle_point(
        &mut self,
        row: u8,
        framed: &[u8],
    ) -> Result<SecureCirclePoint, Error> {
        let circle_row = match row {
            25 => CircleRow::First,
            26 => CircleRow::Second,
            _ => return Err(Error::InvalidRow),
        };
        Ok(circle_sample(&self.sample_block(row, framed)?, circle_row))
    }
}
