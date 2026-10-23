//! Shape diagnostic only: minimal commitment layout, actual field/opening types.
extern crate alloc;
use alloc::vec::Vec;
use aspis_core::r0::CodeField;
use aspis_core::{field::{WideExact as E,M31,QM31},r0::{domain::FibreIndex,wire::FibreOpening}};
#[derive(Clone,Copy,PartialEq,Eq)]
pub enum CommitmentTime {C1,C2}
pub enum Word {Base(Vec<M31>),Secure(Vec<QM31>)}
impl Word {
    fn value(&self,i:usize)->E {
        match self {Self::Base(w)=>E::from_m31(w[i]),Self::Secure(w)=>E::from_qm31(w[i])}
    }
}
pub struct Commitment {pub time:CommitmentTime,pub lanes:Vec<usize>,pub words:Vec<Word>}
impl Commitment {
    pub fn fill_opening(&self,u:FibreIndex,out:&mut FibreOpening) {
        out.values=fill_values(self,u,out.values,0);
        let path=opening_path(self.time);
        out.paths[path]=[[[0;32];7];6];
    }
}
fn fill_values(c:&Commitment,u:FibreIndex,mut values:[[E;29];4],j:usize)->[[E;29];4] {
    if j==c.lanes.len() {return values;}
    let lane=c.lanes[j];
    let row=opening_lane_values(&c.words[j],u);
    values[0][lane]=row[0];values[1][lane]=row[1];
    values[2][lane]=row[2];values[3][lane]=row[3];
    fill_values(c,u,values,j+1)
}
fn opening_lane_values(word:&Word,u:FibreIndex)->[E;4] {
    let at=4*u.get();
    [word.value(at),word.value(at+1),word.value(at+2),word.value(at+3)]
}

fn opening_path(time:CommitmentTime)->usize {match time {CommitmentTime::C1=>0,CommitmentTime::C2=>1}}

pub fn append_opening_values(out:Vec<u8>,opening:FibreOpening)->Vec<u8> {
    let out=append_opening_base_row(out,&opening.values[0]);
    let out=append_opening_base_row(out,&opening.values[1]);
    let out=append_opening_base_row(out,&opening.values[2]);
    let out=append_opening_base_row(out,&opening.values[3]);
    let out=append_opening_secure_row(out,&opening.values[0]);
    let out=append_opening_secure_row(out,&opening.values[1]);
    let out=append_opening_secure_row(out,&opening.values[2]);
    append_opening_secure_row(out,&opening.values[3])
}
fn append_opening_base_row(mut out:Vec<u8>,row:&[E;29])->Vec<u8> {
    let mut lane=0;
    while lane<26 {
        let bytes=row[lane].to_le_bytes();out.extend_from_slice(&bytes[..4]);lane+=1;
    }
    let bytes=row[28].to_le_bytes();out.extend_from_slice(&bytes[..16]);
    out
}
fn append_opening_secure_row(mut out:Vec<u8>,row:&[E;29])->Vec<u8> {
    let mut lane=26;
    while lane<28 {
        let bytes=row[lane].to_le_bytes();out.extend_from_slice(&bytes[..16]);lane+=1;
    }
    out
}
