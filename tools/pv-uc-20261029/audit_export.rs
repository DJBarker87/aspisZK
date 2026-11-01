//! Audit-only serialization of every field of the exact RealR1 compiled input.
use aspis_core::field::M31;
use aspis_statement::{pool_v1::*,poseidon2::Digest};
fn words(out:&mut Vec<u8>,v:&[M31]){out.extend_from_slice(&(v.len() as u64).to_le_bytes());for x in v{out.extend_from_slice(&x.0.to_le_bytes());}}
fn matrix<const N:usize>(out:&mut Vec<u8>,v:&[Vec<M31>;N]){out.extend_from_slice(&(N as u64).to_le_bytes());for col in v{words(out,col);}}
fn digest(out:&mut Vec<u8>,d:&Digest){words(out,d);}
pub fn capture(dir:&std::path::Path,c:&PoolV1PairForestMergedC1CompilationV1){
 let mut out=b"PVUC-PROOF-INPUT-V1".to_vec();
 matrix(&mut out,&c.trace.stable.c1);matrix(&mut out,&c.trace.late);
 out.push(match c.trace.variant{PoolV1PairTraceVariantV1::PrivateTransfer=>0,PoolV1PairTraceVariantV1::Withdrawal=>1});
 words(&mut out,&c.trace.private_directions);
 for v in &c.trace.value_bits{words(&mut out,v);}
 match &c.trace.public_outputs{
  PoolV1PairTracePublicOutputsV1::PrivateTransfer{anchor,nullifier,recipient_commitment,change_commitment,output_pair}=>{out.push(0);for d in [anchor,nullifier,recipient_commitment,change_commitment,output_pair]{digest(&mut out,d);}},
  PoolV1PairTracePublicOutputsV1::Withdrawal{anchor,nullifier,change_commitment,output_pair}=>{out.push(1);for d in [anchor,nullifier,change_commitment,output_pair]{digest(&mut out,d);}}
 }
 out.extend_from_slice(&encode_pool_v1_pair_verified_afterstate_v1(&c.trace.afterstate).unwrap());
 matrix(&mut out,&c.semantic_c1.c1);
 let mut public=vec![0;POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
 encode_pool_v1_pair_late_public_statement_v1(&c.public_statement,&mut public).unwrap();out.extend(public);
 use std::os::unix::fs::OpenOptionsExt;use std::io::Write;
 let mut f=std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(dir.join("proof-input.bin")).unwrap();
 f.write_all(&out).unwrap();f.sync_all().unwrap();
}
