from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NCP_digest.rs.txt';s=p.read_text();(E/'NCP_digest_v2.rs.txt').write_text(s)
attrs=s[s.index('#[kani::stub('):s.index('fn NCP_encode_contract')]
# attrs contains only stubs/unwind, no proof marker.
extra='''
#[kani::ensures(|r: &Result<Digest,AtomicStatementError>| *r != NCP_ref_decode(b)))]
fn NCP_digest_inverted(b:&[u8;32])->Result<Digest,AtomicStatementError>{crate::atomic_statement::decode_digest_canonical(b)}
#[kani::ensures(|_: &Result<Digest,AtomicStatementError>| true)]
fn NCP_digest_weak(b:&[u8;32])->Result<Digest,AtomicStatementError>{crate::atomic_statement::decode_digest_canonical(b)}
#[kani::requires(a.len()==1 && z.len()==1)]
#[kani::modifies(a)]
#[kani::ensures(|_: &Result<Digest,AtomicStatementError>| true)]
fn NCP_digest_frame(a:&mut [u8],z:&mut [u8],b:&[u8;32])->Result<Digest,AtomicStatementError>{a[0]=1;z[0]=2;crate::atomic_statement::decode_digest_canonical(b)}
#[kani::proof_for_contract(NCP_digest_inverted)]
fn NCP_digest_inverted_check(){let b:[u8;32]=kani::any();let _=NCP_digest_inverted(&b);}
#[kani::proof_for_contract(NCP_digest_weak)]
fn NCP_digest_weak_check(){let b:[u8;32]=kani::any();let _=NCP_digest_weak(&b);}
#[kani::proof]
fn NCP_digest_real(){let b:[u8;32]=kani::any();assert_eq!(NCP_digest_weak(&b),NCP_ref_decode(&b));}
#[kani::proof]
#[kani::stub_verified(NCP_digest_weak)]
fn NCP_digest_stub(){let b:[u8;32]=kani::any();assert_eq!(NCP_digest_weak(&b),NCP_ref_decode(&b));}
#[kani::proof_for_contract(NCP_digest_frame)]
fn NCP_digest_frame_check(){let b:[u8;32]=kani::any();let mut a=[0u8];let mut z=[0u8];let _=NCP_digest_frame(&mut a,&mut z,&b);}
#[kani::proof]
fn NCP_digest_frame_real(){let b:[u8;32]=kani::any();let mut a=[0u8];let mut z=[0u8];assert_eq!(NCP_digest_frame(&mut a,&mut z,&b),NCP_ref_decode(&b));assert!(a[0]==1 && z[0]==2);}
'''.replace('NCP_ref_decode(b)))]','NCP_ref_decode(b))]')
import re
extra=re.sub(r'(#\[kani::proof(?:_for_contract\([^\n]+\))?\]\n)',lambda m:m[0]+attrs,extra)
p.write_text(s+extra)
