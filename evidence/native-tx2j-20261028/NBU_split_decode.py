from pathlib import Path
import re
E=Path(__file__).resolve().parent
p=E/'NBU_decode.rs.txt';s=p.read_text()
attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_decode_children')].replace('1881','34')
items={
'exact32':'''let input:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);let out=exact::<32>(&input).unwrap();assert_eq!(out[j],input[j]);''',
'exact8':'''let input:[u8;8]=kani::any();let j:usize=kani::any();kani::assume(j<8);let out=exact::<8>(&input).unwrap();assert_eq!(out[j],input[j]);''',
'decode_window':'''let input:[u8;688]=kani::any();let k:usize=kani::any();kani::assume(k<21);let j:usize=kani::any();kani::assume(j<32);let start=16+32*k;let view=&input[start..start+32];assert_eq!(view.len(),32);assert_eq!(view[j],input[start+j]);assert_eq!(view.as_ptr(),input.as_ptr().wrapping_add(start));''',
'decode_prefix':'''let input:[u8;688]=kani::any();let mut calls=0usize;let result=NBU_decode_cut(&input,|_|{calls+=1;Err(crate::atomic_statement::AtomicStatementError::NonCanonicalDigest)},|_|{assert!(false);Ok(())});let expected=if input[..4]!=POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC[0..4]{PoolV1PairVerifierTransportErrorV1::WrongMagic}else if input[4]!=POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION{PoolV1PairVerifierTransportErrorV1::WrongVersion}else if input[5]!=super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION{PoolV1PairVerifierTransportErrorV1::WrongPairFormat}else if input[6]!=POOL_V1_DIGEST_ENCODING_VERSION{PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding}else if input[7]!=1{PoolV1PairVerifierTransportErrorV1::WrongSuccessCode}else{PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate};assert_eq!(result,Err(expected));assert_eq!(calls,if expected==PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate{1}else{0});'''
}
for name,body in items.items():
 for neg in ['', '_negative']:
  b=body.replace('assert_eq!','assert_ne!',1) if neg else body
  s+='\n'+attrs+'fn NBU_'+name+neg+'(){'+b+'}\n'
p.write_text(s)
