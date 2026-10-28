from pathlib import Path
import subprocess,re,json,hashlib,difflib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='crates/aspis-statement/src/pool_v1/pair_terminal.rs';src=subprocess.check_output(['git','show',rev+':'+path],text=True)
a=src.index('pub fn decode_pool_v1_pair_verified_afterstate_v1(');b=src.index('\nfn exact<const',a);body=src[a:b];body=body[body.index('    if bytes.len()'):];assert body.rstrip().endswith('}')
body=body.replace('super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION','super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION').replace('decode_digest_canonical(', 'decode('.replace('validate_verified_afterstate(&afterstate)?','validate(&afterstate)?')
cut='''fn NBN_decode_cut<F,V>(bytes:&[u8],mut decode:F,mut validate:V)->Result<PoolV1PairVerifiedAfterstateV1,PoolV1PairVerifierTransportErrorV1>
where F:FnMut(&[u8;32])->Result<Digest,crate::atomic_statement::AtomicStatementError>, V:FnMut(&PoolV1PairVerifiedAfterstateV1)->Result<(),PoolV1PairVerifierTransportErrorV1> {
'''+body
vs=re.findall(r'^    (\w+),',re.search(r'pub enum PoolV1PairVerifierTransportErrorV1 \{([^}]+)',src).group(1),re.M)
err='fn NBN_error()->PoolV1PairVerifierTransportErrorV1{match kani::any::<u8>(){'+','.join((str(i) if i<len(vs)-1 else '_')+'=>PoolV1PairVerifierTransportErrorV1::'+v for i,v in enumerate(vs))+'}}\n'
digest='['+','.join(['aspis_core::field::M31(kani::any())']*8)+']'
s='#![allow(non_snake_case,unused_variables)]\nuse super::*;\n'+err+f'fn NBN_digest()->Digest{{{digest}}}\n'+cut
s+='''
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_decode_children(){
 let mut bytes:[u8;688]=kani::any();
 // Parent prefix success is the separately CLOSED ordered header cut.
 bytes[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
 bytes[4]=POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
 bytes[5]=super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
 bytes[6]=POOL_V1_DIGEST_ENCODING_VERSION;bytes[7]=1;
 let decoded:[Digest;21]=DECODED_ARRAY;
 let first_error:usize=kani::any();kani::assume(first_error<=21);
 let observed_byte:usize=kani::any();kani::assume(observed_byte<32);
 let observed_row:usize=kani::any();kani::assume(observed_row<20);
 let status:Result<(),PoolV1PairVerifierTransportErrorV1>=if kani::any::<bool>() {Ok(())} else {Err(NBN_error())};
 let mut calls=0usize;let mut validation_calls=0usize;
 let result=NBN_decode_cut(&bytes,|input|{
   let k=calls;calls+=1;assert!(k<21);
   let start=if k==0 {16} else {48+32*(k-1)};
   assert_eq!(input[observed_byte],bytes[start+observed_byte]);
   if k==first_error {Err(crate::atomic_statement::AtomicStatementError::NonCanonicalDigest)} else {Ok(decoded[k])}
 },|a|{
   validation_calls+=1;
   assert_eq!(a.next_pair_index,u64::from_le_bytes(bytes[8..16].try_into().unwrap()));
   assert_eq!(a.next_root,decoded[0]);
   assert_eq!(a.next_frontier[observed_row],decoded[observed_row+1]);
   status
 });
 if first_error<21 {assert_eq!(result,Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate));assert_eq!(calls,first_error+1);assert_eq!(validation_calls,0);}
 else {assert_eq!(calls,21);assert_eq!(validation_calls,1);match status {
   Err(e)=>assert_eq!(result,Err(e)),
   Ok(())=>{let a=result.unwrap();assert_eq!(a.next_root,decoded[0]);assert_eq!(a.next_frontier[observed_row],decoded[observed_row+1]);assert_eq!(a.next_pair_index,u64::from_le_bytes(bytes[8..16].try_into().unwrap()));}
 }}
}
'''.replace('DECODED_ARRAY','['+','.join(['NBN_digest()']*21)+']')
(E/'NBN_decode.rs.txt').write_text(s)
inc='\n#[cfg(kani)]\n#[path="NBN_decode.rs"]\nmod NBN_decode;\n'
# Previous owned scratch inclusion remains, so the patch is against frozen source.
oldinc='\n#[cfg(kani)]\n#[path="NBN_codecs.rs"]\nmod NBN_codecs;\n'
patch=''.join(difflib.unified_diff(src.splitlines(True),(src+oldinc+inc).splitlines(True),fromfile='a/'+path,tofile='b/'+path))
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_decode.rs'))
(E/'NBN_decode.patch').write_text(patch)
(E/'NBN_DECODE_EXTRACTION.json').write_text(json.dumps(dict(frozen_revision=rev,source=path,source_body='decode_pool_v1_pair_verified_afterstate_v1',cuts=['DigestDecode: SAME 21 exact32 byte images and ordered calls','validate_verified_afterstate: SAME full parsed record'],invariant='arbitrary raw reply records; first_error in0..21; no canonicality or valid-index assumption',unwind=1881,protocol_loops=0),indent=2)+'\n')
