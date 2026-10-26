#!/usr/bin/env python3
"""Owned candidate: constructor query hook executes the full frozen driver body."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
f=O/'core-workspace/crates/aspis-core/src/r0_transcript.rs';source=f.read_text()
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
body=item(source,'pub fn queries_from_pairs(')
twin=body.replace('pub fn queries_from_pairs(','pub fn s126_queries_from_pairs(',1)
wrapper=(R/'tools/s1-query-pairs-cut-20261025/wrapper.rs').read_text()
f.write_text(source+'\n#[cfg(kani)]\n'+twin+'\n'+wrapper)
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text()
a=s.index('fn pairs_stub(');b=s.index('// Only a primitive multiplication',a)
s=s[:a]+'''fn pairs_stub(blocks:&[[u8;32];8],advances:&[[u8;32];8])
 ->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{unsafe{
 assert!(STAGE==5);assert!(DIGEST_CALLS==30);
 let mut k=0;while k<8{
  same_bytes(&blocks[k],&HASHES[14+2*k]);same_bytes(&advances[k],&HASHES[15+2*k]);k+=1;
 }
 let actual=aspis_core::r0_transcript::s126_queries_from_pairs(blocks,advances);
 match actual{Ok((q,next))=>{QUERY=q;STATES[5]=next;},Err(_)=>{FAIL_AT=0;}}
 STAGE=6;actual
}}
'''+s[b:]
needle='#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]'
assert s.count(needle)==7
s=s.replace(needle,needle+'\n#[kani::stub(aspis_core::r0_transcript::QueryScan::scan,aspis_core::r0_transcript::s126_scan_reply)]')
s=s.replace('let result=Prepared::new(&sem,&view,Hash,&mut scratch);','''let tape=kani::any::<[aspis_core::r0_transcript::S126Reply;8]>();
 let mut t=0;while t<8{kani::assume(tape[t].1<=22);kani::assume(tape[t].2<=64);t+=1;}
 // Observer coordinates inspect ghosts only; they do not select replies.
 aspis_core::r0_transcript::s126_init(tape,0,0,0);
 let result=Prepared::new(&sem,&view,Hash,&mut scratch);
 let fail_at=unsafe{FAIL_AT};''')
s=s.replace('assert!(out.queries[i]==queries[i])','assert!(out.queries[i]==unsafe{QUERY[i]})')
# Query failure is determined by the driver; the remaining input selects only
# the independent native claim failure/success path.
old='let fail_at=kani::any::<u8>()%3;'
assert s.count(old)==1
s=s.replace(old,'let fail_at=1+kani::any::<u8>()%2;')
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'query-driver-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',files=files,driver_original_sha256=hashlib.sha256(body.encode()).hexdigest(),driver_twin_sha256=hashlib.sha256(twin.encode()).hexdigest(),driver_changes='Fresh cfg(kani) twin: only function name changes. Complete original QueryScan/default/finish and all eight native driver calls retained.',scope='Full constructor/claim control with query observational hook executing exact native driver twin; only bounded complete-state scan replies cut. Sampler/arithmetic/dot normal-return cuts retained and independently scoped. Same actual query result/selected state feed constructor, rho transcript and returned Prepared. NOT whole S1/SDK/runtime closure.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_query_value_cut_replaced_by_exact_native_driver=True,scan_poststate_cuts=1)))
