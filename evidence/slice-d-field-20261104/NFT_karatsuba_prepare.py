from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text())
src=subprocess.check_output(['git','show','4bb3b3f:'+C+'field.rs'],cwd=R,text=True);a=src.index('fn qm31_from_karatsuba_channel_sums(');start=src.index('{',a);end=start+1;depth=1
while depth:depth+=(src[end]=='{')-(src[end]=='}');end+=1
body=src[start+1:end-1];instrumented=body.replace('mul_by_r(m1)','mul_r(log,m1)');assert instrumented!=body
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{a:CM31,reply:CM31,count:u8}
fn mul_r(log:&mut Log,value:CM31)->CM31{assert!(value.a.0<P&&value.b.0<P);log.a=value;log.count+=1;let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P&&b<P);let reply=CM31{a:M31(a),b:M31(b)};log.reply=reply;reply}
fn reconstructed(c:[u64;3])->CM31{let a=M31::reduce_u64(c[0]);let b=M31::reduce_u64(c[1]);let t=M31::reduce_u64(c[2]);CM31{a:a.sub(b),b:t.sub(a).sub(b)}}
fn from_logged(sums:[[u64;3];3],log:&mut Log)->QM31{BODY}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn reconstruct_log(){let sums:[[u64;3];3]=kani::any();let mut log=Log{a:CM31::ZERO,reply:CM31::ZERO,count:0};let got=from_logged(sums,&mut log);let m0=reconstructed(sums[0]);let m1=reconstructed(sums[1]);let m2=reconstructed(sums[2]);assert!(log.count==1&&log.a==m1);let want=QM31{c0:m0.add(log.reply),c1:m2.sub(m0).sub(m1)};assert!((got==want)!=cfg!(NFT_invert));assert!(got.c0.a.0<P&&got.c0.b.0<P&&got.c1.a.0<P&&got.c1.b.0<P);}
'''.replace('BODY',instrumented)
x[C+'NFT_karatsuba.rs']=code;x[C+'field.rs']+='\n#[cfg(kani)]\n#[path="NFT_karatsuba.rs"]\nmod NFT_karatsuba;\n';p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_karatsuba.rs.txt').write_text(code)
(E/'NFT_KARATSUBA_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),instrumented_body=instrumented,erasure_equal=instrumented.replace('mul_r(log,m1)','mul_by_r(m1)')==body,stub='mul_by_r -> local log with unconstrained canonical CM31 reply',retained_real_callees=['reduce_u64','M31::sub','CM31::add','CM31::sub'],status='OPEN until paired Lean value/source association and raw audit'),indent=1)+'\n')
