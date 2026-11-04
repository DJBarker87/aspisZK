from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text());C='crates/aspis-core/src/'
code='''use super::*;
use crate::field::{CM31,M31,P};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
#[derive(Clone,Copy)] struct Call{kind:u8,a:QM31,b:QM31,reply:QM31}
struct Log{calls:[Call;4],count:usize}
fn op(log:&mut Log,kind:u8,a:QM31,b:QM31)->QM31{assert!(canonical(a)&&canonical(b)&&log.count<4);let r=any_q();kani::assume(canonical(r));let mut observed=a;if cfg!(NFT_bad_argument)&&log.count==0{observed.c0.a.0^=1;}log.calls[log.count]=Call{kind,a:observed,b,reply:r};log.count+=1;r}
// Frozen wide square with the four product/square/mul_u sites externalized;
// let bindings preserve Rust's source evaluation order.
fn logged(value:WideExact,log:&mut Log)->WideExact{let cross=op(log,0,value.c0,value.c1);let aa=op(log,1,value.c0,QM31::ZERO);let bb=op(log,2,value.c1,QM31::ZERO);let u=op(log,3,bb,QM31::ZERO);WideExact{c0:aa.add(u),c1:cross.add(cross)}}
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn square_log(){let value=WideExact{c0:any_q(),c1:any_q()};kani::assume(canonical(value.c0)&&canonical(value.c1));let mut log=Log{calls:[Call{kind:99,a:QM31::ZERO,b:QM31::ZERO,reply:QM31::ZERO};4],count:0};let got=logged(value,&mut log);assert!(log.count==4);assert!(log.calls[0].kind==0&&log.calls[0].a==value.c0&&log.calls[0].b==value.c1);assert!(log.calls[1].kind==1&&log.calls[1].a==value.c0&&log.calls[1].b==QM31::ZERO);assert!(log.calls[2].kind==2&&log.calls[2].a==value.c1&&log.calls[2].b==QM31::ZERO);assert!(log.calls[3].kind==3&&log.calls[3].a==log.calls[2].reply&&log.calls[3].b==QM31::ZERO);let want=WideExact{c0:log.calls[1].reply.add(log.calls[3].reply),c1:log.calls[0].reply.add(log.calls[0].reply)};assert!((got==want)!=cfg!(NFT_invert));assert!(canonical(got.c0)&&canonical(got.c1));}
'''
n=C+'field/wide_exact.rs';x[n]+='\n#[cfg(kani)]\n#[path="NFT_wide_square.rs"]\nmod NFT_wide_square;\n';x[C+'field/NFT_wide_square.rs']=code;p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_wide_square.rs.txt').write_text(code)
(E/'NFT_WIDE_SQUARE_PENDING.json').write_text(json.dumps(dict(function='crates/aspis-core/src/field/wide_exact.rs::WideExact::square',method='opaque four-site QM product/square/mul_u log; no field multiplication in Kani',sites=['cross=c0.mul(c1)','aa=c0.square','bb=c1.square','u=mul_u(bb)'],status='OPEN irrespective of native verdict until every emitted-value pairing, complete coherent model association and audit pass',retained='P6/D188 option A; no premise retirement'),indent=1)+'\n')
p=E/'NFT_run.py';s=p.read_text().replace("if os.environ.get('NFT_INVERT'):env['RUSTFLAGS']+=' --cfg NFT_invert'", "if os.environ.get('NFT_INVERT'):env['RUSTFLAGS']+=' --cfg NFT_invert'\n if os.environ.get('NFT_BADARG'):env['RUSTFLAGS']+=' --cfg NFT_bad_argument'");p.write_text(s)
p=E/'NFT_native_queue.py';s=p.read_text();i=s.index('jobs=');j=s.index('\nfrozen=',i);jobs=[(98,'field::wide_exact::NFT_wide_square::square_log',False,0),(99,'field::wide_exact::NFT_wide_square::square_log',True,1)];p.write_text(s[:i]+'jobs='+repr(jobs)+s[j:])
