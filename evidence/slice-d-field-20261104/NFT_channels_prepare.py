from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text())
source=subprocess.check_output(['git','show','4bb3b3f:'+C+'field.rs'],cwd=R,text=True)
a=source.index('    let left_sum =',source.index('fn qm31_accumulate_product_channels('));b=source.index('    for component in 0..3 {',a);pre=source[a:b]
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
fn cache_prelude(left:QM31,right:QM31)->([[M31;3];3],[[M31;3];3]){
PRELUDE
(left_components,right_components)
}
// Pure cached-row reference reused from NFQ_core_more_prepare.py (prep_spec).
fn add_word(a:u32,b:u32)->u32{let s=a+b;if s>=P{s-P}else{s}}
fn cache_ref(v:QM31)->[[u32;3];3]{let a=v.c0.a.0;let b=v.c0.b.0;let c=v.c1.a.0;let d=v.c1.b.0;let ac=add_word(a,c);let bd=add_word(b,d);[[a,b,add_word(a,b)],[c,d,add_word(c,d)],[ac,bd,add_word(ac,bd)]]}
#[kani::proof] KMXL
fn prelude(){let left=any_q();let right=any_q();kani::assume(canonical(left)&&canonical(right));let(l,r)=cache_prelude(left,right);let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!((l[i][j].0==cache_ref(left)[i][j]&&r[i][j].0==cache_ref(right)[i][j])!=cfg!(NFT_invert));assert!(l[i][j].0<P&&r[i][j].0<P);}
struct Control{pairs:[(usize,usize);9],count:usize}
fn control(log:&mut Control){for component in 0..3{for channel in 0..3{log.pairs[log.count]=(component,channel);log.count+=1;}}}
#[kani::proof] KMXL
fn channel_control(){let mut log=Control{pairs:[(99,99);9],count:0};control(&mut log);let i:usize=kani::any();kani::assume(i<9);assert!(log.count==9);let expected=(i/3,i%3);assert!(log.pairs[i]==if cfg!(NFT_invert){(expected.0,expected.1+1)}else{expected});}
struct ProductLog{a:u64,b:u64,reply:u64,count:u8}
fn product(log:&mut ProductLog,a:u64,b:u64)->u64{log.a=a;log.b=b;log.count+=1;let r:u64=kani::any();kani::assume(r<1u64<<62);log.reply=r;r}
fn channel_cut(mut sums:[[u64;3];3],left_components:[[M31;3];3],right_components:[[M31;3];3],component:usize,channel:usize,log:&mut ProductLog)->[[u64;3];3]{
 sums[component][channel]+=product(log,left_components[component][channel].0 as u64,right_components[component][channel].0 as u64);sums
}
#[kani::proof] KMXL
fn channel_step(){let mut sums:[[u64;3];3]=kani::any();for row in 0..3{for col in 0..3{kani::assume(sums[row][col]<3u64*(1u64<<62));}}
 let left=any_q();let right=any_q();kani::assume(canonical(left)&&canonical(right));let(l,r)=cache_prelude(left,right);
 let component:usize=kani::any();let channel:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(component<3&&channel<3&&i<3&&j<3);
 let old=sums[i][j];let selected=sums[component][channel];let mut log=ProductLog{a:0,b:0,reply:0,count:0};let got=channel_cut(sums,l,r,component,channel,&mut log);
 assert!(log.count==1&&log.a==l[component][channel].0 as u64&&log.b==r[component][channel].0 as u64);assert!(log.a<P as u64&&log.b<P as u64);
 let want=if i==component&&j==channel{selected+log.reply}else{old};assert!(got[i][j]==if cfg!(NFT_invert){want^1}else{want});
}
#[kani::proof] KMXL
fn cache_copy_positive(){let src:[[u32;3];3]=kani::any();let mut dst:[[u32;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]==dst[i][j]);}
#[kani::proof] KMXL
fn cache_copy_negative(){let src:[[u32;3];3]=kani::any();let mut dst:[[u32;3];3]=kani::any();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]!=dst[i][j]);}
'''.replace('PRELUDE',pre).replace('KMXL','''#[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]''')
x[C+'NFT_channels.rs']=code;x[C+'field.rs']+='\n#[cfg(kani)]\n#[path="NFT_channels.rs"]\nmod NFT_channels;\n';p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_channels.rs.txt').write_text(code)
(E/'NFT_CHANNEL_PRELUDE_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',exact_prefix=pre,sha256=hashlib.sha256(pre.encode()).hexdigest(),reference_provenance='NFQ_core_more_prepare.py prep_spec; NFQ_PreparedMultiplier.source',scope='prefix and one arbitrary-prestate channel only; no whole helper closure yet'),indent=1)+'\n')
