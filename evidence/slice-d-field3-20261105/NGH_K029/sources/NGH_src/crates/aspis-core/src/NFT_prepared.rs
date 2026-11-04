use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn any_p()->PreparedQm31Multiplier{PreparedQm31Multiplier{components:[[M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any())],[M31(kani::any()),M31(kani::any()),M31(kani::any())]]}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
fn right_prelude(right:&[QM31;3],index:usize)->[[M31;3];3]{        let right_sum = right[index].c0.add(right[index].c1);
        let right_components = [
            [
                right[index].c0.a,
                right[index].c0.b,
                right[index].c0.a.add(right[index].c0.b),
            ],
            [
                right[index].c1.a,
                right[index].c1.b,
                right[index].c1.a.add(right[index].c1.b),
            ],
            [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
        ];
 right_components}
fn add(a:u32,b:u32)->u32{let s=a+b;if s>=P{s-P}else{s}}
fn cache(v:QM31)->[[u32;3];3]{let a=v.c0.a.0;let b=v.c0.b.0;let c=v.c1.a.0;let d=v.c1.b.0;let ac=add(a,c);let bd=add(b,d);[[a,b,add(a,b)],[c,d,add(c,d)],[ac,bd,add(ac,bd)]]}
struct Control{triples:[(usize,usize,usize);27],count:usize}
fn control(log:&mut Control){for index in 0..3{for component in 0..3{for channel in 0..3{log.triples[log.count]=(index,component,channel);log.count+=1;}}}}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn control27(){let mut log=Control{triples:[(99,99,99);27],count:0};control(&mut log);let k:usize=kani::any();kani::assume(k<27);assert!(log.count==27);let want=(k/9,(k/3)%3,k%3);assert!(log.triples[k]==if cfg!(NFT_invert){(want.0,want.1,want.2+1)}else{want});}
struct Log{index:usize,component:usize,channel:usize,a:u64,b:u64,reply:u64,count:usize}
fn product(log:&mut Log,index:usize,component:usize,channel:usize,a:u64,b:u64)->u64{assert!(a<P as u64&&b<P as u64);let r:u64=kani::any();kani::assume(r<1u64<<62);log.index=index;log.component=component;log.channel=channel;log.a=a;log.b=b;log.reply=r;log.count+=1;r}
fn cell_cut(mut sums:[[u64;3];3],left:&[PreparedQm31Multiplier;3],right_components:[[M31;3];3],index:usize,component:usize,channel:usize,log:&mut Log)->[[u64;3];3]{sums[component][channel]+=product(log,index,component,channel,left[index].components[component][channel].0 as u64,right_components[component][channel].0 as u64);sums}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn cell_step(){let left=[any_p(),any_p(),any_p()];let right=[any_q(),any_q(),any_q()];for k in 0..3{kani::assume(canonical(right[k]));for c in 0..3{for j in 0..3{kani::assume(left[k].components[c][j].0<P);}}}let index:usize=kani::any();let component:usize=kani::any();let channel:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(index<3&&component<3&&channel<3&&i<3&&j<3);let sums:[[u64;3];3]=kani::any();for c in 0..3{for j in 0..3{kani::assume(sums[c][j]<3u64*(1u64<<62));}}let rc=right_prelude(&right,index);let mut log=Log{index:99,component:99,channel:99,a:0,b:0,reply:0,count:0};let got=cell_cut(sums,&left,rc,index,component,channel,&mut log);assert!(log.count==1&&log.index==index&&log.component==component&&log.channel==channel);assert!(log.a==left[index].components[component][channel].0 as u64&&log.b==rc[component][channel].0 as u64);let want=if i==component&&j==channel{sums[i][j]+log.reply}else{sums[i][j]};assert!(got[i][j]==if cfg!(NFT_invert){want^1}else{want});}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn prelude(){let right=[any_q(),any_q(),any_q()];for k in 0..3{kani::assume(canonical(right[k]));}let index:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(index<3&&i<3&&j<3);let rc=right_prelude(&right,index);assert!((rc[i][j].0==cache(right[index])[i][j])!=cfg!(NFT_invert));assert!(rc[i][j].0<P);}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy3_positive(){let src=[any_p(),any_p(),any_p()];let mut dst=[any_p(),any_p(),any_p()];let k:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(k<3&&i<3&&j<3);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k].components[i][j].0==dst[k].components[i][j].0);}
#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy3_negative(){let src=[any_p(),any_p(),any_p()];let mut dst=[any_p(),any_p(),any_p()];let k:usize=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(k<3&&i<3&&j<3);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k].components[i][j].0!=dst[k].components[i][j].0);}
