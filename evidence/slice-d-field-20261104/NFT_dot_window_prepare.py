from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text());n='crates/aspis-core/src/NFT_dot.rs';s=x[n]
arr=', '.join(['any_q()']*7);vals=', '.join(['M31(kani::any())']*7)
s+='''
fn term_window(weights:&[QM31;7],values:&[M31;7],index:usize,raw:[u64;4],log:&mut Log)->[u64;4]{let value=values[index].0 as u64;let weight=weights[index];term_cut(raw,weight,value,log)}
#[kani::proof] KMXL
fn window7(){let weights=[WEIGHTS];let values=[VALUES];for j in 0..7{kani::assume(canonical(weights[j])&&values[j].0<P);}let index:usize=kani::any();let i:usize=kani::any();kani::assume(index<7&&i<4);let raw:[u64;4]=kani::any();for j in 0..4{kani::assume(raw[j]<3u64*(1u64<<62));}let mut log=Log{a:[0;4],b:[0;4],reply:[0;4],count:0};let out=term_window(&weights,&values,index,raw,&mut log);let weight=weights[index];let a=match i{0=>weight.c0.a.0,1=>weight.c0.b.0,2=>weight.c1.a.0,_=>weight.c1.b.0};assert!(weights.len()==values.len()&&weights.len()==7&&weights.len()>4);assert!(log.count==4&&log.a[i]==a as u64&&log.b[i]==values[index].0 as u64);let want=raw[i]+log.reply[i];assert!(out[i]==if cfg!(NFT_invert){want^1}else{want});}
fn selected(q:QM31,i:usize)->u32{match i{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
#[kani::proof] KMXL
fn copy7_positive(){let src=[WEIGHTS];let mut dst=[QM31::ZERO;7];let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<7&&j<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(selected(src[i],j)==selected(dst[i],j));}
#[kani::proof] KMXL
fn copy7_negative(){let src=[WEIGHTS];let mut dst=[QM31::ZERO;7];let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<7&&j<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(selected(src[i],j)!=selected(dst[i],j));}
'''.replace('WEIGHTS',arr).replace('VALUES',vals).replace('KMXL','''#[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]''')
x[n]=s;p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins[n]=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_dot.rs.txt').write_text(s)
