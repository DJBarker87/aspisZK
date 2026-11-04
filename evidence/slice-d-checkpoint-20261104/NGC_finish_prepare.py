from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs'
x[n]+='''
fn qword(q:K,j:usize)->u32{match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
// One actual enumerate/iter_mut transition, at an arbitrary cursor/prestate.
fn finish_window(b:&BatchedWeights,weights:&mut[K],index:usize)->usize{
 let mut iter=weights.iter_mut().enumerate();
 let (i,w)=iter.nth(index).unwrap();*w=b.value(i);iter.len()
}
#[kani::proof] KMXL
fn finish_step(){let raw:[[u64;4];64]=kani::any();let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};let mut old:[K;64]=kani::any();let index:usize=kani::any();let observed:usize=kani::any();let limb:usize=kani::any();kani::assume(index<64&&observed<64&&limb<4);let previous=old[observed];let rawword=raw[index][limb];let left=finish_window(&b,&mut old,index);assert!(left==63-index);let expected=if observed==index{M31::reduce_u64(rawword).0}else{qword(previous,limb)};assert!(qword(old[observed],limb)==if cfg!(NGC_invert){expected^1}else{expected});}
#[kani::proof] KMXL
fn finish_canonical(){let raw:[[u64;4];64]=kani::any();let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};let index:usize=kani::any();let limb:usize=kani::any();kani::assume(index<64&&limb<4);let got=b.value(index);assert!((qword(got,limb)<2147483647)!=cfg!(NGC_invert));}
struct FinishControl{count:usize,selected:usize,index:usize,place:*mut K}
fn finish_control(weights:&mut[K],log:&mut FinishControl){for(i,w)in weights.iter_mut().enumerate(){if log.count==log.selected{log.index=i;log.place=w as *mut K;}log.count+=1;}}
#[kani::proof] KMXL
fn finish_order(){let mut weights:[K;64]=kani::any();let selected:usize=kani::any();kani::assume(selected<64);let mut log=FinishControl{count:0,selected,index:99,place:core::ptr::null_mut()};finish_control(&mut weights,&mut log);let exact=log.count==64&&log.index==selected&&log.place==unsafe{weights.as_mut_ptr().add(selected)};assert!(exact!=cfg!(NGC_invert));}
#[kani::proof] KMXL
fn raw_copy_positive(){let raw:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<4);let expected=raw[i][j];let out=Vec::from(raw);assert!(out.len()==64&&out[i][j]==expected);}
#[kani::proof] KMXL
fn raw_copy_negative(){let raw:[[u64;4];64]=kani::any();let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<4);let expected=raw[i][j];let out=Vec::from(raw);assert!(out.len()!=64||out[i][j]!=expected);}
'''.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]''')
(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
