from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;T=E.parent/'slice-d-field-20261104'
x=json.loads((T/'NFT_NATIVE_INPUTS.json').read_text())
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/field.rs'],text=True)
start=frozen.index('        sums = qm31_accumulate_product_channels(sums, left[index], right[index]);',frozen.index('fn qm31_sum_products_small<'))
end=frozen.index('\n    }',start)
body=frozen[start:end]
assert body.strip()=='sums = qm31_accumulate_product_channels(sums, left[index], right[index]);\n        index += 1;'
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(x:QM31)->bool{x.c0.a.0<P&&x.c0.b.0<P&&x.c1.a.0<P&&x.c1.b.0<P}
struct Log{before:[[u64;3];3],left:QM31,right:QM31,reply:[[u64;3];3],count:usize}
fn cut(log:&mut Log,sums:[[u64;3];3],left:QM31,right:QM31)->[[u64;3];3]{
 assert!(canonical(left)&&canonical(right));
 log.before=sums;log.left=left;log.right=right;log.count+=1;
 let reply:[[u64;3];3]=kani::any();log.reply=reply;reply
}
fn step<const N:usize>(mut sums:[[u64;3];3],left:[QM31;N],right:[QM31;N],mut index:usize,log:&mut Log)->([[u64;3];3],usize){
BODY
(sums,index)
}
fn check<const N:usize>(left:[QM31;N],right:[QM31;N]){
 let sums:[[u64;3];3]=kani::any();let index:usize=kani::any();kani::assume(index<N);
 kani::assume(canonical(left[index])&&canonical(right[index]));
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);
 let old=sums[i][j];let expected_left=left[index];let expected_right=right[index];
 let mut log=Log{before:kani::any(),left:any_q(),right:any_q(),reply:kani::any(),count:0};
 let(out,next)=step(sums,left,right,index,&mut log);
 assert!(log.count==1&&next==index+1);
 assert!(log.before[i][j]==old&&log.left==expected_left&&log.right==expected_right);
 let want=log.reply[i][j];assert!(out[i][j]==if cfg!(NGA_invert){want^1}else{want});
}
'''.replace('BODY',body.replace('qm31_accumulate_product_channels(sums,','cut(log,sums,'))
kmx='''#[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]'''
for n in [2,3,4]:
 arr=','.join(['any_q()']*n)
 code+=f'\n#[kani::proof] {kmx}\nfn outer{n}(){{check([{arr}],[{arr}]);}}\n'
for which,op in [('positive','=='),('negative','!=')]:
 code+=f'''\n#[kani::proof] {kmx}
fn copy_{which}(){{let src:[[u64;3];3]=kani::any();let mut dst:[[u64;3];3]=kani::any();unsafe{{core::ptr::copy_nonoverlapping(&src,&mut dst,1)}};let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<3&&j<3);assert!(src[i][j]{op}dst[i][j]);}}
'''
x['crates/aspis-core/src/field.rs']+='\n#[cfg(kani)]\n#[path="NGA_outer.rs"]\nmod NGA_outer;\n'
x['crates/aspis-core/src/NGA_outer.rs']=code
(E/'NGA_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NGA_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=1)+'\n')
(E/'NGA_outer.rs.txt').write_text(code)
(E/'NGA_OUTER_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),rewrite='replace only qm31_accumulate_product_channels by local-record cut; retain actual sums,left[index],right[index], index+=1',scope='New arbitrary-prestate outer data iteration, distinct from NFT data-independent control chronology. One selected complete U64 cell and exact four-limb arguments; arbitrary full helper reply.',closure_credit=False),indent=1)+'\n')
(E/'NGA_gate.py').write_text((T/'NFT_gate.py').read_text().replace('NFT','NGA'))
print('Prepared new outer data-iteration shape; no field arithmetic in Kani')
