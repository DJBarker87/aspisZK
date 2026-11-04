from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;p=E/'NFT_NATIVE_INPUTS.json';x=json.loads(p.read_text());C='crates/aspis-core/src/'
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
struct Log<const N:usize>{left:[QM31;N],right:[QM31;N],reply:QM31,count:u8}
fn child<const N:usize>(log:&mut Log<N>,left:[QM31;N],right:[QM31;N])->QM31{assert!(N>=2&&N<=4);for i in 0..N{assert!(canonical(left[i])&&canonical(right[i]));}log.left=left;log.right=right;log.count+=1;let r=any_q();kani::assume(canonical(r));log.reply=r;r}
fn wrapper<const N:usize>(left:[QM31;N],right:[QM31;N],log:&mut Log<N>)->QM31{child(log,left,right)}
fn check<const N:usize>(left:[QM31;N],right:[QM31;N]){for i in 0..N{kani::assume(canonical(left[i])&&canonical(right[i]));}let mut log=Log{left:[QM31::ZERO;N],right:[QM31::ZERO;N],reply:QM31::ZERO,count:0};let got=wrapper(left,right,&mut log);let i:usize=kani::any();kani::assume(i<N);assert!(log.count==1&&log.left[i]==left[i]&&log.right[i]==right[i]);assert!((got==log.reply)!=cfg!(NFT_invert));}
struct Sequence{index:[usize;4],count:usize}
fn control<const N:usize>(log:&mut Sequence){let mut index=0usize;while index<N{log.index[log.count]=index;log.count+=1;index+=1;}}
fn check_control<const N:usize>(){let mut log=Sequence{index:[99;4],count:0};control::<N>(&mut log);assert!(log.count==N);let i:usize=kani::any();kani::assume(i<N);assert!(log.index[i]==if cfg!(NFT_invert){i+1}else{i});}
'''
kmx='''#[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]'''
for n in [2,3,4]:
 arr=', '.join(['any_q()']*n)
 code+='\n#[kani::proof] '+kmx+f'\nfn wrapper{n}(){{check([{arr}],[{arr}]);}}\n'
 code+='\n#[kani::proof] '+kmx+f'\nfn control{n}(){{check_control::<{n}>();}}\n'
x[C+'NFT_small.rs']=code;x[C+'field.rs']+='\n#[cfg(kani)]\n#[path="NFT_small.rs"]\nmod NFT_small;\n';p.write_text(json.dumps(x,indent=1)+'\n');p=E/'NFT_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});p.write_text(json.dumps(pins,indent=1)+'\n');(E/'NFT_small.rs.txt').write_text(code)
source=subprocess.check_output(['git','show','4bb3b3f:'+C+'field.rs'],text=True)
for arity in [2,3,4]:assert f'pub fn qm31_sum_products{arity}(left: [QM31; {arity}], right: [QM31; {arity}]) -> QM31 {{\n    qm31_sum_products_small(left, right)\n}}'in source
(E/'NFT_SMALL_ERASURE.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',wrapper_erasure_equal=True,arity=[2,3,4],control='exact while index<N; body replaced by recording call only',callee='qm31_sum_products_small',callee_status='OPEN; wrappers earn no composed credit until child and coherent model association close'),indent=1)+'\n')
