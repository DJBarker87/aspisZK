from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;P=E.parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';core='crates/aspis-core/src/'
frozen=lambda n:subprocess.check_output(['git','show',F+':'+n],text=True)
src=frozen(core+'state_only_prefix.rs')
code=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn q(w:[u32;4])->QM31{QM31{c0:crate::field::CM31{a:crate::field::M31(w[0]),b:crate::field::M31(w[1])},c1:crate::field::CM31{a:crate::field::M31(w[2]),b:crate::field::M31(w[3])}}}
fn anyq()->QM31{let w:[u32;4]=kani::any();for a in w{kani::assume(a<2147483647);}q(w)}
fn add(x:u32,y:u32)->u32{let s=x+y;if s>=2147483647{s-2147483647}else{s}}
fn sub(x:u32,y:u32)->u32{if x>=y{x-y}else{x+2147483647-y}}
struct Log{reply:QM31,left:[u32;4],right:[u32;4],calls:usize}
fn product(bit:QM31,carry:QM31,log:&mut Log)->QM31{log.left=words(bit);log.right=words(carry);log.calls+=1;log.reply}
fn step(z:&[QM31;10],successor:&mut[QM31;10],carry:&mut QM31,coordinate:usize,log:&mut Log){
 let bit = z[coordinate];
 let bit_and_carry = product(bit,*carry,log);
 successor[coordinate] = bit.add(*carry).sub(bit_and_carry.add(bit_and_carry));
 *carry = bit_and_carry;
}
fn exercise(g:u8){let z=core::array::from_fn(|_|anyq());let mut s=core::array::from_fn(|_|anyq());let before=s;let mut carry=anyq();let old=carry;let p=anyq();let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<10);let mut log=Log{reply:p,left:[0;4],right:[0;4],calls:0};
 step(&z,&mut s,&mut carry,i,&mut log);
 let expected=sub(add(words(z[i])[j],words(old)[j]),add(words(p)[j],words(p)[j]));
 if cfg!(NGW_invert){match g{0=>{let mut w=words(s[i]);w[j]^=1;s[i]=q(w)},1=>log.left[j]^=1,2=>{let mut w=words(carry);w[j]^=1;carry=q(w)},3=>{let mut w=words(s[k]);w[j]^=1;s[k]=q(w)},_=>log.calls+=1}}
 assert!(match g{0=>words(s[i])[j]==expected,1=>log.left==words(z[i])&&log.right==words(old),2=>words(carry)==words(p),3=>words(s[k])[j]==if k==i{expected}else{words(before[k])[j]},_=>log.calls==1});
}
fn absorb(g:u8){let mut a=core::array::from_fn::<_,10,_>(|_|anyq());let old=a;let j:usize=kani::any();kani::assume(j<4);let k:usize=kani::any();kani::assume(k<10);
 a[7]=QM31::ONE.sub(a[7]);a[6]=QM31::ONE.sub(a[6]);
 if cfg!(NGW_invert){let mut w=words(a[k]);w[j]^=1;a[k]=q(w);}
 let one=if j==0{1}else{0};let expected=if k==7||k==6{sub(one,words(old[k])[j])}else{words(old[k])[j]};assert!(words(a[k])[j]==expected);let _=g;
}
fn control(){let z=[QM31::ZERO;10];let mut n=0;let mut trace=[0usize;10];for coordinate in (0..z.len()).rev(){trace[n]=coordinate;n+=1;}let j:usize=kani::any();kani::assume(j<10);if cfg!(NGW_invert){trace[j]^=1;}assert!(n==10&&trace[j]==9-j);}
fn copy_control(){let a:[u8;160]=kani::any();let mut b:[u8;160]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<160);if cfg!(NGW_invert){b[i]^=1;}assert!(a[i]==b[i]);}
macro_rules! gate{($n:ident,$f:ident,$g:expr)=>{#[kani::proof]#[kani::unwind(161)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $n(){$f($g)}};}
'''
for i in range(5):code+=f'gate!(step_g{i},exercise,{i});\n'
code+='gate!(absorption,absorb,0);\n'
for n in ['control','copy_control']:code+=f'#[kani::proof]#[kani::unwind(161)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn {n}_gate(){{{n}()}}\n'
inputs={core+'lib.rs':'#![cfg_attr(kani,feature(allocator_api))]\n'+frozen(core+'lib.rs'),core+'state_only_prefix.rs':src+'\n#[cfg(kani)] #[path="NGW_points.rs"] mod NGW_points;\n',core+'NGW_points.rs':code}
(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
original=json.loads((P/'slice-d-finish-20261105/NGM_FROZEN_SOURCE_PINS.json').read_text());pins=dict(original)
pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in inputs.items()})
(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in inputs.items():patch+=difflib.unified_diff((frozen(n) if n in original else '').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in original else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
# Reset all predecessor modifications while preserving a single scratch source copy.
old=json.loads((P/'slice-d-finish-20261105/NGM_NATIVE_INPUTS.json').read_text())
reset={n:frozen(n) for n in old if n in original};reset.update(inputs)
(E/'NGW_SETUP_INPUTS.json').write_text(json.dumps(reset))
(E/'NGW_NATIVE_PROVENANCE.json').write_text(json.dumps(dict(frozen=F,kmx_patch_sha256=hashlib.sha256((P/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest(),method='source-ordered single iteration fission; multiplication opaque local record; arbitrary canonical QM31 prestate; arithmetic and array frame split; no full fold',feature_parity='aspis-core r0 leaf helper; frozen function body has no cfg-dependent branches; deployed parent still required',status='OPEN pending native gates and complete Lean association'),indent=2)+'\n')
