"""Scratch-only, cfg(kani) contract annotations; frozen bodies retained verbatim."""
from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
get=lambda n:subprocess.check_output(['git','show',F+':'+n]).decode()
field='crates/aspis-core/src/field.rs';s=get(field)
annotations=[
('pub fn reduce_u64(value: u64) -> M31 {','true','NDD_field::verdict_reduce64(r.0 == NDD_field::reference::reduce_u62_ref(value))'),
('pub fn qm31_pack_base4(values: &[QM31]) -> QM31 {','values.len() <= 4 && values.iter().all(|v| NDD_field::canonical(*v))','NDD_field::pack_pred(NDD_field::limbs(*r), NDD_field::reference::pack_ref([NDD_field::padded(values,0),NDD_field::padded(values,1),NDD_field::padded(values,2),NDD_field::padded(values,3)]))'),
('fn qm31_from_karatsuba_channel_sums(sums: [[u64; 3]; 3]) -> QM31 {','true','NDD_field::verdict_channels(NDD_field::limbs(*r) == NDD_field::reference::channels_ref(sums))'),
('pub fn reduce_u62(value: u64) -> M31 {','value < (1u64<<62)','NDD_field::verdict(r.0 == NDD_field::reference::reduce_u62_ref(value))'),
('pub fn new(value: QM31) -> Self {','NDD_field::canonical(value)','NDD_field::verdict(NDD_field::prepared_limbs(*r) == NDD_field::reference::prepared_ref(NDD_field::limbs(value)))'),
('pub fn from_m31(a: M31) -> CM31 {','true','NDD_field::verdict([r.a.0,r.b.0] == NDD_field::reference::cm31_from_ref(a.0))'),
('pub fn neg(self) -> M31 {','self.0 < P','NDD_field::verdict(r.0 == NDD_field::reference::m31_neg_ref(self.0))'),
('pub fn neg(self) -> CM31 {','self.a.0 < P && self.b.0 < P','NDD_field::verdict([r.a.0,r.b.0] == NDD_field::reference::cm31_neg_ref([self.a.0,self.b.0]))'),
('pub fn neg(self) -> QM31 {','NDD_field::canonical(self)','NDD_field::verdict(NDD_field::limbs(*r) == NDD_field::reference::qm31_neg_ref(NDD_field::limbs(self)))'),
('pub fn is_zero(self) -> bool {',None,None),
]
for sig,req,post in annotations:
 if req is None:continue
 assert s.count(sig)==1,(sig,s.count(sig))
 if '::cm31_neg_ref' in post:post=post.replace('NDD_field::verdict(', 'NDD_field::verdict_cneg(')
 if '::qm31_neg_ref' in post:post=post.replace('NDD_field::verdict(', 'NDD_field::verdict_qneg(')
 attrs=f'#[cfg_attr(kani, kani::requires({req}))]\n    #[cfg_attr(kani, kani::ensures(|r| {post}))]\n    '
 s=s.replace(sig,attrs+sig)
# Only the QM31 zero predicate, not the same-spelled M31/CM31 predicates.
pos=s.index('impl QM31 {');a=s[:pos];b=s[pos:]
sig='pub fn is_zero(self) -> bool {'
assert b.count(sig)==1
b=b.replace(sig,'#[cfg_attr(kani, kani::ensures(|r| NDD_field::verdict(*r == NDD_field::reference::qm31_zero_ref(NDD_field::limbs(self)))))]\n    '+sig)
s=a+b+'\n#[cfg(kani)]\nmod NDD_field;\n'
h='''use super::*;
impl kani::Arbitrary for M31{fn any()->Self{M31(kani::any())}}
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="NDD_reference.rs"] pub(super) mod reference;
pub(super) fn verdict(v:bool)->bool {if cfg!(NDD_negative){!v}else{v}}
pub(super) fn pack_pred(x:[u32;4],y:[u32;4])->bool{let equal=if cfg!(NDD_pack0){x[0]==y[0]}else if cfg!(NDD_pack1){x[1]==y[1]}else if cfg!(NDD_pack2){x[2]==y[2]}else if cfg!(NDD_pack3){x[3]==y[3]}else{x==y};verdict_pack(equal)}
pub(super) fn verdict_reduce64(v:bool)->bool{if cfg!(NDD_negative_reduce64){!v}else{v}}
pub(super) fn verdict_pack(v:bool)->bool{if cfg!(NDD_negative_pack){!v}else{v}}
pub(super) fn padded(x:&[QM31],k:usize)->[u32;4]{if k<x.len(){limbs(x[k])}else{[0;4]}}
pub(super) fn verdict_channels(v:bool)->bool{if cfg!(NDD_negative_channels){!v}else{v}}
pub(super) fn verdict_cneg(v:bool)->bool{if cfg!(NDD_negative_cneg){!v}else{v}}
pub(super) fn verdict_qneg(v:bool)->bool{if cfg!(NDD_negative_qneg){!v}else{v}}
pub(super) fn limbs(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
pub(super) fn qm(x:[u32;4])->QM31{QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
pub(super) fn canonical(x:QM31)->bool{let x=limbs(x);x[0]<P && x[1]<P && x[2]<P && x[3]<P}
pub(super) fn prepared_limbs(x:PreparedQm31Multiplier)->[[u32;3];3]{let a=x.components;[[a[0][0].0,a[0][1].0,a[0][2].0],[a[1][0].0,a[1][1].0,a[1][2].0],[a[2][0].0,a[2][1].0,a[2][2].0]]}
#[kani::proof_for_contract(qm31_from_karatsuba_channel_sums)] fn channels_contract(){qm31_from_karatsuba_channel_sums(kani::any());}
#[kani::proof_for_contract(qm31_pack_base4)]
#[kani::stub_verified(M31::reduce_u64)]
#[kani::stub(<[QM31]>::copy_from_slice,KMX_copy_from_slice)] #[kani::unwind(7)]
fn pack_contract(){let x:[QM31;4]=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];let n:usize=kani::any();kani::assume(n<=4);qm31_pack_base4(&x[..n]);}
#[kani::proof_for_contract(M31::reduce_u64)] fn reduce64_contract(){M31::reduce_u64(kani::any());}
#[kani::proof_for_contract(M31::reduce_u62)] fn reduce_contract(){M31::reduce_u62(kani::any());}
#[kani::proof_for_contract(PreparedQm31Multiplier::new)] fn prepared_contract(){PreparedQm31Multiplier::new(qm(kani::any()));}
#[kani::proof_for_contract(CM31::from_m31)] fn from_contract(){CM31::from_m31(M31(kani::any()));}
#[kani::proof_for_contract(M31::neg)] fn mneg_contract(){M31(kani::any()).neg();}
#[kani::proof_for_contract(CM31::neg)] fn cneg_contract(){CM31{a:M31(kani::any()),b:M31(kani::any())}.neg();}
#[kani::proof_for_contract(QM31::neg)] fn qneg_contract(){qm(kani::any()).neg();}
#[kani::proof_for_contract(QM31::is_zero)] fn zero_contract(){qm(kani::any()).is_zero();}
'''
h=h.replace('#[kani::proof_for_contract(', '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::proof_for_contract(')
widepath='crates/aspis-core/src/field/wide_exact.rs'
wide=get(widepath).replace('pub fn neg(self) -> Self {', '#[cfg_attr(kani,kani::requires(super::NDD_field::wide_canonical(self)))]\n    #[cfg_attr(kani,kani::ensures(|r|super::NDD_field::verdict_wide(super::NDD_field::wide_limbs(*r)==super::NDD_field::reference::wide_neg_ref(super::NDD_field::wide_limbs(self)))))]\n    pub fn neg(self) -> Self {')
h += '\n#[kani::proof] #[kani::unwind(3)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] fn pack_copy_window(){let src:[QM31;4]=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];let mut dst:[QM31;4]=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];let before=dst;let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<4&&j<4);unsafe{core::ptr::copy_nonoverlapping(src.as_ptr().add(i),dst.as_mut_ptr().add(i),1)};if cfg!(NDD_negative_copy){assert_ne!(dst[i],src[i]);}else{assert_eq!(dst[i],src[i]);if i!=j{assert_eq!(dst[j],before[j]);}}}\npub(super) fn wide_limbs(x:WideExact)->[u32;8]{let a=limbs(x.c0());let b=limbs(x.c1());[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]]}\npub(super) fn wide_canonical(x:WideExact)->bool{canonical(x.c0())&&canonical(x.c1())}\npub(super) fn verdict_wide(v:bool)->bool{if cfg!(NDD_negative_wide){!v}else{v}}\n#[kani::proof_for_contract(WideExact::neg)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] fn wide_contract(){let a=qm(kani::any());let b=qm(kani::any());kani::assume(canonical(a)&&canonical(b));WideExact::new(a,b).neg();}\n'
h += (E/'NDD_PackRaw.rs').read_text()
corelib='crates/aspis-core/src/lib.rs'
files={widepath:wide,corelib:'#![cfg_attr(kani, feature(allocator_api))]\n'+get(corelib),field:s,'crates/aspis-core/src/field/NDD_field.rs':h,'crates/aspis-core/src/field/NDD_reference.rs':(E/'NDD_reference.rs').read_text()}
patch=''
for n,v in files.items():patch+=''.join(difflib.unified_diff(get(n).splitlines(True) if n in [field,corelib,widepath] else [],v.splitlines(True),fromfile='a/'+n if n in [field,corelib,widepath] else '/dev/null',tofile='b/'+n))
(E/'NDD_SCRATCH.patch').write_text(patch)
(E/('NDD_INSTRUMENT_'+hashlib.sha256(patch.encode()).hexdigest()+'.patch')).write_text(patch)
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028');s=b/'NDD_src'
for n,v in json.loads(PAYLOAD).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_text(v)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NDD_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
'''.replace('PAYLOAD',repr(json.dumps(files)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
print('installed scratch annotations; patch',hashlib.sha256(patch.encode()).hexdigest())
