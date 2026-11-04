from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-statement/src/';files={};bases={}
def frozen(n):return subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True)
n=C+'pool_v1/pair_forest_semantic_terminal.rs';s=bases[n]=frozen(n)
for sig,expr in [('fn variant_expected_output(variant: CompiledVariant) -> M31','r.0 == NFQ_stmt::variant_ref(variant)'),('fn copy_variant(variant: CompiledVariant) -> PoolV1PairForestCompiledVariantV1','*r == NFQ_stmt::copy_ref(variant)')]:
 assert s.count(sig)==1;s=s.replace(sig,'#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| ('+expr+') != cfg!(NFQ_invert)))]\n'+sig,1)
s+='\n#[cfg(kani)]\n#[path="NFQ_stmt.rs"]\nmod NFQ_stmt;\n';files[n]=s
files[C+'pool_v1/NFQ_stmt.rs']='''use super::*;
fn any_variant()->CompiledVariant{if kani::any(){CompiledVariant::PrivateTransfer}else{CompiledVariant::Withdrawal}}
pub(super) fn variant_ref(v:CompiledVariant)->u32{match v{CompiledVariant::PrivateTransfer=>1,CompiledVariant::Withdrawal=>0}}
pub(super) fn copy_ref(v:CompiledVariant)->PoolV1PairForestCompiledVariantV1{match v{CompiledVariant::PrivateTransfer=>PoolV1PairForestCompiledVariantV1::PrivateTransfer,CompiledVariant::Withdrawal=>PoolV1PairForestCompiledVariantV1::Withdrawal}}
#[kani::proof_for_contract(variant_expected_output)]
fn variant_contract(){let _=variant_expected_output(any_variant());}
#[kani::proof_for_contract(copy_variant)]
fn copy_contract(){let _=copy_variant(any_variant());}
impl kani::Arbitrary for PoolV1PairForestCompiledVariantV1{fn any()->Self{if kani::any(){Self::PrivateTransfer}else{Self::Withdrawal}}}
#[kani::modifies()] #[kani::ensures(|_r| true)]
fn weak_enum()->PoolV1PairForestCompiledVariantV1{PoolV1PairForestCompiledVariantV1::PrivateTransfer}
#[kani::proof_for_contract(weak_enum)]
fn enum_real(){assert!(matches!(weak_enum(),PoolV1PairForestCompiledVariantV1::PrivateTransfer));}
#[kani::proof] #[kani::stub_verified(weak_enum)]
fn enum_unimplied(){assert!(matches!(weak_enum(),PoolV1PairForestCompiledVariantV1::PrivateTransfer));}
#[kani::modifies(&mut x[0])] #[kani::ensures(|_r| true)]
fn bad_enum_frame(x:&mut[u8;2])->PoolV1PairForestCompiledVariantV1{x[1]=x[1].wrapping_add(1);PoolV1PairForestCompiledVariantV1::PrivateTransfer}
#[kani::proof_for_contract(bad_enum_frame)]
fn enum_frame(){let mut x:[u8;2]=kani::any();let _=bad_enum_frame(&mut x);}
'''
n=C+'state_only_poseidon.rs';s=bases[n]=frozen(n);sig='fn extension_limbs(value: QM31) -> [u32; 4]';assert s.count(sig)==1
s=s.replace(sig,'#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| (*r == NFQ_poseidon::limbs_ref(value)) != cfg!(NFQ_invert)))]\n'+sig,1)+'\n#[cfg(kani)]\n#[path="NFQ_poseidon.rs"]\nmod NFQ_poseidon;\n';files[n]=s
kmx='''#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
'''
code='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn limbs_ref(v:QM31)->[u32;4]{[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]}
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
#[kani::proof_for_contract(extension_limbs)]
KMXL
fn limbs_contract(){let _=extension_limbs(any_q());}
#[kani::proof]
KMXL
fn copy_positive(){let src:[u32;4]=kani::any();let mut dst:[u32;4]=kani::any();let k:usize=kani::any();kani::assume(k<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k]==dst[k]);}
#[kani::proof]
KMXL
fn copy_negative(){let src:[u32;4]=kani::any();let mut dst:[u32;4]=kani::any();let k:usize=kani::any();kani::assume(k<4);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src[k]!=dst[k]);}
#[kani::modifies()] #[kani::ensures(|r| r[0]==0)]
fn weak_array()->[u32;4]{[0,1,2,3]}
#[kani::proof_for_contract(weak_array)]
KMXL
fn array_real(){assert!(weak_array()[1]==1);}
#[kani::proof] #[kani::stub_verified(weak_array)]
KMXL
fn array_unimplied(){assert!(weak_array()[1]==1);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r[0]==0)]
fn bad_array_frame(x:&mut[u8;2])->[u32;4]{x[1]=x[1].wrapping_add(1);[0,1,2,3]}
#[kani::proof_for_contract(bad_array_frame)]
KMXL
fn array_frame(){let mut x:[u8;2]=kani::any();let _=bad_array_frame(&mut x);}
'''.replace('KMXL',kmx);files[C+'NFQ_poseidon.rs']=code
n=C+'lib.rs';bases[n]=frozen(n);files[n]=bases[n].replace('#![no_std]','#![cfg_attr(kani,feature(allocator_api))]\n#![no_std]',1)
inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in files.items():patch+=difflib.unified_diff(bases.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in bases else '/dev/null',tofile='b/'+n)
(E/'NFQ_statement.patch').write_text(''.join(patch))
