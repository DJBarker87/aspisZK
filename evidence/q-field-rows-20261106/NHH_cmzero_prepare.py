from pathlib import Path
import json,subprocess,re,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NHH_ARG_CM_INPUTS.json').read_text());src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/field.rs'],text=True)
m=re.search(r'pub fn inv_with\(',src);a=src.index('{',m.end());i=a+1;d=1
while d:d+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[a+1:i-1];inst=body.replace('self','input').replace('inverse(norm)','M31::inv(norm)');assert inst.replace('M31::inv(norm)','inverse(norm)').replace('input','self')==body
extra='''
fn NHH_zero_product(a:M31,b:M31)->M31{assert!(a==M31(0)&&b==M31(0));let out=M31(kani::any());kani::assume(out==M31(0));out}
fn NHH_fixed_zero(input:CM31)->CM31{
'''+inst+'''
}
#[kani::proof]
#[kani::should_panic]
#[kani::stub(M31::mul,NHH_zero_product)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn cm_zero_panic(){if !cfg!(NHH_invert){let _=NHH_fixed_zero(CM31::ZERO);}}
#[kani::proof]
#[kani::stub(M31::mul,NHH_zero_product)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(80)]
fn cm_zero_prefix(){let input=CM31::ZERO;let norm=input.a.mul(input.a).add(input.b.mul(input.b));check(norm==M31(0));}
'''
x['crates/aspis-r1-cost-probe/src/NHH_fields.rs']+=extra;(E/'NHH_CM_ZERO_INPUTS.json').write_text(json.dumps(x));(E/'NHH_CM_ZERO_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n')
(E/'NHH_CM_ZERO_ERASURE.json').write_text(json.dumps(dict(function='CM31::inv_with fixed M31::inv specialization at zero',erasure_equal=True,source_body_sha256=hashlib.sha256(body.encode()).hexdigest(),specialized_body_sha256=hashlib.sha256(inst.encode()).hexdigest(),product_stub='NHH_zero_product',paired_law='NHH_InverseOutcomes.zero_product',domain='both M31 operands are exactly0, asserted in stub and proved by cm_zero_prefix; original canonical zero receiver',generic_pointer_credit=False),indent=1)+'\n')
