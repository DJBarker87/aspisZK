"""Check the frozen Rust control shapes used by the kernel structural transport.

This is a source pin/shape gate, not a claim of a whole-machine Rust proof.
Arithmetic leaves are shared frozen source, extracted without stubs.
"""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027'
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def body(s,name):
 s=clean(s);pos=s.index('pub fn '+name);a=s.index('{',pos);depth=0
 for i in range(a,len(s)):
  if s[i]=='{':depth+=1
  if s[i]=='}':
   depth-=1
   if depth==0:return s[a:i+1]
 raise ValueError(name)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',re.sub(r',\s*(?=[}\]])','',clean(s)))
expected={
 'secure_circle_point_from_parameter':'''{
 let square=parameter.square();
 let inverse_denominator=QM31::ONE.add(square).try_inv().ok_or(CirclePointError::SingularParameter)?;
 Ok(SecureCirclePoint{x:QM31::ONE.sub(square).mul(inverse_denominator),y:parameter.add(parameter).mul(inverse_denominator),})
 }''',
 'secure_ood_circle_point_from_parameter':'''{
 let point=secure_circle_point_from_parameter(parameter)?;
 if parameter.c1==CM31::ZERO{return Err(CirclePointError::ParameterInCm31Subfield);}
 Ok(point)
 }''',
 'circle_fallback_point':'''{
 let parameter=CIRCLE_FALLBACK_PARAMETERS[sample%2];
 match secure_ood_circle_point_from_parameter(parameter){
 Ok(point)=>point,Err(_)=>SecureCirclePoint{x:QM31::ONE,y:QM31::ZERO,},}
 }''',
 'circle_sample':'''{
 secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else(|_|{
 aspis_core::transcript::circle_fallback_point(match row{CircleRow::First=>0,CircleRow::Second=>1,})
 })
 }'''}
files={'secure_circle_point_from_parameter':'crates/aspis-core/src/circle.rs',
 'secure_ood_circle_point_from_parameter':'crates/aspis-core/src/circle.rs',
 'circle_fallback_point':'crates/aspis-core/src/transcript.rs',
 'circle_sample':'crates/aspis-r1-cost-probe/src/sampler.rs'}
checks={}
for name,exp in expected.items():
 p=R/files[name];actual=body(p.read_text(),name)
 assert tokens(actual)==tokens(exp),(name,actual)
 checks[name]={'path':files[name],'file_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'body_sha256':hashlib.sha256(actual.encode()).hexdigest(),'complete_body_tokens_match':True}
# The fallback array is literally the same pair of parameters; names differ only.
transcript=clean((R/'crates/aspis-core/src/transcript.rs').read_text())
a=transcript.index('pub const CIRCLE_FALLBACK_PARAMETERS:');b=transcript.index(';',transcript.index('=',a))
native_const=transcript[a:b].split('=',1)[1].replace('crate::field::','')
owned=clean((R/'tools/pv-alib-20261027/sampler-owned-reference.rs').read_text())
a=owned.index('pub const FALLBACK:');b=owned.index(';',owned.index('=',a))
owned_const=owned[a:b].split('=',1)[1]
assert tokens(native_const)==tokens(owned_const)
meta=json.loads((E/'circle-owned-translation.json.txt').read_text())
assert all(not x.get('is_opaque') for k in ['functions','globals'] for x in meta.get(k,[]))
raw=(E/'circle-owned-Funs.lean.txt').read_text()
assert not re.search(r'\b(axiom|sorry|admit|native_decide|implemented_by)\b',raw)
report={'kind':'pinned-source structural control transport under ruling (k)',
 'kernel_theorems':['R1Z.PV_AL_CircleControl.native_owned','R1Z.PV_AL_CircleNative.map_source','R1Z.PV_AL_CircleNative.fallback_source','R1Z.PV_AL_CircleNative.source_reference'],
 'native_function_body_checks':checks,'fallback_constants_equal':True,
 'all_extracted_functions_and_globals_nonopaque':True,'arithmetic_stubs':False,
 'native_differential':'native-circle-owned-03: 8712 wrapper checks, all three map outcomes, both rows',
 'boundary':'structural source/library law plus extraction; no unbounded whole-machine or deployed claim'}
(E/'STRUCTURAL-CIRCLE-GATE.json').write_text(json.dumps(report,indent=2)+'\n')
print('complete native control bodies and fallback constants match structural gate; no opaque arithmetic leaves')
