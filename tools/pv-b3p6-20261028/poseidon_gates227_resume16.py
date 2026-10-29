"""Append adapters to exact Poseidon modules; no arithmetic/source edits."""
from pathlib import Path
import json,hashlib,sys
P=Path('tools/pv-b3p6-20261028/v244');D=Path('evidence/pv-b3p6-20261028/resume16')
wrap='''pub(crate) mod access16 {use super::*;
pub fn external(mut s:[QM31;16])->[QM31;16] {external_linear_lazy(&mut s);s}
pub fn internal(mut s:[QM31;16])->[QM31;16] {internal_linear_lazy(&mut s);s}
pub fn packed(s:[QM31;16])->[QM31;4] {external_linear_packed(s)}
pub fn raw(s:[QM31;4])->[u64;4] {external_local_packed_raw(s)}
pub fn round(s:[QM31;16],c:[QM31;16])->[QM31;16] {full_round(s,c)}
pub fn round_m31(s:[QM31;16],c:[u32;16])->[QM31;16] {full_round_m31_constants(s,c)}
pub fn round_packed(s:[QM31;16],c:[QM31;16])->[QM31;4] {full_round_packed(s,c)}
pub fn round_m31_packed(s:[QM31;16],c:[u32;16])->[QM31;4] {full_round_m31_constants_packed(s,c)}
pub fn interpolate(w:[QM31;3],a:[u32;16],b:[u32;16],c:[u32;16])->[QM31;16] {interpolate_three_constant_columns(w,a,b,c)}
pub fn pair(s:[QM31;16],l:&[QM31;16])->[QM31;16] {interpolated_internal_pair(s,l)}
fn opening(z:[QM31;16],s:[QM31;16],x:[QM31;16])->StateOnlyPoseidonOpenings {StateOnlyPoseidonOpenings{z,succ_z:s,xor12_z:x}}
pub fn leading(z:[QM31;16],s:[QM31;16],x:[QM31;16])->[QM31;4] {leading_pair_packed(&opening(z,s,x))}
pub fn projected(z:[QM31;16],s:[QM31;16],x:[QM31;16],block:QM31,local:[QM31;16])->[QM31;4] {evaluate_state_only_poseidon_oracle_projected(&opening(z,s,x),&StateOnlyPoseidonSelectors{block,local})}
}'''
records=json.loads((D/'verbatim-prefixes.json').read_text());records=[r for r in records if 'poseidon_kani16'not in r['path']]
for side,src in [('deployed',Path('crates/aspis-statement/src/state_only_poseidon.rs')),('reference',P/'reference_poseidon.rs')]:
 raw=src.read_bytes();w=wrap
 if side=='deployed':w=w.rsplit('}',1)[0]+'''pub fn at_point(p:&[QM31;10])->(QM31,[QM31;16]) {let s=StateOnlyPoseidonSelectors::at_point(p);(s.block,s.local)}
pub fn expand_high(p:&[QM31;10])->[QM31;64] {StateOnlyPoseidonSelectors::expand(&p[..6])}
pub fn expand_low(p:&[QM31;10])->[QM31;16] {StateOnlyPoseidonSelectors::expand(&p[6..])}
}'''
 out=raw+b'\n'+w.encode()+b'\n';dest=P/f'{side}_poseidon_kani16.rs'
 if '--check'in sys.argv:assert dest.read_bytes()==out
 else:dest.write_bytes(out)
 records.append(dict(path=str(dest),prefix_source=str(src),prefix_bytes=len(raw),prefix_sha256=hashlib.sha256(raw).hexdigest(),module_sha256=hashlib.sha256(out).hexdigest(),identity='exact byte prefix; appended adapters'))
if '--check'in sys.argv:assert json.loads((D/'verbatim-prefixes.json').read_text())==records
else:(D/'verbatim-prefixes.json').write_text(json.dumps(records,indent=2)+'\n')
