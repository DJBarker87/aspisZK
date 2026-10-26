from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];d=Path(__file__).parent
p=r/'crates/aspis-statement/src/logup.rs';s=p.read_text()
f=s[s.index('pub fn compress_tagged_tuple('):s.index('\n/// Deliberately broken')].strip()
a=f.index('    for value in values {\n')+len('    for value in values {\n');b=f.index('\n    }',a);body=f[a:b]
assert body=='        compressed = compressed.add(power.mul_m31(*value));\n        power = power.mul(lambda);'
text='''// Generated from the frozen source; check with generate.py --check.
use aspis_core::field::{M31,CM31,QM31};
fn lift(value:M31)->QM31 {QM31::from_cm31(CM31::from_m31(value))}
'''+f+'''
pub fn shipped_step(mut compressed:QM31,mut power:QM31,value:&M31,lambda:QM31)->(QM31,QM31) {
'''+body+'''
    (compressed,power)
}
pub fn reference_step(out:QM31,power:QM31,value:M31,lambda:QM31)->(QM31,QM31) {
    (out.add(power.mul_m31(value)),power.mul(lambda))
}
pub fn reference16(tag:M31,values:[M31;16],lambda:QM31)->QM31 {
    let mut state=(lift(tag),lambda);let mut i=0usize;
    while i<16 {state=reference_step(state.0,state.1,values[i],lambda);i+=1;}
    state.0
}
'''
text=text.replace('pub fn shipped_step(', '#[inline(always)]\npub fn shipped_step(')
text+='#[inline(always)]\npub fn owned_step_matched(mut compressed:QM31,mut power:QM31,value:&M31,lambda:QM31)->(QM31,QM31) {\n'+body+'\n    (compressed,power)\n}\n'
fission=f.replace('pub fn compress_tagged_tuple(', 'pub fn compress_fission(').replace(body,'        (compressed,power)=shipped_step(compressed,power,value,lambda);')
text+='\n'+fission+'\n'
p=d/'proof/generated.rs'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
print(json.dumps(dict(source=str(p),shipped_sha256=hashlib.sha256(s.encode()).hexdigest(),function_sha256=hashlib.sha256(f.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest())))
