#!/usr/bin/env python3
"""Copy owned pole/compression bodies; instrument actual expression/loop sites.
The strict body whitelist is the public-shape/noninterference source check.
Field leaves are covered by the retained stage-2 symbolic gates, not expanded
into a large nonlinear proof here. No claim about compiler/CPU timing.
"""
from pathlib import Path
import re, hashlib, json, subprocess
R=Path(__file__).resolve().parents[2];T=R/'tools/ct-kernels-20261022'
def function(s,name):
 start=s.index('fn '+name+'('); start=s.rfind('\n',0,start)+1
 end=s.index('{',start); depth=1;i=end+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
s=(R/'crates/aspis-r1-cost-probe/src/ct_pole.rs').read_text()
# Fail closed on edits that might introduce secret control/index dependencies.
expected='''use aspis_core::field::QM31;
#[inline(always)]
pub(crate) fn equal(a: QM31, b: QM31) -> bool {
let different = (a.c0.a.0 ^ b.c0.a.0)
| (a.c0.b.0 ^ b.c0.b.0)
| (a.c1.a.0 ^ b.c1.a.0)
| (a.c1.b.0 ^ b.c1.b.0);
different == 0
}
#[inline(always)]
pub(crate) fn keep_clear(clear: bool, active: bool, chi: QM31, value: QM31) -> bool {
clear & !(active & equal(chi, value))
}
pub(crate) fn all_slots_clear(values: &[[[QM31; 2]; 2]], masks: &[u16; 64], chi: QM31) -> bool {
let mut clear = true;
for (row, sides) in values.iter().enumerate() {
let active = masks[row >> 4] & (1 << (row & 15)) != 0;
for side in sides {
for value in side {
clear = keep_clear(clear, active, chi, *value);
}
}
}
clear
}'''
clean=lambda v:'\n'.join(x.strip() for x in v.splitlines() if x.strip() and not x.strip().startswith('//'))
assert clean(s)==expected
out=s.replace('use aspis_core::field::QM31;', 'use aspis_core::field::QM31;\nuse super::pole_proofs::event;')
out=out.replace('    let different =', '    event(1);\n    let different =').replace('    different == 0','    event(2);\n    different == 0')
out=out.replace('    clear & !','    event(3);\n    clear & !')
out=out.replace('    let mut clear = true;', '    event(4);\n    let mut clear = true;')
out=out.replace('        let active =','        event(100 + row as u32);\n        let active =')
out=out.replace('        for side in sides {','        for (side_index, side) in sides.iter().enumerate() {\n            event(2000 + side_index as u32);')
out=out.replace('            for value in side {','            for (slot_index, value) in side.iter().enumerate() {\n                event(3000 + slot_index as u32);')
(T/'pole-instrumented.rs').write_text(out)
logup=(R/'crates/aspis-statement/src/logup.rs').read_text()
compression=function(logup,'compress_tagged_tuple');lift=function(logup,'lift')
base=subprocess.check_output(['git','show','c6be35873e:crates/aspis-statement/src/logup.rs'],cwd=R).decode()
assert compression==function(base,'compress_tagged_tuple') and lift==function(base,'lift')
assert compression=='''pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
}'''
(T/'pole-compression.rs').write_text('use aspis_core::field::{M31,CM31,QM31};\n'+lift+'\n'+compression+'\n')
c=compression.replace('    let mut compressed =', '    super::pole_proofs::event(10);\n    let mut compressed =').replace('    for value in values {','    for (index, value) in values.iter().enumerate() {\n        super::pole_proofs::event(4000 + index as u32);').replace('        power =','        super::pole_proofs::event(11);\n        power =')
(T/'pole-compression-instrumented.rs').write_text('use aspis_core::field::{M31,CM31,QM31};\n'+lift+'\n'+c+'\n')
(T/'pole-compression-reference.rs').write_text('use super::reference::{M31,CM31,QM31};\n'+lift+'\n'+compression+'\n')
host=(R/'crates/aspis-r1-cost-probe/src/host_semantic.rs').read_text()
host_base=subprocess.check_output(['git','show','c6be35873e:crates/aspis-r1-cost-probe/src/host_semantic.rs'],cwd=R).decode()
assert function(host,'lean_copy_row_values')==function(host_base,'lean_copy_row_values')
assert 'return Ok(crate::ct_pole::all_slots_clear(&values, &masks, chi));' in function(host,'no_pole')
print(json.dumps(dict(lean_copy_row_values_unchanged=True,ct_pole_sha256=hashlib.sha256(s.encode()).hexdigest(),compression_sha256=hashlib.sha256(compression.encode()).hexdigest(),compression_unchanged_from_research=True,scope='Kani eager equality/fold step, two-row scan and 16-limb compression; public-shape scan composition; native full-1024-row traces; inherited field kernel gates'),indent=2))
