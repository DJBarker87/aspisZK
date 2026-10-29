"""Generate verbatim-prefix modules with harness-only visibility adapters.
The original deployed and reference files are never edited. --check is preflight.
"""
from pathlib import Path
import json,hashlib,sys,re
P=Path('tools/pv-b3p6-20261028/v244');D=Path('evidence/pv-b3p6-20261028/resume16');D.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
wrappers={
'copy':'''pub(crate) mod access16 { use super::*;
pub fn mask(v:&[QM31;16],m:u16)->QM31 { MASK_CALL }
#[cfg(not(feature="optimized-terminal"))]
pub fn active(h:[QM31;64],l:[QM31;16])->QM31 { Selectors{high:h,low:l}.active_literal() }
pub fn pattern(v:&[QM31;16],l:QM31)->[QM31;14] { pattern_values_literal(v,l) }
pub fn masks()->[u16;64] { constants::ACTIVE_ROW_MASKS }
}''',
 'terminal':'''pub(crate) mod access16 { use super::*;
pub fn pre<const N:usize>(p:&mut[QM31;24],s:usize,v:&[QM31;N]) { add_preweighted(p,s,v) }
#[cfg(feature="optimized-terminal")]
pub fn shared<const N:usize>(p:&mut[QM31;24],s:usize,v:&[QM31;N],q:QM31) { add_preweighted_shared_selector(p,s,v,q) }
pub fn reconstruct(v:&[QM31;16])->QM31 { reconstruct_10(v) }
pub fn equality(a:&[QM31;10],b:&[QM31;10])->QM31 { equality_value(a,b) }
pub fn sum(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>])->QM31 { sum_high(&Selectors{high:h,low:l},r) }
#[cfg(not(feature="optimized-terminal"))]
pub fn digest(o:&mut[QM31;8],q:QM31,v:&[QM31;16],s:usize,d:&[M31;8],t:bool) { add_digest_binding(o,q,v,s,d,t) }
#[cfg(not(feature="optimized-terminal"))]
pub fn absorption(a:[QM31;5],v:&[QM31;16])->[QM31;16] { absorption_lanes_literal(a[0],a[1],a[2],a[3],a[4],v) }
#[cfg(not(feature="optimized-terminal"))]
pub fn occupancy(a:QM31,b:QM31,c:M31,v:&[QM31;16])->[QM31;12] { occupancy_lanes_literal(a,b,c,v) }
}'''
}
records=[]
for family,stem in [('copy','copy_terminal'),('terminal','terminal')]:
 for side in ['host','reference']:
  src=P/f'{side}_{stem}.rs';raw=src.read_bytes();w=wrappers[family]
  if side=='reference':w=w.replace('add_digest_binding(o,q,v,s,d,t)', '*o=add_digest_binding(*o,q,*v,s,*d,t)').replace('absorption_lanes_literal(a[0],a[1],a[2],a[3],a[4],v)', 'absorption_lanes_literal(a[0],a[1],a[2],a[3],a[4],v)')
  if family=='copy':w=w.replace('MASK_CALL','selector_mask_sum_16(v,m)' if side=='host' else 'selector_mask_sum_16(*v,m)')
  dest=P/f'{side}_{stem}_kani16.rs';out=raw+b'\n// Harness-only adapters after an unmodified module prefix.\n'+w.encode()+b'\n'
  if '--check' in sys.argv:assert dest.read_bytes()==out
  else:dest.write_bytes(out)
  deployed=Path('crates/aspis-r1-cost-probe/src')/src.name if side=='host' else src
  assert deployed.read_bytes()==raw
  records.append(dict(path=str(dest),prefix_source=str(deployed),prefix_bytes=len(raw),prefix_sha256=sha(raw),module_sha256=sha(out),identity='exact byte prefix; only appended visibility adapters'))
# Avoid touching the established lib.rs or deployed bodies.
lib='''#![feature(allocator_api)]
extern crate alloc;
mod host_terminal_field;
#[path="host_copy_terminal_kani16.rs"] mod host_copy_terminal;
#[path="host_terminal_kani16.rs"] mod host_terminal;
#[path="reference_copy_terminal_kani16.rs"] mod reference_copy_terminal;
#[path="reference_terminal_kani16.rs"] mod reference_terminal;
mod reference_field;
mod reference_poseidon;
mod std194227;
#[path="../kmx/KMX_stubs.rs"] mod KMX_stubs;
#[cfg(kani)] mod equivalence16;
'''
if '--check' in sys.argv:assert (P/'lib_kani16.rs').read_text()==lib
else:(P/'lib_kani16.rs').write_text(lib)
# Independent manifest retains exact original dependency/feature resolution.
(P.parent/'v244-kani16').mkdir(exist_ok=True)
m=(P/'Cargo.toml').read_text().replace('path="lib.rs"','path="../v244/lib_kani16.rs"')
m=re.sub(r'\[\[bin\]\][\s\S]*?(?=\[dependencies\])','',m,count=1)
m=re.sub(r'\n\[\[bin\]\][\s\S]*$','\n',m)
if '--check' in sys.argv:assert (P.parent/'v244-kani16'/'Cargo.toml').read_text()==m
else:(P.parent/'v244-kani16'/'Cargo.toml').write_text(m)
(D/'verbatim-prefixes.json').write_text(json.dumps(records,indent=2)+'\n')
print('verbatim-prefix preflight',len(records))


