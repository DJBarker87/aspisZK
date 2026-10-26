"""Check proposed cfg(kani)-only wrappers against actual shipped loop snippets."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(__file__).resolve().parents[2]
src=root/'crates/aspis-core/src/state_only_hiding.rs'
s=src.read_text();template=(Path(__file__).with_name('mask_step_template.rs')).read_text()
needles=[
'coefficients[usize::from(FACTOR_EXPONENTS[column])] =\n            mul_tower_basis(c1[column], column & 3);',
'coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =\n            mul_tower_basis(mask_only_c1[column], column & 3);',
'suffix = suffix.add(point[variable]);\n        if variable != 0 {\n            weighted = weighted.add(suffix);\n        }',
'shared = prepared_linear.mul(shared).add(coefficients[exponent]);']
for n in needles:
 assert s.count(n)==1,(n,'source occurrence count',s.count(n))
 assert template.count(n)==1,(n,'wrapper occurrence count')
r=dict(shipped_source=str(src.relative_to(root)),shipped_source_sha256=hashlib.sha256(s.encode()).hexdigest(),wrapper_sha256=hashlib.sha256(template.encode()).hexdigest(),snippets=[dict(text=n,sha256=hashlib.sha256(n.encode()).hexdigest()) for n in needles],status='PREPARED exact source-body wrappers, not a P6 result',bounds=dict(c1='column<16; coeff length27; exponent table slots0..26',mask='column<10; coeff length27; exponent table slots1..21',linear='variable<10',horner='exponent<26; coeff length27'),no_stubs=True)
out=root/'evidence/pv-cb-20261026/mask-step-source-check.json'
out.write_text(json.dumps(r,indent=2)+'\n');print(r['status'])

# Capture the unmodified shipped module in a cfg(kani)-only proof crate. Only
# inner documentation comments become ordinary comments for inclusion. No
# production crate is edited; the whole-function Kani mirror gate binds it.
body='\n'.join('//'+line[3:] if line.startswith('//!') else line for line in s.splitlines())+'\n'
suffix='\n'.join('//'+line[3:] if line.startswith('//!') else line for line in template.replace('#![cfg(kani)]\n','',1).splitlines())+'\n'
mirror=body+'\n// Proof-only step exports follow the exact captured source.\n'+suffix
(root/'tools/pv-cb-20261026/step-proof/captured_mask.rs').write_text(mirror)
r.update(captured_prefix_sha256=hashlib.sha256(body.encode()).hexdigest(),captured_module_sha256=hashlib.sha256(mirror.encode()).hexdigest(),capture_change='only inner //! documentation comments changed to ordinary // comments; all shipped function/constant bodies are byte-identical; proof step exports appended',binding_gate='checks::captured_source with all37 raw QM31 values and unwind40; not yet run')
out.write_text(json.dumps(r,indent=2)+'\n')
