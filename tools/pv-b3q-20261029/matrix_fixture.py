"""Generate an exact-source matrix observer without replacing its private payload type."""
from pathlib import Path
import subprocess,json,hashlib,re
D=Path('evidence/pv-b3q-20261029');T=Path('tools/pv-b3q-20261029/matrix');T.mkdir(exist_ok=True)
def git(p):return subprocess.check_output(['git','show','15819d2768:'+p])
def sha(x):return hashlib.sha256(x).hexdigest()
raw=git('crates/aspis-core/src/field.rs');text=raw.decode();start=text.index('pub fn qm31_sum_products3_prepared(');b=text.index('{',start);depth=1;e=b+1
while depth:depth+=(text[e]=='{')-(text[e]=='}');e+=1
original=text[start:e];observed=original.replace('pub fn qm31_sum_products3_prepared(','pub fn observed_matrix(',1).replace(') -> QM31 {',') -> (QM31, [[u64;3];3]) {',1)
assert observed.count('qm31_from_karatsuba_channel_sums(sums)')==1
observed=observed.replace('qm31_from_karatsuba_channel_sums(sums)','(qm31_from_karatsuba_channel_sums(sums), sums)')
# Exact erasure of the sole observation and signature change recovers ALL tokens.
erased=observed.replace('pub fn observed_matrix(','pub fn qm31_sum_products3_prepared(',1).replace(') -> (QM31, [[u64;3];3]) {',') -> QM31 {',1).replace('(qm31_from_karatsuba_channel_sums(sums), sums)','qm31_from_karatsuba_channel_sums(sums)')
assert erased==original
# The function lives in the exact original field module. No prepared-type adapter.
(T/'field.rs').write_bytes(raw+b'\n'+observed.encode()+b'\n')
(T/'field').mkdir(exist_ok=True)
for name in ['ct.rs','wide_exact.rs']:(T/'field'/name).write_bytes(git('crates/aspis-core/src/field/'+name))
# Original private components are exposed only as a read-only observer.
with (T/'field.rs').open('a')as f:f.write('\npub fn observed_components(p: &PreparedQm31Multiplier) -> [[M31;3];3] { p.components }\n')
x=dict(source_revision='15819d2768e2ed80a614edae6aa5d7dcb9055e84',original_field_sha256=sha(raw),original_function_sha256=sha(original.encode()),observed_function_sha256=sha(observed.encode()),observation_erasure_byte_identical=True,adapter='none: exact source module, exact private PreparedQm31Multiplier, exact constructor, exact ct arithmetic',observation='copy sums after all 27 assignments at original reconstruction argument; all nine entries returned',source_store_statement='sums[component][channel] += left[index].components[component][channel].0 as u64 * right_components[component][channel].0 as u64;',finite_validation_only=True,input_hashes={str(p):sha(p.read_bytes())for p in T.rglob('*.rs')})
(D/'matrix-source-association.json').write_text(json.dumps(x,indent=2)+'\n')
