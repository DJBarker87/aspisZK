"""Resolve V240's reached primitive families, not the conservative crate envelope."""
from pathlib import Path
import json,lzma,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028');S=D/'src'
files=json.loads(lzma.decompress((D/'prior-sources.json.xz').read_bytes()))['files']
L=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|\w+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return s[a:i+1]
 raise ValueError(needle)
out=[]
for rel,names in {
 'core/src/num/uint_macros.rs':['pub const fn wrapping_add(', 'pub const fn wrapping_sub(', 'pub const fn wrapping_mul('],
 'core/src/slice/index.rs':['fn index(self, slice: &[T])'],
}.items():
 old=files['evidence/library/'+rel];new=files['deployed/library/'+rel]
 raw=(L/rel).read_bytes();assert hashlib.sha256(raw).hexdigest()==new['sha256']
 assert hashlib.sha256(old['text'].encode()).hexdigest()==old['sha256']
 for name in names:
  a=body(old['text'],name);b=body(raw.decode(),name)
  assert tokens(a)==tokens(b),(rel,name,a,b)
  out.append(dict(path=rel,item=name,old_file_sha256=old['sha256'],deployed_file_sha256=new['sha256'],old_body=a,deployed_body=b,body_tokens_identical=True))
bundle=json.loads((D/'project-native-inputs.json').read_text())
owned=bundle['tools/pv-cb-20261026/step-proof/owned_compress.rs']['text']
native=(S/'crates/aspis-r1-cost-probe/src/prover_shared.rs').read_text()
a=body(owned,'pub fn compress(');b=body(native,'fn compress_tagged_tuple(')
assert [x if x!='out' else 'compressed' for x in tokens(a)]==tokens(b)
out.append(dict(native='prover_shared::compress_tagged_tuple',owned='original finite differential compress::compress',difference='alpha rename out to compressed only',complete_body_tokens_equal_after_alpha_rename=True,owned_sha256=hashlib.sha256(owned.encode()).hexdigest()))
field=(S/'crates/aspis-core/src/field.rs').read_text()
assert '#[cfg(feature = "ct-host-prover")]\nimpl M31 {' in field
ct=field[field.index('#[cfg(feature = "ct-host-prover")]\nimpl M31 {'):]
for name,expected in [('add','{Self(ct::add(self.0,rhs.0))}'),('sub','{Self(ct::sub(self.0,rhs.0))}')]:
 assert tokens(body(ct,'pub fn '+name+'('))==tokens(expected)
assert 'fn reduce_u64(x: u64) -> u32 { ct::reduce64(x) }' in field
selected=dict(artifact='devnet_spend',project_features_reference='native-leaves/receipt.json',
 core_ct_enabled=True,core_audit_instrumentation_disabled=True,
 fields=['CM31.from_m31','QM31.from_cm31','QM31.add','QM31.mul','QM31.mul_m31'],
 owned_lean='PV_RDB2_Applied_00_P through PV_RDB2_Applied_25_compress',
 complete_result='R1Z.PV_RDB2_Compress.complete/installed',
 no_allocation_in_helper=True,no_mutable_borrow_in_helper=True,
 pointer_boundary='intrinsic shared slice indexing; arrayOutOfBounds on rejection; loop guard excludes rejection at every reached read',
 excluded_envelope='NonNull/SIMD/allocator/formatting symbols from the old original-logup conservative crate envelope are not calls in the actual candidate index-helper body. No law for those symbols is inferred from this exclusion.')
(D/'V240-primitive-binding.json').write_text(json.dumps(dict(checks=out,selection=selected,profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='rustc1.94.1'),indent=2)+'\n')
print('PASS uint wrapping families, shared-index body, deployed CT selection and original owned fixture association')
