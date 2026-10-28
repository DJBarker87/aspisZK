"""Exact deployed source binding at V240's actual index-helper boundary.

No generic name-envelope or finite test is used to infer a call target. This
checks the caller, helper, shared-index impl, and pointer iterator primitives
separately. It does not grant a restored disposition by itself.
"""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
S=D/'src'
L=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|\w+|[^\s]',clean(s))
def body(s,needle):
 a=s.index('{',s.index(needle));depth=0
 for i in range(a,len(s)):
  depth+=(s[i]=='{')-(s[i]=='}')
  if depth==0:return s[a:i+1]
 raise ValueError(needle)
checks=[]
def check(p,needle,expected,law):
 raw=p.read_bytes();text=clean(raw.decode());b=body(text,needle)
 assert tokens(b)==tokens(expected),(str(p),needle,b)
 checks.append(dict(path=str(p),file_sha256=hashlib.sha256(raw).hexdigest(),item=needle,
   body=b,body_sha256=hashlib.sha256(b.encode()).hexdigest(),exact_tokens=True,law=law))
check(S/'crates/aspis-r1-cost-probe/src/prover_shared.rs','fn compress_tagged_tuple(','''{
 let mut compressed=QM31::from_cm31(CM31::from_m31(tag));let mut power=lambda;let mut i=0usize;
 while i<values.len(){compressed=compressed.add(power.mul_m31(values[i]));power=power.mul(lambda);i=i.wrapping_add(1);}
 compressed}''','PV_Op223_Applied.prover_shared.compress_tagged_tuple; Index.index_complete/read_copy_complete/increment_bound')
caller=(S/'crates/aspis-r1-cost-probe/src/host_semantic.rs').read_text()
assert 'let compressed=crate::prover_shared::compress_tagged_tuple(tag,&limbs,lambda);' in caller
nonnull=L/'core/src/ptr/non_null.rs'
assert hashlib.sha256(nonnull.read_bytes()).hexdigest()=='c1b6db4d0b71413bd827ff9cc4dc7f53a5bbb4945be3e1356943fa630c48732f'
src=clean(nonnull.read_text())
assert '#[repr(transparent)]' in src
assert tokens(body(src,'pub struct NonNull<'))==tokens('{pointer:*const T,}')
check(nonnull,'pub const fn from_ref(', '{unsafe{NonNull{pointer:r as *const T}}}', 'NonNull.from_ref_complete')
check(nonnull,'pub const fn cast<U>(', '{unsafe{NonNull{pointer:self.as_ptr() as *mut U}}}', 'NonNull.cast_complete/cast_provenance/cast_metadata')
check(nonnull,'pub const fn as_ptr(', '{unsafe{mem::transmute::<Self,*mut T>(self)}}', 'transparent single-field projection')
check(nonnull,"pub const unsafe fn as_ref<'a>(",'{unsafe{&*self.as_ptr().cast_const()}}','Pointer.next_storage; shared-reference storage relation')
check(nonnull,'pub const unsafe fn add(', '{unsafe{NonNull{pointer:intrinsics::offset(self.as_ptr(),count)}}}', 'Pointer.advance_address/read_bounds/advance_valid')
check(L/'core/src/slice/index.rs','fn index(self, slice: &[T])', '{&(*slice)[self]}','Index.index_complete; intrinsic checked indexing with unchanged storage')
check(L/'core/src/slice/iter.rs',"pub(super) const fn new(slice:",'''{
 let len=slice.len();let ptr:NonNull<T>=NonNull::from_ref(slice).cast();
 unsafe{let end_or_len=if T::IS_ZST{without_provenance(len)}else{ptr.as_ptr().add(len)};
 Self{ptr,end_or_len,_marker:PhantomData}}}''','NonNull.iterator_constructor; Pointer.valid')
check(L/'core/src/slice/iter/macros.rs','fn next(&mut self)', '''{
 let ptr=self.ptr;let end_or_len=self.end_or_len;
 unsafe{if T::IS_ZST{let len=end_or_len.addr();if len==0{return None;}
 self.end_or_len=without_provenance_mut(len.unchecked_sub(1));}
 else{if ptr==crate::intrinsics::transmute::<$ptr,NonNull<T>>(end_or_len){return None;}
 self.ptr=ptr.add(1);}Some({ptr}.$into_ref())}}''','Pointer.next_complete/next_storage; shared sized M31 branch only')
out=dict(row='V240',artifact='devnet_spend',toolchain='rustc1.94.1',
 profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',
 resolved_features_reference='native-leaves/receipt.json',checks=checks,
 actual_caller=dict(path='crates/aspis-r1-cost-probe/src/host_semantic.rs',sha256=hashlib.sha256(caller.encode()).hexdigest(),call='crate::prover_shared::compress_tagged_tuple(tag,&limbs,lambda)'),
 source_boundary='actual candidate index helper; original logup iterator is a separate source boundary',
 differences=[dict(old='transparent transmute',deployed='explicit single field construction',proof='NonNull.from_ref_complete/cast_complete',effects='address/allocation identity retained; target-sized cast drops metadata; heap and borrow tokens unchanged')],
 machine_boundary='Rust intrinsic indexing, reference semantics, repr(transparent), word-copy and offset semantics; no SBF or compiler correctness claim',
 structural_status='local bodies checked; row restoration additionally requires concrete proof-cone replay and exact arithmetic/call association',restored=False)
(D/'V240-deployed-body-binding.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS exact deployed candidate index helper, caller, checked indexing and pointer primitive bodies')
