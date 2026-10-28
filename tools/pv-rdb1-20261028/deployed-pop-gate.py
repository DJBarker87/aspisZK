"""Fail-closed complete-body binding for the deployed pop library boundary.
Primitive pointer/load/copy meanings retain the original structural boundary.
No Kani, compiler, allocator internals or machine adequacy credit is claimed.
"""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
checks=[]
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tok(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def end(s,a):
 d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return i+1
 raise ValueError('unclosed body')
def body(s,anchor):
 s=clean(s);a=s.index('{',s.index(anchor));return s[a:end(s,a)]
def release(s):
 # Exactly two cfg-gated debug-only items in ptr::add and one in ptr::read.
 # Remove only complete annotated declarations or macro statements.
 marker='#[cfg(debug_assertions)]'
 while marker in s:
  a=s.index(marker);brace=s.find('{',a);semi=s.find(');',a)
  z=brace if brace >= 0 and (semi < 0 or brace < semi) else -1
  if z>=0:
   b=end(s,z)
  else:
   b=s.index(');',a)+2
  s=s[:a]+s[b:]
 return s

def check(file,anchor,want,law,select=False):
 p=S/file;s=p.read_text();actual=body(s,anchor);selected=release(actual) if select else actual
 assert tok(selected)==tok(want),(file,anchor,selected,want)
 # Matched source negative control: changing an operation is rejected.
 assert tok(selected+';')!=tok(want)
 checks.append(dict(file=str(p),file_sha256=hashlib.sha256(s.encode()).hexdigest(),anchor=anchor,complete_body=actual,selected_release_body=selected,tokens_equal=True,law=law))

check('core/src/ptr/non_null.rs','pub struct NonNull','{pointer: *const T,}','repr transparent pointer wrapper')
s=(S/'core/src/ptr/non_null.rs').read_text();prefix=s[:s.index('pub struct NonNull')]
assert '#[repr(transparent)]' in prefix[-1800:]
check('core/src/ptr/non_null.rs','pub const fn as_ptr','{unsafe {mem::transmute::<Self, *mut T>(self)}}','transparent representation; no pointer-to-integer conversion')
check('core/src/ptr/non_null.rs','pub const fn cast<U>','{unsafe {NonNull {pointer: self.as_ptr() as *mut U}}}','PV_RDB1_Pointer.cast_complete; cast_observation')
check('core/src/ptr/unique.rs','pub const fn cast<U>','{Unique {pointer: self.pointer.cast(), _marker: PhantomData}}','cast_complete, zero-size PhantomData')
check('core/src/ptr/unique.rs','pub const fn as_non_null_ptr','{self.pointer}','transparent projection')
for a,w in [('pub(crate) const fn ptr(', '{self.inner.ptr()}'),('fn ptr<T>', '{self.non_null::<T>().as_ptr()}'),('fn non_null<T>', '{self.ptr.cast().as_non_null_ptr()}'),('pub(crate) const fn capacity(', '{self.inner.capacity(size_of::<T>())}'),('fn capacity(&self, elem_size', '{if elem_size == 0 {usize::MAX} else {self.cap.as_inner()}}')]:
 check('alloc/src/raw_vec/mod.rs',a,w,'pointer projections/cast law; capacity unchanged (usize::MAX for ZST)')
check('core/src/num/niche_types.rs','pub const fn as_inner','{unsafe {crate::mem::transmute(self)}}','transparent UsizeNoHighBit unwrapping; no arithmetic/effect')
for a,w in [('pub const fn as_ptr(', '{self.buf.ptr()}'),('pub const fn capacity(', '{self.buf.capacity()}'),('pub const fn len(', '{let len = self.len; unsafe {intrinsics::assume(len <= T::MAX_SLICE_LEN)}; len}')]:
 check('alloc/src/vec/mod.rs',a,w,'retained valid-vector invariant and direct header/pointer projection')
check('alloc/src/vec/mod.rs','pub fn pop(','''{if self.len == 0 {None} else {unsafe {self.len -= 1;core::hint::assert_unchecked(self.len < self.capacity());Some(ptr::read(self.as_ptr().add(self.len())))}}}''','PV_RDB1_V184.complete; last_bounds; read_address')
check('core/src/ptr/const_ptr.rs','pub const unsafe fn add(', '{unsafe {intrinsics::offset(self, count)}}','PV_RDB1_Pointer.offset_cast, offset_bounds, offset_zst, no_wrap; retained valid owned allocation domain',True)
check('core/src/ptr/mod.rs','pub const unsafe fn read<T>', '{unsafe {crate::intrinsics::read_via_copy(src)}}','retained initialized readSlot meaning; backing bytes unchanged',True)
# The assume is true for every admitted nonempty buffer, independently of
# whether optional UB checks are enabled. No panic runtime can be reached.
check('core/src/hint.rs','pub const unsafe fn assert_unchecked(','''{unsafe {ub_checks::assert_unsafe_precondition!(check_language_ub,"hint::assert_unchecked must never be called when the condition is false",(cond: bool = cond) => cond,);crate::intrinsics::assume(cond);}}''','PV_RDB1_Pointer.last_bounds; false precondition branch unreachable')
check('alloc/src/vec/mod.rs','pub fn remove(','''{#[cold] #[cfg_attr(not(panic = "immediate-abort"), inline(never))] #[track_caller] #[optimize(size)] fn assert_failed(index: usize, len: usize) -> ! {panic!("removal index (is {index}) should be < len (is {len})");} match self.try_remove(index) {Some(elem) => elem,None => assert_failed(index, self.len()),}}''','MoveFacts.last_bound excludes None/panic')
check('alloc/src/vec/mod.rs','pub fn try_remove(','''{let len = self.len();if index >= len {return None;} unsafe {let ret;{let ptr = self.as_mut_ptr().add(index);ret = ptr::read(ptr);ptr::copy(ptr.add(1), ptr, len - index - 1);}self.set_len(len - 1);Some(ret)}}''','MoveLast.remove_last; MoveMemory.last_copy; one-past bounds for zero-count copy')
check('alloc/src/vec/mod.rs','pub const fn as_mut_ptr(', '{self.buf.ptr()}','same pointer law as as_ptr')
check('alloc/src/vec/mod.rs','pub unsafe fn set_len(','''{ub_checks::assert_unsafe_precondition!(check_library_ub,"Vec::set_len requires that new_len <= capacity()",(new_len: usize = new_len, capacity: usize = self.capacity()) => new_len <= capacity);self.len = new_len;}''','shorten; last_bounds proves precondition')
# Compare the actual old changed body too: identical cast expression, differing
# only in transparent wrapping versus transmute. Never equate arbitrary casts.
old=Path(str(S).replace('1.94.1','nightly-2026-06-01'))/'core/src/ptr/non_null.rs'
b=body(old.read_text(),'pub const fn cast<U>')
assert tok(b)==tok('{unsafe {transmute(self.as_ptr() as *mut U)}}')
ref=(D/'pop-move-reference.rs').read_text()
assert tok(body(ref,'pub fn pop_move_reference<T>'))==tok('{let n = v.len();if n == 0 {None} else {Some(v.remove(n-1))}}')
assert tok(body(ref,'pub fn pop_move_owned<T>'))==tok('{let last=pop_move_reference(&mut v);(last,v)}')
# Source model embedding checked against committed local source pins on upload.
j=dict(row='V184',evidence_class='structural (K-1 substitute)',checks=checks,old_cast=dict(path=str(old),body=b,sha256=hashlib.sha256(old.read_bytes()).hexdigest()),reference_sha256=hashlib.sha256(ref.encode()).hexdigest(),complete_Result_law='R1Z.PV_RDB1_V184.complete',pointer_law='R1Z.PV_RDB1_Pointer.cast_complete',resolved_edges={'assert_unchecked::precondition_check':'last_bounds proves cond true; no panic', 'check_language_ub/runtime':'optional branch cannot fail because condition is true', 'niche_types::as_inner':'complete transparent unwrap checked', 'panic_nounwind_fmt/runtime':'unreachable from valid pop/remove-last', 'const_ptr::add':'complete release body is intrinsic offset; bounds/no_wrap law with original valid-buffer relation'},retained_boundary='Initialized-slot read, transparent representation, raw cast/offset/copy intrinsic semantics, valid runtime carrier, compiler/executable, allocator and side channels unchanged. No new trust field. No allocator or destructor call in pop/remove-last.',features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3; debug_assertions=false; overflow_checks=false; panic=unwind',native_differential=['native-pop/receipt.json','native-pop-zst/receipt.json'],kani_credit=False)
(D/'v184-deployed-binding.json').write_text(json.dumps(j,indent=2)+'\n')
print('PASS V184: complete deployed pointer/pop/remove-last source binding; no allocator/destructor effect; original intrinsic boundary retained')
