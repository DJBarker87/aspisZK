"""Static influence-channel census for GenericArray<u8,U64>::default.
This is the static half of own-2 triple-prime, never a source-binding proof.
"""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
lib={x['relative']:x for f in ['library-sources.json','v237-library-sources.json'] for x in json.load(open(E/f))}
deps={(x['crate'],x['relative']):x for x in json.load(open(E/'buffer-dependency-sources.json'))}
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def span(record,context,marker):
 s=record['text'];assert s.count(context)==1,(record['path'],context,s.count(context));a=s.index(marker,s.index(context));b=s.index('{',a);depth=0
 for m in lex.finditer(s,b):
  if m[0]=='{':depth+=1
  elif m[0]=='}':
   depth-=1
   if not depth:return s[a:m.end()]
 raise AssertionError(marker)
rows=[]
def add(record,context,marker,channels,callees):
 body=span(record,context,marker)
 words=[m[0] for m in lex.finditer(body) if not m[0].startswith(('//','/*','"'))]
 assert not set(words).intersection({'static','thread_local','getenv','errno','random','clock_gettime','read_volatile','asm','extern'}),(marker,words)
 rows.append(dict(path=record['path'],file_sha256=record['sha256'],context=context,marker=marker,body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest(),influence_channels=channels,callees=callees))
g=deps['generic-array-0.14.7','lib.rs'];i=deps['generic-array-0.14.7','impls.rs']
add(i,'Default for GenericArray<T, N>','fn default(', 'No arguments; concrete T=u8 literal default, N=U64 fixed public type.','GenericSequence.generate; zero-capture u8 Default closure')
add(g,'GenericSequence<T> for GenericArray<T, N>','fn generate<','All state is local: uninitialized stack storage, initialized position0, fixed64 writes. No old destination byte is read.','ArrayBuilder.new/iter_position/into_inner; Iterator.enumerate/for_each; ptr.write; u8.default; local position increment')
for marker,channels,callees in [
('pub unsafe fn new(', 'Construct local MaybeUninit and position0. No allocator.', 'MaybeUninit.uninit'),
('pub unsafe fn iter_position(', 'Borrow only the caller-owned builder array and position field; no old byte values read.','MaybeUninit.as_mut_ptr; GenericArray.deref_mut; slice.iter_mut'),
('pub unsafe fn into_inner(', 'Read fully initialized local array after64 writes; forget builder to suppress its Drop; return those bytes.','ptr.read; mem.forget; MaybeUninit.assume_init')]:
 add(g,'impl<T, N: ArrayLength<T>> ArrayBuilder<T, N>',marker,channels,callees)
add(g,'Drop for ArrayBuilder<T, N>','fn drop(', 'Normal path suppressed by forget. Any unwind guard tests needs_drop<u8>=false; no destructor callback.','mem.needs_drop (compiler Copy/type property); element drop branch excluded')
add(g,'DerefMut for GenericArray<T, N>','fn deref_mut(', 'Cast same local object pointer and form a mutable slice with constant N::USIZE=64. Returned addresses never become result bytes.','slice.from_raw_parts_mut; typename constant64; compiler pointer casts')
add(lib['slice/mod.rs'],'pub const fn iter_mut(','pub const fn iter_mut(', 'Forward same borrowed local slice.','IterMut.new')
add(lib['slice/iter.rs'],"impl<'a, T> IterMut<'a, T>",'pub(super) const fn new(', 'Only slice metadata and the local allocation pointer. T::IS_ZST=false for u8; end=base+64.','slice.len; NonNull.from_mut/cast/as_ptr; pointer.add; PhantomData construction')
add(lib['iter/traits/iterator.rs'],'fn enumerate(self)','fn enumerate(self)', 'Move the same iterator into an adapter.','Enumerate.new')
add(lib['iter/adapters/enumerate.rs'],'pub(in crate::iter) fn new(', 'pub(in crate::iter) fn new(', 'Store iterator and initialize count0.','Struct construction only')
add(lib['iter/traits/iterator.rs'],'fn for_each<F>','fn for_each<F>', 'Unit accumulator; closure forwards each local item; no output or system interaction.','Enumerate.fold; call closure adapter')
add(lib['iter/adapters/enumerate.rs'],'fn fold<Acc, Fold>','fn fold<Acc, Fold>', 'Count starts0, increments after each local closure, bounded by64.','IterMut.fold; supplied closure ptr.write then position increment')
add(lib['slice/iter/macros.rs'],'fn fold<B, F>','fn fold<B, F>', 'is_empty and len compare/subtract pointers in the same fixed64-byte allocation. In the u8 branch guards and distance depend only on relative offsets. Body indexes0..63 and only passes each local write location.','is_empty!/len! macros; NonNull.add/as_ptr; unchecked usize increment; supplied local closure')
for name,context,marker,channels,callees in [
('mem/maybe_uninit.rs','pub const fn uninit()','pub const fn uninit()', 'Create local uninitialized storage without reading its contents.','Union/unit construction'),
('mem/maybe_uninit.rs','pub const fn as_mut_ptr(','pub const fn as_mut_ptr(', 'Same caller-owned storage pointer; no data read.','Pointer cast only'),
('mem/maybe_uninit.rs','pub const unsafe fn assume_init(self)','pub const unsafe fn assume_init(self)', 'Read the local fully initialized value; inhabited u8 array type.','assert_inhabited; const-pointer cast/read of the same initialized local storage; compiler primitive'),
('mem/mod.rs','pub const fn forget<','pub const fn forget<', 'Suppress Drop through ManuallyDrop; no external state.','ManuallyDrop.new'),
('mem/manually_drop.rs','pub const fn new(value: T)','pub const fn new(value: T)', 'Store the same moved local value.','Struct construction only'),
('ptr/mod.rs','pub const unsafe fn write<T>','pub const unsafe fn write<T>', 'Write the supplied zero to supplied local storage. Does not read or drop old bytes. debug_assertions block inactive.','intrinsics.write_via_move; compiler/runtime memory primitive'),
('ptr/mod.rs','pub const unsafe fn read<T>','pub const unsafe fn read<T>', 'Read only supplied fully initialized caller-local storage.','intrinsics.read_via_copy; compiler/runtime memory primitive'),
('slice/raw.rs','pub const unsafe fn from_raw_parts_mut<','pub const unsafe fn from_raw_parts_mut<', 'Construct slice over same supplied local storage and constant length64; UB debug checks inactive in deployed release.','ptr.slice_from_raw_parts_mut; compiler reference formation')]:
 add(lib[name],context,marker,channels,callees)
# Macro instantiation is fixed, not an arbitrary Default implementation.
assert 'default_impl! { u8, 0,' in lib['default.rs']['text']
add(lib['default.rs'],'macro_rules! default_impl','macro_rules! default_impl', 'Instantiate $t=u8,$v=0. No input, no capture, no callee.','Literal0 only')
# Every low-level source file is pinned and scanned at these confined wrappers.
for name,context,marker in [
('ptr/non_null.rs','pub const fn from_mut(','pub const fn from_mut('),
('ptr/non_null.rs','pub const fn cast<U>','pub const fn cast<U>'),
('ptr/non_null.rs','pub const fn as_ptr(self)','pub const fn as_ptr(self)'),
('ptr/non_null.rs','pub const unsafe fn add(self','pub const unsafe fn add(self'),
('ptr/mut_ptr.rs','pub const unsafe fn add(self','pub const unsafe fn add(self'),
('ptr/const_ptr.rs','pub const unsafe fn offset_from_unsigned','pub const unsafe fn offset_from_unsigned')]:
 add(lib[name],context,marker,'Only supplied same-allocation pointer coordinates/counts; no mutable external data read. Debug precondition branches inactive; address tests normalize to public relative bounds.','Compiler pointer arithmetic/projection intrinsics and precondition wrappers; V370 retained')
for name,context,marker,reason in [
('slice/iter/macros.rs','macro_rules! if_zst','macro_rules! if_zst','T=u8 is non-ZST. Only the same-allocation pointer branch is reached; the ZST addr() branch is excluded.'),
('slice/iter/macros.rs','macro_rules! is_empty','macro_rules! is_empty','Compare base with end=base+64; fixed false, by relative endpoint equality.'),
('slice/iter/macros.rs','macro_rules! len {','macro_rules! len {','Same-allocation unsigned pointer distance is64, independent of base.'),
('ptr/mut_ptr.rs','PartialEq for *mut T','fn eq(','Primitive equality of the same local base/end thin pointers; no external memory read.'),
('ptr/non_null.rs','PartialEq for NonNull<T>','fn eq(','Thin u8 pointers compared only as base/end from one fixed-length allocation.'),
('ptr/non_null.rs','pub const unsafe fn new_unchecked(','pub const unsafe fn new_unchecked(','Forward the supplied non-null local pointer. Language UB checks inactive; no external state read.'),
('ptr/non_null.rs','pub const unsafe fn offset_from_unsigned','pub const unsafe fn offset_from_unsigned','Same supplied pointers forward to raw-pointer distance; result constant64.'),
('ptr/mut_ptr.rs','pub const unsafe fn offset_from_unsigned','pub const unsafe fn offset_from_unsigned','Same supplied pointers forward to const-pointer distance; result constant64.'),
('ptr/mod.rs','pub const fn slice_from_raw_parts_mut<','pub const fn slice_from_raw_parts_mut<','Forward supplied local pointer and constant length to metadata construction.'),
('ptr/metadata.rs','pub const fn from_raw_parts_mut<','pub const fn from_raw_parts_mut<','Aggregate the same local pointer and supplied length; no pointee read.'),
('ptr/const_ptr.rs','pub const fn cast<U>','pub const fn cast<U>','Same local address, transparent type cast; no external memory read.'),
('ptr/const_ptr.rs','pub const unsafe fn read(self)','pub const unsafe fn read(self)','Forward the same initialized local pointer to ptr.read.'),
('slice/mod.rs','pub const fn len(','pub const fn len(','Return caller-supplied slice metadata, here64.'),
('ptr/metadata.rs','pub const fn metadata<','pub const fn metadata<','Return compiler pointer metadata from the supplied pointer.'),
('ub_checks.rs','macro_rules! assert_unsafe_precondition','macro_rules! assert_unsafe_precondition','Precondition call gated by check_language_ub/ub_checks; no argument expression or panic diagnostic executes in the deployed release.'),
('ub_checks.rs','pub(crate) const fn check_language_ub','pub(crate) const fn check_language_ub','Runtime UB checks false for deployed debug_assertions=false; constant-evaluation branch also false.')]:
 add(lib[name],context,marker,reason,'Argument-confined source macro/forwarding and compiler intrinsics; no unclassified external callee')
# Known memory builtins may inspect implementation state internally; the ruling
# classifies their effect channels, not their foreign or internal origin.
out=dict(root='generic_array0.14.7::GenericArray<u8,typenum1.20.1::U64>::default()',input_domain='unit; no parameters or captured environment',records=rows,allocation_requests=[],memory_primitives='Any introduced memset/memcpy/memmove operates only on caller-supplied local storage; permitted own-2 triple-prime(1), semantics retained at V370.',address_independence='IterMut base/end and len use one valid allocation of64 u8. base+offset=base+length iff offset=length and (base+length)-base=length; named V237 address lemmas. Pointer values feed only local memory destinations, not returned byte values. No address hashing or address-to-integer result/control channel survives release checks.',allocator_channel_iii='Closed: no allocator call or external mutable read in this helper cone.',drop='u8 is Copy, has no Drop; builder is forgotten on success, unwind needs_drop<u8> false; closure/iterator captures are references or unit.',errors='No zero-sized block check in GenericArray helper. Its fixed64 iteration cannot overflow. u8.default cannot panic. BlockBuffer64 zero guard and CoreWrapper field order belong to separate own-1 original-checker bindings; Core::default remains original full Result parameter.',disqualifying_channels=[],qualification='Static influence census only. Requires fresh literal-value kernel proof and exhaustive deployed-configuration harness execution. Does not itself restore V237.',evidence_class='exhaustive over a singleton input domain, deployed-configuration harness (pending execution)')
(E/'v237-influence-census.json').write_text(json.dumps(out,indent=2)+'\n');print(len(rows),'complete source bodies/macro nodes classified; no disqualifying influence channel; native and kernel gates pending.')
