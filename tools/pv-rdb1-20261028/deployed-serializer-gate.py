from gate_common import *
import ast
F=D.parent/'codex-pv-fscan-20261028';p=F/'src/crates/aspis-core/src/field/wide_exact.rs';s=p.read_text()
for anchor,want in [('pub fn to_le_bytes(', '{let mut bytes=[0;Self::BYTE_LEN];for (chunk,limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs()) {chunk.copy_from_slice(&limb.to_le_bytes());}bytes}'),('pub const fn to_limbs(', '{[self.c0.c0.a.0,self.c0.c0.b.0,self.c0.c1.a.0,self.c0.c1.b.0,self.c1.c0.a.0,self.c1.c0.b.0,self.c1.c1.a.0,self.c1.c1.b.0,]}')]:
 actual=body(s,anchor);assert tok(actual)==tok(want),(anchor,actual)
 checks.append(dict(file=str(p),file_sha256=hashlib.sha256(s.encode()).hexdigest(),anchor=anchor,complete_body=actual,tokens_equal=True))
assert 'pub const LIMB_COUNT: usize = 8;' in s and 'pub const BYTE_LEN: usize = 32;' in s
bundle=json.loads((F/'project-native-inputs.json').read_text());ref=bundle['tools/pv-relink-20261028/v195-bridge.rs']['text'];flat=body(ref,'fn wide_bytes_flat(')
assert re.findall(r'let ([a-h])=l\[(\d)\].to_le_bytes\(\)',flat)==[(chr(97+i),str(i)) for i in range(8)]
assert re.findall(r'([a-h])\[(\d)\]',flat)==[(chr(97+i),str(j)) for i in range(8) for j in range(4)]
checks.append(dict(owned_reference='tools/pv-relink-20261028/v195-bridge.rs',sha256=hashlib.sha256(ref.encode()).hexdigest(),complete_body=flat,coordinates='all8 scalar calls/all32 coordinates in identical limb order'))

def scoped(file,scope,anchor,want):
 p=S/file;s=p.read_text();actual=body(s[s.index(scope):],anchor);assert tok(actual)==tok(want),(file,scope,anchor,actual)
 checks.append(dict(file=str(p),file_sha256=hashlib.sha256(s.encode()).hexdigest(),scope=scope,anchor=anchor,complete_body=actual,tokens_equal=True))
scoped('core/src/slice/iter.rs',"impl<'a, T> ChunksExactMut",'pub(super) const fn new(', '{let rem=slice.len()%chunk_size;let fst_len=slice.len()-rem;let (fst,snd)=unsafe {slice.split_at_mut_unchecked(fst_len)};Self {v:fst,rem:snd,chunk_size,_marker:PhantomData}}')
scoped('core/src/slice/iter.rs',"Iterator for ChunksExactMut",'fn next(', '{unsafe {&mut *self.v}.split_at_mut_checked(self.chunk_size).and_then(|(chunk,rest)| {self.v=rest;Some(chunk)})}')
scoped('core/src/slice/iter.rs',"Iterator for ChunksExactMut",'unsafe fn __iterator_get_unchecked(', '{let start=idx*self.chunk_size;unsafe {from_raw_parts_mut(self.v.as_mut_ptr().add(start),self.chunk_size)}}')
scoped('core/src/iter/adapters/zip.rs','macro_rules! zip_impl_general_defaults','default fn next(', '{let x=self.a.next()?;let y=self.b.next()?;Some((x,y))}')
scoped('core/src/iter/adapters/zip.rs','A: TrustedRandomAccess + Iterator','fn next(', '{if self.index<self.len {let i=self.index;self.index+=1;unsafe {Some((self.a.__iterator_get_unchecked(i),self.b.__iterator_get_unchecked(i)))}} else {None}}')
check('core/src/array/iter.rs','fn next(&mut self)', '{self.unsize_mut().next()}','forward alive index; no mixed front/back path')
check('core/src/array/iter/iter_inner.rs','fn next(&mut self)', '{self.alive.next().map(|idx| {unsafe {self.data.get_unchecked(idx).assume_init_read()}})}','forward alive index increments once; input T=u32 is Copy and has no Drop')
check('core/src/array/iter.rs','unsafe fn __iterator_get_unchecked(', '{let elem_ref=unsafe {self.as_mut_slice().get_unchecked_mut(idx)};unsafe {ptr::read(elem_ref)}}','same indexed u32 for all i<8; random or forward route has same value trace')
check('core/src/mem/manually_drop.rs','pub const fn new(value:', '{ManuallyDrop {value:MaybeDangling::new(value)}}','Wrappers.new')
scoped('core/src/mem/manually_drop.rs','Deref for ManuallyDrop<T>','fn deref(', '{self.value.as_ref()}')
scoped('core/src/mem/manually_drop.rs','DerefMut for ManuallyDrop<T>','fn deref_mut(', '{self.value.as_mut()}')
check('core/src/mem/maybe_dangling.rs','fn as_ref(', '{&self.0}','Wrappers.deref_complete; transparent inner value')
check('core/src/mem/maybe_dangling.rs','fn as_mut(', '{&mut self.0}','Wrappers.deref_mut_complete; restoration retained')
check('core/src/ptr/non_null.rs','pub const fn from_ref(', '{unsafe {NonNull {pointer:r as *const T}}}','PointerConstruct.from_ref_complete')
check('core/src/ptr/non_null.rs','pub const fn from_mut(', '{unsafe {NonNull {pointer:r as *mut T}}}','PointerConstruct.from_mut_complete')
check('core/src/ptr/non_null.rs','pub const fn cast<U>', '{unsafe {NonNull {pointer:self.as_ptr() as *mut U}}}','Pointer.cast_complete')
# Reuse the exact complete copy body expectation from the reviewed writer
# gate, not a freshly generated expected body from the installed source.
gate=(D/'deployed-writer-gate.py').read_text();node=next(x for x in ast.walk(ast.parse(gate)) if isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id=='check' and len(x.args)>2 and isinstance(x.args[1],ast.Constant) and x.args[1].value=='const unsafe fn copy_from_slice_impl<')
check('core/src/slice/mod.rs','const unsafe fn copy_from_slice_impl<',ast.literal_eval(node.args[2]),'V195.chunk_width excludes length failure; Copy.copies_result/full overwrite/frame law')
j=dict(row='V195',evidence_class='structural (K-1 substitute)',checks=checks,laws=['PV_RDB1_V195.complete','PV_RDB1_V195.source_complete','PV_RDB1_V195.chunk_width','PV_RDB1_V195.chunk_count','PV_RDB1_V195.slot_bounds','PV_RDB1_V195.cover','PV_RDB1_V195.disjoint','PV_RDB1_Wrappers.deref_complete','PV_RDB1_Wrappers.deref_mut_complete'],source_dispatch='Both forward and specialized indexed Zip.next routes checked. Fixed32/4 destination and8 u32 limbs; monotone0..7 indexing; no mixed front/back. All4-byte copy lengths match. No zero-chunk or bounds panic reachable.',conservative_changed_panic_nodes='Vec::deref, AtomicPtr construction, CStr conversion and panic attribution belong to conservative panic/formatting envelope; constant nonzero chunk width and proved32-byte/8-word bounds exclude entry. No invocation of these bodies is silently credited as a successful native call.',D188='Native mutable chunk writes are bound directly to snapshot-copy source law. No Aeneas emission of mutable-iterator writes or discarded restoration is credited.',features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3; debug_assertions=false; overflow_checks=false; panic=unwind',native_validation='project-wide/receipt.json:108309 paired arrays observing all32 bytes,raw u32 domain; reused unchanged; finite only',retained_boundary='Original generic raw-carrier op51 value/library intrinsic interpretation; no field reduction. Compiler/binary/side-channel obligations remain; no allocator call introduced.',new_trust_items=[],kani_credit=False)
(D/'v195-deployed-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS V195 complete deployed serializer/copy/iterator/wrapper binding')
