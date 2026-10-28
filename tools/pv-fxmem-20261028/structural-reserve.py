from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
src=(R/'tools/pv-fxmem-20261028/structural-drop.py').read_text();exec(src[src.index('def clean('):src.index('expected=')])
rows=json.loads((E/'RESERVE-SOURCE.json').read_text())
expected={
'pub fn try_reserve_exact(':'{self.buf.try_reserve_exact(self.len, additional)}',
'pub(crate) fn try_reserve_exact(':'{unsafe {self.inner.try_reserve_exact(len, additional, T::LAYOUT)}}',
'unsafe fn try_reserve_exact(':'{if self.needs_to_grow(len, additional, elem_layout) {unsafe {self.grow_exact(len, additional, elem_layout)?;}}unsafe {hint::assert_unchecked(!self.needs_to_grow(len, additional, elem_layout));}Ok(())}',
'unsafe fn grow_exact(':'{if elem_layout.size() == 0 {return Err(CapacityOverflow.into());}let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;let ptr = unsafe {self.finish_grow(cap, elem_layout)?};unsafe {self.set_ptr_and_cap(ptr, cap)};Ok(())}',
'fn needs_to_grow(':'{additional > self.capacity(elem_layout.size()).wrapping_sub(len)}',
'fn finish_grow(':'{let new_layout = layout_array(cap, elem_layout)?;let memory = if let Some((ptr, old_layout)) = unsafe {self.current_memory(elem_layout)} {debug_assert!(old_layout.align() == new_layout.align());unsafe {hint::assert_unchecked(old_layout.align() == new_layout.align());self.alloc.grow(ptr, old_layout, new_layout)}} else {self.alloc.allocate(new_layout)};match memory {Ok(memory) => Ok(memory),Err(_) => Err(AllocError {layout: new_layout, non_exhaustive: ()}.into()),}}',
'unsafe fn set_ptr_and_cap(':'{self.ptr = Unique::from(ptr.cast());self.cap = unsafe {Cap::new_unchecked(cap)};}',
'fn alloc_impl_runtime(':'{match layout.size() {0 => Ok(layout.dangling_ptr().cast_slice(0)),size => unsafe {let raw_ptr = if zeroed {alloc_zeroed(layout)} else {alloc(layout)};let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;Ok(ptr.cast_slice(size))},}}',
'fn layout_array(':'{debug_assert!(elem_layout.size() == elem_layout.pad_to_align().size());elem_layout.repeat_packed(cap).map_err(const |_| CapacityOverflow.into())}',
'fn grow_impl_runtime(':'{debug_assert!(new_layout.size() >= old_layout.size(),"`new_layout.size()` must be greater than or equal to `old_layout.size()`");match old_layout.size() {0 => self.alloc_impl(new_layout, zeroed),old_size if old_layout.align() == new_layout.align() => unsafe {let new_size = new_layout.size();hint::assert_unchecked(new_size >= old_layout.size());let raw_ptr = realloc_nonnull(ptr, old_layout, new_size);let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;if zeroed {raw_ptr.add(old_size).write_bytes(0,new_size - old_size);}Ok(ptr.cast_slice(new_size))},old_size => unsafe {let new_ptr = self.alloc_impl(new_layout, zeroed)?;ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), old_size);self.deallocate(ptr, old_layout);Ok(new_ptr)},}}'}
assert len(rows)==len(expected)
for x in rows:
 assert tokens(x['body'])==tokens(expected[x['anchor']]),x
 x['complete_tokens_match']=True
f=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';s=f.read_text();calls=[]
for i,line in enumerate(s.splitlines(),1):
 if 'alloc.vec.Vec.try_reserve_exact' in line:calls.append(dict(line=i,context='\n'.join(s.splitlines()[i-2:i+3])))
assert len(calls)==4
j=dict(evidence_class='structural (K-1 substitute)',checks=rows,emitted_calls=calls,
 emitted_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),
 scope='Four emitted calls, each on Vec::new: Vec<[u8;32]>, Vec<Vec<T>> in generic encode, Vec<Word>, Vec<Vec<M31>>. The reference also handles valid general buffers and the zero-size overflow path using effective Vec::capacity.',
 source_order='needs_to_grow; zero-size overflow; checked len+additional; checked repeated layout; allocate or same-align Global grow; map null/error to AllocError with requested layout; install pointer/capacity only after success; never change len or run element Drop.',
 allocation_world='The raw allocator step is explicit and may change its private state even when returning null. Returning null preserves buffer/header/data. Counts and ordered allocator requests are retained. Successful realloc moves the old allocation bytes in memoryAfter, including uninitialized slots, and invalidates old allocation identity if moved.',
 differences='Reference combines three ordered pure rejection tests into a disjunction after the no-growth test; source_reference proves harmlessness. Nat subtraction corresponds to wrapping_sub only for valid len<=capacity; same-type layouts share alignment, so Global grow fallback for changed alignment is unreachable. New allocations are nonzero sized. zeroed=false, so no zero-fill branch is taken.',
 retained='No theorem about libc internals, arbitrary allocator nonreturn, deployed binary, or side-channel equivalence. These remain P and are not new T fields. Finite native validation recorded separately.')
layout=json.loads((E/'LAYOUT-SOURCE.json').read_text())
layout_expected={
 'pub const fn repeat_packed(':'{if let Some(size) = self.size.checked_mul(n) {Layout::from_size_alignment(size, self.align)} else {Err(LayoutError)}}',
 'fn max_size_for_alignment(':'{unsafe {unchecked_sub(isize::MAX as usize + 1, alignment.as_usize())}}',
 'const fn is_size_alignment_valid(':'{size <= Self::max_size_for_alignment(alignment)}',
 'const fn from_size_alignment(':'{if Layout::is_size_alignment_valid(size, alignment) {Ok(Layout {size, align: alignment})} else {Err(LayoutError)}}'}
assert len(layout['bodies'])==len(layout_expected)
for x in layout['bodies']:
 assert tokens(x['body'])==tokens(layout_expected[x['anchor']]),x
 x['complete_tokens_match']=True
j['layout']=layout
j['symbolic_differences']='PV_FXM_ReserveLayout.aligned_limit proves padded alignment guard equivalence; product_error combines checked-mul overflow with the smaller byte bound; wrapped_available proves valid-buffer wrapping subtraction equals Nat subtraction; same_alignment excludes Global changed-alignment fallback.'
j['physical_boundary']='World.memory is a logical allocation snapshot, whose validity is governed by live. PV_FXM_Physical retains actual raw bytes and arbitrary allocator-accessible external effects inside Runtime. No preservation of physical freed storage is claimed.'
(E/'STRUCTURAL-RESERVE-GATE.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS 10 complete pinned bodies and 4 emitted fresh-vector call sites')
