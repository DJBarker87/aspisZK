"""Check old/deployed std bodies for the newly proved transport families.

This does not install a concrete allocator or infer a complete call cone from
the conservative inventory. Remaining source/instantiation gaps stay explicit.
"""
from pathlib import Path
import json,lzma,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
files=json.loads(lzma.decompress((D/'prior-sources.json.xz').read_bytes()))['files']
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'"(?:[^"\\]|\\.)*"|::|=>|\w+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return s[a:i+1]
 raise ValueError(needle)
def source(key):
 r=files[key];raw=r['text'].encode();assert hashlib.sha256(raw).hexdigest()==r['sha256']
 if key.startswith('deployed/'):
  assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256'],key
 return r['text']
checks=[]
def pair(label,oldkey,newkey,oldneedle,newneedle,expectedold,expectednew,law,domain):
 a=body(source(oldkey),oldneedle);b=body(source(newkey),newneedle)
 assert tokens(a)==tokens(expectedold),(label,'historical body',a)
 assert tokens(b)==tokens(expectednew),(label,'deployed body',b)
 checks.append(dict(family=label,old_key=oldkey,deployed_key=newkey,old_file_sha256=files[oldkey]['sha256'],deployed_file_sha256=files[newkey]['sha256'],old_body=a,deployed_body=b,exact_expected_bodies=True,proof=law,domain=domain))
ol='evidence/library/core/src/alloc/layout.rs';nl='deployed/library/core/src/alloc/layout.rs'
pair('Layout.from_size_alignment',ol,nl,'pub const fn from_size_alignment(','const fn from_size_alignment(',
 '{if Layout::is_size_alignment_valid(size,alignment){Ok(Layout{size,align:alignment})}else{Err(LayoutError)}}',
 '{if size>Self::max_size_for_align(align){return Err(LayoutError);}Ok(Layout{size,align})}',
 'LayoutGuards.from_size_alignment/complete_effect; Alignment.allocator_argument','same valid alignment word; LayoutError retained as Err value')
pair('Layout.is_size_align_valid',ol,nl,'const fn is_size_align_valid(','const fn is_size_align_valid(',
 '{let Some(alignment)=Alignment::new(align)else{return false};Self::is_size_alignment_valid(size,alignment)}',
 '{let Some(align)=Alignment::new(align)else{return false};if size>Self::max_size_for_align(align){return false;}true}',
 'LayoutGuards.is_size_align_valid','all input sizes and Alignment::new outcomes, including invalid alignment')
pair('Layout.repeat',ol,nl,'pub const fn repeat(','pub const fn repeat(','''{
 let padded=self.pad_to_align();let Ok(result)=(if let Some(k)=n.checked_sub(1){
 let Ok(repeated)=padded.repeat_packed(k)else{return Err(LayoutError);};repeated.extend_packed(*self)
 }else{debug_assert!(n==0);self.repeat_packed(0)})else{return Err(LayoutError);};Ok((result,padded.size()))}''',
 '{let padded=self.pad_to_align();if let Ok(repeated)=padded.repeat_packed(n){Ok((repeated,padded.size()))}else{Err(LayoutError)}}',
 'LayoutRepeat.padded_complete/padded_effect; LayoutGeneral.before_success/after_success/before_after_size',
 'equality on already-padded real-type layouts; explicit restated before/after law on unpadded layouts')
orv='evidence/library/alloc/src/raw_vec/mod.rs';nrv='deployed/library/alloc/src/raw_vec/mod.rs'
pair('layout_array',orv,nrv,'const fn layout_array(','const fn layout_array(',
 '{debug_assert!(elem_layout.size()==elem_layout.pad_to_align().size());elem_layout.repeat_packed(cap).map_err(const |_|CapacityOverflow.into())}',
 '{match elem_layout.repeat(cap){Ok((layout,_pad))=>Ok(layout),Err(_)=>Err(CapacityOverflow.into()),}}',
 'LayoutRepeat.layout_array/checked_mul_layout','real-type padded layout; CapacityOverflow mapping and allocator-world frame retained')
pair('RawVecInner.new_in',orv,nrv,'const fn new_in(alloc: A, align: Alignment)','const fn new_in(alloc: A, align: Alignment)',
 '{let ptr=Unique::from_non_null(NonNull::without_provenance(align.as_nonzero_usize()));Self{ptr,cap:ZERO_CAP,alloc}}',
 '{let ptr=Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()));Self{ptr,cap:ZERO_CAP,alloc}}',
 'RawVec.new_in_complete/new_in_no_allocation; Alignment.nonzero_accessor_complete','valid alignment; no allocation call, cap0, allocator moved into unchanged owner')
oa='evidence/library/core/src/mem/alignment.rs';na='deployed/library/core/src/ptr/alignment.rs'
for k in [oa,na]:
 s=source(k);marker=s.index('#[cfg(target_pointer_width = "64")]');enum=body(s[marker:],'enum AlignmentEnum')
 assert tokens(enum)==tokens('{'+','.join(f'_Align1Shl{i}=1<<{i}' for i in range(64))+',}')
 assert '#[repr(usize)]' in s[marker:s.index('enum AlignmentEnum',marker)]
 assert '#[repr(transparent)]' in s[:s.index('pub struct Alignment')]
checks.append(dict(family='Alignment representation',old_key=oa,deployed_key=na,exact64discriminants=True,representation='transparent wrapper over repr(usize) enum',proof='Alignment.positive/within_half_word/allocator_argument'))
pair('Alignment nonzero accessor',oa,na,'pub const fn as_nonzero_usize(','pub const fn as_nonzero(',
 '{unsafe{mem::transmute::<Alignment,NonZero<usize>>(self)}}',
 '{unsafe{mem::transmute::<Alignment,NonZero<usize>>(self)}}',
 'Alignment.nonzero_accessor_complete','the same 64-bit discriminant is exposed; no pointer provenance is invented')
oat='evidence/library/core/src/sync/atomic.rs';nat='deployed/library/core/src/sync/atomic.rs'
old=source(oat);new=source(nat);old=old[old.index('impl<T> AtomicPtr<T>'):];new=new[new.index('impl<T> AtomicPtr<T>'):]
for name,needle,eo,en,law in [
 ('AtomicPtr.new','pub const fn new(', '{unsafe{transmute(p)}}','{AtomicPtr{p:UnsafeCell::new(p)}}','Atomic.new_complete'),
 ('AtomicPtr.load','pub fn load(', '{unsafe{atomic_load(self.as_ptr(),order)}}','{unsafe{atomic_load(self.p.get(),order)}}','Atomic.load_complete/new_then_load'),
 ('AtomicPtr.as_ptr','pub const fn as_ptr(', '{self.v.get().cast()}','{self.p.get()}','PointerBridge.cast_complete; Atomic.load_complete')]:
 a=body(old,needle);b=body(new,needle);assert tokens(a)==tokens(eo),(name,a);assert tokens(b)==tokens(en),(name,b)
 checks.append(dict(family=name,old_body=a,deployed_body=b,proof=law,domain='thin atomic pointer word, transparent cell representation; identical underlying atomic hook/order/effects'))
ov='evidence/library/alloc/src/vec/mod.rs';nv='deployed/library/alloc/src/vec/mod.rs'
a=body(source(ov),'pub const fn as_mut_slice(');b=body(source(nv),'pub const fn as_mut_slice(')
assert tokens(a)==tokens(b)
checks.append(dict(family='Vec.as_mut_slice',old_body=a,deployed_body=b,body_tokens_identical=True,proof='VecBorrow.complete_return/every_write/roundtrip/no_spare_exposure',scope='Copy-element families; native slice metadata and restoration relationship must be instantiated per row'))
a=body(source(ov),'pub fn truncate(');b=body(source(nv),'pub fn truncate(')
oldexpr='self.as_mut_ptr().add(len).cast_slice(remaining_len)'
newexpr='ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len),remaining_len)'
assert ''.join(tokens(oldexpr)) in ''.join(tokens(a))
assert ''.join(tokens(newexpr)) in ''.join(tokens(b))
assert ''.join(tokens(a)).replace(''.join(tokens(oldexpr)),'PTR_SLICE')==''.join(tokens(b)).replace(''.join(tokens(newexpr)),'PTR_SLICE')
checks.append(dict(family='Vec.truncate',old_body=a,deployed_body=b,exact_only_difference='raw-slice constructor spelling',proof='Truncate.complete/reduced_before_drop/no_drop_when_extending',effects='length reduced before destructor; destructor errors and world evidence preserved'))
og='evidence/library/alloc/src/alloc.rs';ng='deployed/library/alloc/src/alloc.rs'
pair('Global.alloc_impl_runtime',og,ng,'fn alloc_impl_runtime(','fn alloc_impl_runtime(','''{
 match layout.size(){0=>Ok(layout.dangling_ptr().cast_slice(0)),size=>unsafe{
 let raw_ptr=if zeroed{alloc_zeroed(layout)}else{alloc(layout)};
 let ptr=NonNull::new(raw_ptr).ok_or(AllocError)?;Ok(ptr.cast_slice(size))},}}''',
 '''{match layout.size(){0=>Ok(NonNull::slice_from_raw_parts(layout.dangling(),0)),size=>unsafe{
 let raw_ptr=if zeroed{alloc_zeroed(layout)}else{alloc(layout)};
 let ptr=NonNull::new(raw_ptr).ok_or(AllocError)?;Ok(NonNull::slice_from_raw_parts(ptr,size))},}}''',
 'GlobalAlloc.runtime_complete/zero_no_allocator_call/null_is_allocation_error; ConstructorEffects.slice_complete',
 'same allocator hooks and error worlds; fresh-memory semantics of the concrete hook still require resource-family association')
for name,hook in [('alloc','__rust_alloc'),('alloc_zeroed','__rust_alloc_zeroed')]:
 pair('Global.'+name,og,ng,'pub unsafe fn '+name+'(','pub unsafe fn '+name+'(',
  '{unsafe{__rust_no_alloc_shim_is_unstable_v2();'+hook+'(layout.size(),layout.alignment())}}',
  '{unsafe{__rust_no_alloc_shim_is_unstable_v2();'+hook+'(layout.size(),layout.align())}}',
  'GlobalAlloc.allocate_complete; Alignment.allocator_argument',
  'word encoding of alignment and all argument positions/call order preserved; allocator primitive not replaced')
out=dict(checks=checks,toolchain='rustc1.94.1',profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',
 domains='transport families only; no assumption added to capped trust record',
 pending=['Box::new intrinsic lowering to allocation+initialization','concrete allocator freshness/prefix guarantee and resource-family association','per-row concrete call/instantiation cone and complete project checker where still missing'],
 association_correction='The old V258 RawVec<T,A>::new_in classification pointed at RawVecInner<A>::new_in. The Inner theorem is not promoted to the typed wrapper without its own binding.',
 unpadded_difference='LayoutGeneral restates the true difference; native probe confirms before size1 vs deployed size8 for Layout(1,8). No assigned real-type padded-layout row is refuted.',restored_rows=[])
(D/'stdlib-transports.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS exact std constructor, alignment, Layout, atomic and Vec transport-family source checks; concrete allocator/Box associations remain explicit')
