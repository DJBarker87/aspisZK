"""Focused pinned std store/drop correspondence gate; no whole-worker credit."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';STD=E/'inputs/std-1.94.1'
sha=lambda b:hashlib.sha256(b).hexdigest()
for pin in json.loads((E/'std-vec-source-pins-D572.json').read_text())['files']:
 assert sha((R/pin['path']).read_bytes())==pin['sha256'],pin['path']
# Tokenise strings before comments, including nested Rust block comments.
def tokens(s):
 out=[];i=0
 while i<len(s):
  if s[i].isspace():i+=1;continue
  if s.startswith('//',i):
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  if s.startswith('/*',i):
   depth=1;i+=2
   while depth:
    assert i<len(s),'unterminated comment'
    if s.startswith('/*',i):depth+=1;i+=2
    elif s.startswith('*/',i):depth-=1;i+=2
    else:i+=1
   continue
  if s[i]=='"':
   j=i+1
   while j<len(s):
    if s[j]=='\\':j+=2
    elif s[j]=='"':j+=1;break
    else:j+=1
   out.append(s[i:j]);i=j;continue
  m=re.match(r'[A-Za-z_]\w*|\d+',s[i:])
  if m:out.append(m[0]);i+=len(m[0])
  else:out.append(s[i]);i+=1
 return out
rows=[]
def body(path,expected,correspondence,remaining):
 ts=tokens((STD/path).read_text());want=tokens(expected)
 hits=[i for i in range(len(ts)) if ts[i:i+len(want)]==want]
 assert len(hits)==1,(path,len(hits),expected[:80])
 rows.append(dict(path=str((STD/path).relative_to(R)),full_body=expected,
  token_sha256=sha('\0'.join(want).encode()),complete_body_checked=True,
  correspondence=correspondence,remaining=remaining))
body('alloc/src/vec/mod.rs','''pub fn push(&mut self, value: T) { let _ = self.push_mut(value); }''',
 ['delegate push_mut; returned reference unused'],[])
body('alloc/src/vec/mod.rs','''pub fn push_mut(&mut self, value: T) -> &mut T {
 let len = self.len;
 if len == self.buf.capacity() { self.buf.grow_one(); }
 unsafe { let end = self.as_mut_ptr().add(len); ptr::write(end, value);
 self.len = len + 1; &mut *end }
}''',
 ['OwnedPush.no_growth proves guard false ONLY on reserved domain',
  'OwnedPush.stores writes value, increments initialized length, retains allocation/reservation',
  'returned borrow discarded by Vec.push; no mutable restoration is discarded by an extraction'],
 ['grow_one for handles remains unbound; memory primitive/codegen boundary V370'])
body('alloc/src/vec/mod.rs','''fn extend_trusted(&mut self, iterator: impl iter::TrustedLen<Item = T>) {
 let (low, high) = iterator.size_hint();
 if let Some(additional) = high {
 debug_assert_eq!(low, additional, "TrustedLen iterator's size hint is not exact: {:?}", (low, high));
 self.reserve(additional);
 unsafe { let ptr = self.as_mut_ptr(); let mut local_len = SetLenOnDrop::new(&mut self.len);
 iterator.for_each(move |element| {
 ptr::write(ptr.add(local_len.current_len()), element); local_len.increment_len(1);
 }); }
 } else { panic!("capacity overflow"); }
}''',
 ['Range/Map TrustedLen selection and exact upper bound checked by D572 gate',
  'release debug_assertions=false: debug formatting not reached',
  'initial from_iter capacity covers reserve(additional); no second allocation',
  'TrustedStores.beginCollect/write: local initialized prefix and unchanged borrowed published length',
  'TrustedStores.drop_publishes: guard publishes initialized length on normal exit',
  'TrustedStores.erasure preserves full outcomes/events/post-world to retained collector'],
 ['iterator/closure native lifecycle; runtime fault diagnostics and allocator binding; None branch unreachable for reached ranges'])
body('alloc/src/vec/set_len_on_drop.rs','''pub(super) fn new(len: &\'a mut usize) -> Self {
 SetLenOnDrop { local_len: *len, len }
}''',['TrustedStores.beginCollect copies initial length and retains borrowed field'],[])
body('alloc/src/vec/set_len_on_drop.rs','''pub(super) fn increment_len(&mut self, increment: usize) {
 self.local_len += increment;
}''',['TrustedStores.write_order specializes increment=1; room bounds arithmetic by Usize.max'],[])
body('alloc/src/vec/set_len_on_drop.rs','''pub(super) fn current_len(&self) -> usize { self.local_len }''',
 ['TrustedStores.Frame.initialized.values.length is local_len'],[])
body('alloc/src/vec/set_len_on_drop.rs','''fn drop(&mut self) { *self.len = self.local_len; }''',
 ['TrustedStores.publish/drop_publishes; panic=abort does not run an unwind destructor'],[])
body('alloc/src/raw_vec/mod.rs','''const fn capacity(&self, elem_size: usize) -> usize {
 if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }
}''', ['OwnedDrain.capacity: exact capacity derived from raw metadata including ZST'],[])
body('alloc/src/raw_vec/mod.rs','''unsafe fn deallocate(&mut self, elem_layout: Layout) {
 if let Some((ptr, layout)) = unsafe { self.current_memory(elem_layout) } {
 unsafe { self.alloc.deallocate(ptr, layout); }
 }
}''', ['OwnedDrain.release: no request on None; exact retained allocation on Some'],
 ['Global/System deallocation and native heap/event interpretation'])
body('alloc/src/raw_vec/mod.rs','''const unsafe fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)> {
 if elem_layout.size() == 0 || self.cap.as_inner() == 0 { None } else {
 unsafe { let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
 let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
 Some((self.ptr.into(), layout)) }
 }
}''',
 ['OwnedDrain.release: None on ZST/raw capacity zero; otherwise ORIGINAL pointer, size*rawCapacity, alignment',
  'OwnedDrain.ownership/empty_donor_release: draining to zero preserves the original allocation and release layout'],
 ['native allocation validity/disjointness and size*rawCapacity<=isize::MAX; release event codec'])
body('alloc/src/raw_vec/mod.rs','''fn drop(&mut self) { unsafe { self.inner.deallocate(T::LAYOUT) } }''',
 ['RawVec drop deallocates the retained allocation, independent of initialized length'],
 ['deallocate/Global implementation and native release event codec'])
body('alloc/src/vec/mod.rs','''fn drop(&mut self) {
 unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len)) }
}''',
 ['OwnedDrain.ownership: donor has zero initialized elements, hence no element destructor',
  'implicit field drop then calls RawVec drop with retained allocation'],
 ['drop-glue/compiler boundary V370; IntoIter and nonempty failure cleanup remain separate'])
if '--bodies-only' in sys.argv:
 print('Pinned complete std bodies:',len(rows),'token checks passed; proof correspondence NOT checked')
 raise SystemExit(0)
modules=['RetainedMethods','RetainedSpine','RetainedFacts','TrustedStores','OwnedDrain','OwnedPush','RetainedErase','CounterBounds']
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
models={}
for m in modules:
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_V263_'+m+'.lean')
 h=sha(p.read_bytes());assert accepted['R1Z.PV_V263_'+m]['source_sha256']==h,m
 models[m]=h
out=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 evidence_class='structural reserved-store/drop argument; not a complete native worker association',
 std_toolchain='1.94.1',profile=dict(release=True,panic='abort',debug_assertions=False,overflow_checks=False),
 bodies=rows,models=models,source_binding_complete=False,op257_installed=False,reached_success=False,
 remaining=['Native allocation ownership/lifetimes and concrete layouts in actual world',
 'Growing handle push, thread/TLS/scope/join/native schedule/EVH codec',
 'Actual opsNative and NativeControl stateful installation',
 'Discharge actual callback success then actual capture and Nonempty P'])
(E/'store-source-binding-D575.json').write_text(json.dumps(out,indent=2)+'\n')
print('Pinned complete std bodies:',len(rows),'reserved stores/drop correspondence checked; whole binding INCOMPLETE')
