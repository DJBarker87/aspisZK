"""Complete pinned IntoIter bodies and payload-indirection source checks."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';STD=E/'inputs/std-1.94.1'
sha=lambda b:hashlib.sha256(b).hexdigest()
for manifest in ['std-vec-source-pins-D572.json','handle-std-source-pins.json']:
 for pin in json.loads((E/manifest).read_text())['files']:
  assert sha((R/pin['path']).read_bytes())==pin['sha256'],pin['path']
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
 q=R/path;ts=tokens(q.read_text());want=tokens(expected)
 hits=[i for i in range(len(ts)) if ts[i:i+len(want)]==want]
 assert len(hits)==1,(path,len(hits),expected[:80])
 rows.append(dict(path=path,full_body=expected,token_sha256=sha('\0'.join(want).encode()),complete_body_checked=True,correspondence=correspondence,remaining=remaining))
vec='evidence/pv-v263-20261102/inputs/std-1.94.1/alloc/src/vec/'
std='evidence/pv-v263-20261102/inputs/std-1.94.1/'
body(vec+'mod.rs','''fn into_iter(self) -> Self::IntoIter {
 unsafe {
 let me = ManuallyDrop::new(self);
 let alloc = ManuallyDrop::new(ptr::read(me.allocator()));
 let buf = me.buf.non_null(); let begin = buf.as_ptr();
 let end = if T::IS_ZST {begin.wrapping_byte_add(me.len())}
 else {begin.add(me.len()) as *const T};
 let cap = me.buf.capacity();
 IntoIter { buf, phantom: PhantomData, cap, alloc, ptr: buf, end }
 }
}''',['OwnedIterator.intoIter transfers remaining values and original allocation without a Vec destructor',
 'pointer begins at original base; endPointer uses byte wrapping for ZST and element stride for non-ZST'],
 ['native allocator ownership/provenance and non-ZST address validity; phantom and Global/System allocator lowering'])
body(vec+'into_iter.rs','''fn next(&mut self) -> Option<T> {
 let ptr = if T::IS_ZST {
 if self.ptr.as_ptr() == self.end as *mut T {return None;}
 self.end = self.end.wrapping_byte_sub(1); self.ptr
 } else {
 if self.ptr == non_null!(self.end, T) {return None;}
 let old = self.ptr; self.ptr = unsafe {old.add(1)}; old
 };
 Some(unsafe {ptr.read()})
}''',['OwnedIterator.next/moves: return exactly next value, shorten remaining initialized sequence, advance consumed count',
 'cursor advances by element size; ZST cursor stays aligned and remaining count decreases',
 'exhausted retains original allocation and returns None without any resource/runtime method request'],
 ['typed native read and pointer/end encoding, including modulo ZST encoding and non-ZST allocation validity'])
body(vec+'into_iter.rs','''fn drop(&mut self) {
 struct DropGuard<'a, T, A: Allocator>(&'a mut IntoIter<T, A>);
 impl<T, A: Allocator> Drop for DropGuard<'_, T, A> {
 fn drop(&mut self) {
 unsafe {
 let alloc = ManuallyDrop::take(&mut self.0.alloc);
 let _ = RawVec::from_nonnull_in(self.0.buf, self.0.cap, alloc);
 }
 }
 }
 let guard = DropGuard(self);
 unsafe {ptr::drop_in_place(guard.0.as_raw_mut_slice());}
}''',['OwnedIterator.drop: drop remaining initialized elements, then guard deallocates original buf/cap',
 'exhausted_drop: no element destructor; exact deallocator post-state/events; panic mapped to abort under profile',
 'finalize .abort does not run an invented unwind guard after an element panic/abort'],
 ['actual handle/caught-result/closure element drop glue and Global/System release codec; memory provenance'])
body(std+'alloc/src/raw_vec/mod.rs','''pub(crate) unsafe fn from_nonnull_in(ptr: NonNull<T>, capacity: usize, alloc: A) -> Self {
 unsafe {
 let ptr = ptr.cast(); let capacity = new_cap::<T>(capacity);
 Self {inner: RawVecInner::from_nonnull_in(ptr, capacity, alloc), _marker: PhantomData}
 }
}''',['original buf, not current cursor, is reconstructed for drop',
 'ZST capacity ignored by new_cap and never deallocated; non-ZST original raw capacity retained'],
 ['new_cap, RawVec constructor and native drop glue/codegen boundary'])
body(std+'std/src/thread/lifecycle.rs', '''pub(super) struct JoinInner<'scope, T> {
 native: imp::Thread, thread: Thread, packet: Arc<Packet<'scope, T>>,
}''',['returned payload T occurs only behind Arc<Packet<T>> in the handle'],
 ['compiler layout law V370; complete join lifecycle remains open'])
body(std+'std/src/thread/lifecycle.rs', '''struct Packet<'scope, T> {
 scope: Option<Arc<ScopeData>>, result: UnsafeCell<Option<Result<T>>>,
 _marker: PhantomData<Option<&'scope ScopeData>>,
}''',['Packet is sized for every reached T; its payload-dependent layout affects the separate Arc allocation, not inline handle storage'],
 ['Packet allocation, result transport and Arc drop are still V400-257-lowering obligations'])
body('evidence/pv-v263-20261102/inputs/std-1.94.1-scoped.rs',
 '''pub struct ScopedJoinHandle<'scope, T>(JoinInner<'scope, T>);''',
 ['scoped handle wraps JoinInner directly'],['native layout/monomorphisation boundary V370'])
body(std+'std/src/thread/thread.rs', '''pub struct Thread {inner: Pin<Arc<Inner, System>>,}''',
 ['Thread uses System-allocated Arc, distinct from the Global handle Vec allocation'],
 ['System allocator and Thread/Inner lifecycle; cannot count all thread allocations from Vec capacities'])
body(std+'std/src/sys/thread/unix.rs', '''pub struct Thread {id: libc::pthread_t,}''',
 ['Unix native handle holds pthread_t'],['target/libc ABI and compiler layout boundary V370'])
if '--bodies-only' in sys.argv:
 print('nine complete iterator/handle definitions checked; whole worker binding not checked')
 raise SystemExit(0)
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
models={}
for m in ['OwnedIterator','OwnedForks']:
 q=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_V263_'+m+'.lean');h=sha(q.read_bytes())
 assert accepted['R1Z.PV_V263_'+m]['source_sha256']==h,m;models[m]=h
out=dict(script_sha256=sha(Path(__file__).read_bytes()),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 evidence_class='local structural iterator/handle indirection argument; not machine proof or complete worker binding',
 rows=rows,models=models,payload_indirection='Source establishes separate Packet allocation; representative handle size24/align8 measured by N90125. This is not an actual callback execution or a standalone machine proof of arbitrary monomorphisation layout.',
 source_binding_complete=False,actual_op257_installed=False,actual_reached_success=False,
 remaining=['native byte heap/provenance, typed moves, allocation validity/disjointness',
 'actual element/closure/packet/Arc/Thread drop and join/scope/TLS effects',
 'replace abstract lifecycle/method hooks in whole spine with these owned components',
 'EVH lowering, native schedule, actual opsNative stateful capture, actual callbacks and Nonempty P'])
(E/'iterator-source-binding-continuation.json').write_text(json.dumps(out,indent=2)+'\n')
print('nine complete iterator/handle definitions plus two accepted model sources; whole worker binding OPEN')
