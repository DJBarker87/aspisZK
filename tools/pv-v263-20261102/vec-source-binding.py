"""Pinned std body structural gate. Deliberately no whole-worker binding credit."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((E/'std-vec-source-pins-D572.json').read_text())
for p in pins['files']:assert sha((R/p['path']).read_bytes())==p['sha256'],p['path']
std=E/'inputs/std-1.94.1'
def tokens(s):
 s=re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
 return re.findall(r'"(?:\\.|[^"\\])*"|[A-Za-z_]\w*|\d+|\S',s)
def contains(haystack,needle):
 return any(haystack[i:i+len(needle)]==needle for i in range(len(haystack)-len(needle)+1))
rows=[]
def body(path,signature,expected,steps):
 src=(std/path).read_text();ts=tokens(src);sig=tokens(signature)
 starts=[i for i in range(len(ts)) if ts[i:i+len(sig)]==sig];assert len(starts)==1,(path,signature,starts)
 start=starts[0];op=ts.index('{',start);depth=1;end=op+1
 while depth:
  if ts[end]=='{':depth+=1
  if ts[end]=='}':depth-=1
  end+=1
 got=ts[start:end];assert got==tokens(expected),(path,signature)
 rows.append(dict(path=str((std/path).relative_to(R)),signature=signature,body_token_sha256=sha('\0'.join(got).encode()),exact_body_checked=True,steps=steps))
body('alloc/src/vec/mod.rs','pub fn append(','''pub fn append(&mut self, other: &mut Self) {
 unsafe { self.append_elements(other.as_slice() as _); other.set_len(0); }
}''',[
 ['borrow initialized donor slice','source.values.val; distinct owned vector allocations in source'],
 ['append_elements call','reserved append scalar/copy steps below'],
 ['other.set_len(0)','VectorDrain.drain_source; AppendBinding.stores'],
 ['return Unit with both mutable owners restored','VecSpine.append returns (out,drained); donor destructor follows']])
body('alloc/src/vec/mod.rs','unsafe fn append_elements(','''unsafe fn append_elements(&mut self, other: *const [T]) {
 let count = other.len(); self.reserve(count); let len = self.len();
 unsafe { ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(len), count) };
 self.len += count;
}''',[
 ['count=other.len()','source.values.length'],['reserve(count)','AppendBinding.reserve_no_growth under existing sufficient reservation'],
 ['len=self.len()','out.values.length'],['copy_nonoverlapping to suffix','VectorDrain.drain_values; memory primitive/compiler V370 retained'],
 ['self.len+=count','VectorDrain.drain_length; AppendBinding.length_add_no_wrap']])
body('alloc/src/vec/mod.rs','pub fn reserve(','''pub fn reserve(&mut self, additional: usize) {
 self.buf.reserve(self.len, additional);
}''',[['delegate with current length and added count','unchanged count/length to RawVec.reserve']])
body('alloc/src/raw_vec/mod.rs','pub(crate) fn reserve(','''pub(crate) fn reserve(&mut self, len: usize, additional: usize) {
 unsafe { self.inner.reserve(len, additional, T::LAYOUT) }
}''',[['layout argument','same element layout as both allocated Vec owners'],['delegate','RawVecInner.reserve']])
body('alloc/src/raw_vec/mod.rs','unsafe fn reserve(','''unsafe fn reserve(&mut self, len: usize, additional: usize, elem_layout: Layout) {
 #[cold] unsafe fn do_reserve_and_handle<A: Allocator>(slf: &mut RawVecInner<A>,len: usize,additional: usize,elem_layout: Layout,) {
 if let Err(err) = unsafe { slf.grow_amortized(len, additional, elem_layout) } { handle_error(err); }
 }
 if self.needs_to_grow(len, additional, elem_layout) {
 unsafe { do_reserve_and_handle(self, len, additional, elem_layout); }
 }
}''',[['needs_to_grow guard','AppendBinding.reserve_no_growth'],['grow_amortized/error handler branch','unreachable ONLY under the room bound; not erased for arbitrary calls'],['return on no growth','no allocator request or native failure at this method']])
body('alloc/src/raw_vec/mod.rs','const fn needs_to_grow(','''const fn needs_to_grow(&self, len: usize, additional: usize, elem_layout: Layout) -> bool {
 additional > self.capacity(elem_layout.size()).wrapping_sub(len)
}''',[['capacity minus initialized length','AppendBinding.no_sub_wrap; Buffer.fits and Buffer.bounded'],['compare added count','room implies guard false'],['ZST capacity','lower reservation bound suffices; native validation includes ZST']])
collect=(std/'alloc/src/vec/spec_from_iter_nested.rs').read_text()
trusted='''impl<T, I> SpecFromIterNested<T, I> for Vec<T> where I: TrustedLen<Item = T>, {
 fn from_iter(iterator: I) -> Self {
 let mut vector = match iterator.size_hint() { (_, Some(upper)) => Vec::with_capacity(upper), _ => panic!("capacity overflow"), };
 vector.spec_extend(iterator); vector
 }
}'''
assert contains(tokens(collect),tokens(trusted))
map_src=(std/'core/src/iter/adapters/map.rs').read_text();range_src=(std/'core/src/iter/range.rs').read_text()
assert 'unsafe impl<A: TrustedStep> TrustedLen for ops::Range<A> {}' in range_src
assert 'SourceIter' not in range_src and 'InPlaceIterable' not in range_src
assert contains(tokens(map_src),tokens('unsafe impl<B,I,F> TrustedLen for Map<I,F> where I: TrustedLen,F:FnMut(I::Item)->B,{}'))
assert contains(tokens(range_src),tokens('''macro_rules! unsafe_impl_trusted_step {
 ($($type:ty)*) => {$(
 #[unstable(feature = "trusted_step", issue = "85731")]
 unsafe impl TrustedStep for $type {}
 )*};
}'''))
assert contains(tokens(range_src),tokens('unsafe_impl_trusted_step![AsciiChar char i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize Ipv4Addr Ipv6Addr];'))
models={n:sha((R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_V263_'+n+'.lean')).read_bytes()) for n in ['VectorDrain','VecSpine','AppendBinding','CollectBinding','Captures','BufferLoop','BufferFamily']}
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
for n in ['VectorDrain','VecSpine','AppendBinding','CollectBinding','Captures','BufferLoop','BufferFamily']:
 assert accepted['R1Z.PV_V263_'+n]['source_sha256']==models[n]
receipt=json.loads((E/'N90123-receipt.json').read_text());assert receipt['exit']==0 and receipt['admission_allowed']
out=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),evidence_class='structural source argument for reserved append control/stores; NOT a complete worker/native refinement',std_toolchain=pins['toolchain'],exact_std_bodies=rows,collect_selection=dict(range_usize='TrustedStep/TrustedLen',map='preserves TrustedLen',in_place_collect='Range has no SourceIter or InPlaceIterable',selected='SpecFromIterNested TrustedLen',capacity='upper bound before any next/callback',store='extend_trusted writes prefix and SetLenOnDrop publishes length; guard/lifetime binding still required'),models=models,native_validation=dict(attempt='N90123',checks=221,credit='finite validation only; not callback-source success'),remaining=['Substitute BufferFamily and reservation-preserving drains into the outer Vec spine; its Vec.new donor currently forgets capacity. Complete physical heap/reservation/deallocation relation','VecSpine lifecycle hooks do not yet supply the native std/thread/TLS/handle/closure/drop codec','CollectBinding.stores is a full-outcome logical refinement; native SetLenOnDrop and collect heap/lifetime binding remains','Native realisation of join-late scheduling and EVH codec','Actual captured callback source laws, actual opsNative installation and reached successful capture'],complete_worker_binding=False,op257_installed=False,actual_reached_success=False,nonempty_P=False)
(E/'vec-source-binding-D572.json').write_text(json.dumps(out,indent=2)+'\n')
print('Pinned std:',len(rows),'complete reserved-append bodies checked; TrustedLen selection checked; whole binding INCOMPLETE')
