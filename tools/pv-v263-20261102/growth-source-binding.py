"""Pinned complete Rust 1.94.1 growth bodies; local structural binding only."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';STD=E/'inputs/std-1.94.1'
sha=lambda b:hashlib.sha256(b).hexdigest()
for pin in json.loads((E/'std-vec-source-pins-D572.json').read_text())['files']:
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
def body(expected,correspondence,remaining):
 path=STD/'alloc/src/raw_vec/mod.rs';ts=tokens(path.read_text());want=tokens(expected)
 hits=[i for i in range(len(ts)) if ts[i:i+len(want)]==want]
 assert len(hits)==1,(len(hits),expected[:80])
 rows.append(dict(path=str(path.relative_to(R)),full_body=expected,token_sha256=sha('\0'.join(want).encode()),complete_body_checked=True,correspondence=correspondence,remaining=remaining))
body('''const fn min_non_zero_cap(size: usize) -> usize {
 if size == 1 { 8 } else if size <= 1024 { 4 } else { 1 }
}''',['RawGrowth.minCap matches all three branches'],[])
body('''pub(crate) fn grow_one(&mut self) {
 unsafe { self.inner.grow_one(T::LAYOUT) }
}''',['delegate with actual monomorphised element layout'],['actual T layout association V400-257-layout'])
body('''unsafe fn grow_one(&mut self, elem_layout: Layout) {
 if let Err(err) = unsafe { self.grow_amortized(self.cap.as_inner(), 1, elem_layout) } {
 handle_error(err);
 }
}''',['RawGrowth.requestedCap uses RAW capacity as len and additional=1',
 'GrowingPush.push routes overflow to runtime.overflow; no invented source Result'],
 ['handle_error/diagnostics abort observation remains runtime binding'])
body('''unsafe fn grow_amortized(&mut self, len: usize, additional: usize, elem_layout: Layout,)
 -> Result<(), TryReserveError> {
 debug_assert!(additional > 0);
 if elem_layout.size() == 0 { return Err(CapacityOverflow.into()); }
 let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
 let cap = cmp::max(self.cap.as_inner() * 2, required_cap);
 let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
 let ptr = unsafe { self.finish_grow(cap, elem_layout)? };
 unsafe { self.set_ptr_and_cap(ptr, cap) };
 Ok(())
}''',['release profile eliminates debug assertion',
 'RawGrowth.plan/grow retain ZST overflow and cap/byte overflow',
 'raw+1 checked overflow implies selected cap>=raw+1 exceeds Usize.max and is rejected',
 'raw*2 cannot overflow for a valid nonzero allocation (raw<=isize::MAX)',
 'GrowingFacts.grows_fault retains complete allocator fault prefix before descriptor commit',
 'GrowingFacts.grows_success commits pointer and exact requested cap, preserves type layout'],
 ['native allocation validity/isize bounds/byte preservation required; formal model uses Nat arithmetic under these source bounds'])
body('''unsafe fn finish_grow(&self, cap: usize, elem_layout: Layout,)
 -> Result<NonNull<[u8]>, TryReserveError> {
 let new_layout = layout_array(cap, elem_layout)?;
 let memory = if let Some((ptr, old_layout)) = unsafe { self.current_memory(elem_layout) } {
 debug_assert!(old_layout.align() == new_layout.align());
 unsafe {
 hint::assert_unchecked(old_layout.align() == new_layout.align());
 self.alloc.grow(ptr, old_layout, new_layout)
 }
 } else { self.alloc.allocate(new_layout) };
 match memory {
 Ok(memory) => Ok(memory),
 Err(_) => Err(AllocError { layout: new_layout, non_exhaustive: () }.into()),
 }
}''',['RawGrowth.Resize.old=None is allocate; Some retains pointer,old bytes,alignment for grow',
 'new byte size=cap*element size for valid Rust element layouts (size multiple of alignment)',
 'release current_memory correspondence retained from D575'],
 ['Global::grow/allocate and actual byte heap are unbound; resize is an explicit runtime operation, not fabricated callback values'])
body('''const unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<[u8]>, cap: usize) {
 self.ptr = Unique::from(ptr.cast());
 self.cap = unsafe { Cap::new_unchecked(cap) };
}''',['GrowingFacts.grows_success uses requested cap, not allocator returned slice length'],[])
body('''const fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
 match elem_layout.repeat(cap) {
 Ok((layout, _pad)) => Ok(layout),
 Err(_) => Err(CapacityOverflow.into()),
 }
}''',['RawGrowth.plan checks byte isize bound and retains overflow',
 'RawGrowth.byte_bound_implies_cap: explicit usize cap check redundant for nonzero element size'],
 ['Layout::repeat body/stride law and native validity/alignment remain required before whole binding'])
if '--bodies-only' in sys.argv:
 print('seven complete pinned growth bodies checked; proof/native association not checked')
 raise SystemExit(0)
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
models={}
for m in ['RawGrowth','GrowingPush','GrowingFacts','GrowthSchedule']:
 q=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_V263_'+m+'.lean')
 h=sha(q.read_bytes());assert accepted['R1Z.PV_V263_'+m]['source_sha256']==h,m
 models[m]=h
receipt=json.loads((E/'N90125-receipt.json').read_text());assert receipt['accepted']
results=json.loads((E/'N90125-native-results.json').read_text())
assert len(results)==3 and all(r['expected'] for r in results)
out=dict(script_sha256=sha(Path(__file__).read_bytes()),
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 evidence_class='local structural growth argument plus same-input finite native validation; not machine source proof',
 bodies=rows,models=models,native_receipt='N90125-receipt.json',native_validation='representative scoped-handle payloads; NOT actual encoder/SemanticOracle execution',
 profile=dict(rustc='1.94.1',release=True,opt_level=3,panic='abort',debug_assertions=False,overflow_checks=False),
 source_binding_complete=False,actual_op257_installed=False,actual_reached_success=False,
 remaining=['byte heap, valid ownership/layout, Global allocator and Layout::repeat binding',
 'actual handle layout and integration of OwnedForks/iterator lifecycle into complete source spine',
 'native schedule, thread/TLS/scope, EVH codec',
 'actual opsNative/stateful capture and actual callback laws'])
(E/'growth-source-binding-continuation.json').write_text(json.dumps(out,indent=2)+'\n')
print('seven complete growth bodies; four accepted model sources; finite native differential/control checked; whole binding OPEN')
