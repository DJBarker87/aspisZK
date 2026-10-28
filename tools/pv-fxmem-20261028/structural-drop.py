"""Complete-body token checks for Vec<u32> drop; K-1 structural substitute."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
b='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'
paths={k:b+v for k,v in dict(vec='alloc/src/vec/mod.rs',raw='alloc/src/raw_vec/mod.rs',alloc='alloc/src/alloc.rs',mem='core/src/mem/mod.rs').items()}
code='from pathlib import Path\nimport json\nprint(json.dumps({k:Path(p).read_text() for k,p in '+repr(paths)+'.items()}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
sources=json.loads(r.stdout)
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def body(s,anchor):
 s=clean(s);p=s.index(anchor);a=s.index('{',p);d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  if s[i]=='}':
   d-=1
   if d==0:return s[a:i+1]
 raise ValueError(anchor)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
expected=[('vec','Drop for Vec<T, A>', '{fn drop(&mut self) {unsafe {self.as_mut_ptr().cast_slice(self.len).drop_in_place()}}}'),
 ('raw','Drop for RawVec<T, A>','{fn drop(&mut self) {unsafe {self.inner.deallocate(T::LAYOUT)}}}'),
 ('raw','unsafe fn deallocate(&mut self, elem_layout: Layout)', '{if let Some((ptr, layout)) = unsafe {self.current_memory(elem_layout)} {unsafe {self.alloc.deallocate(ptr, layout);}}}'),
 ('alloc','unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)','{unsafe {self.deallocate_impl(ptr, layout)}}'),
 ('alloc','const unsafe fn deallocate_impl(&self, ptr: NonNull<u8>, layout: Layout)','{core::intrinsics::const_eval_select((ptr, layout),Global::deallocate_impl_const,Global::deallocate_impl_runtime,)}'),
 ('alloc','fn deallocate_impl_runtime(ptr: NonNull<u8>, layout: Layout)','{if layout.size() != 0 {unsafe {dealloc_nonnull(ptr, layout)}}}'),
 ('mem','pub const fn drop<T>(_x: T)','{}')]
checks=[]
for k,a,want in expected:
 actual=body(sources[k],a);assert tokens(actual)==tokens(want),(k,a,actual)
 checks.append(dict(file=paths[k],anchor=a,body=actual,tokens_equal=True))
current=body(sources['raw'],'const unsafe fn current_memory(')
# Record the complete actual branch/layout calculation for audit; assertions
# below ensure the nonzero-capacity test and allocation-layout construction.
assert 'self.cap.as_inner() == 0' in current and 'elem_layout.size() == 0' in current,current
assert tokens(current)==tokens('''{if elem_layout.size() == 0 || self.cap.as_inner() == 0 {None} else {unsafe {let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());Some((self.ptr.into(), layout))}}}'''),current
checks.append(dict(file=paths['raw'],anchor='current_memory',body=current,branch_checks=True))
j=dict(evidence_class='structural (K-1 substitute)',files={k:dict(path=paths[k],sha256=hashlib.sha256(v.encode()).hexdigest()) for k,v in sources.items()},checks=checks,
 type='Vec<u32,Global>; u32 has no user destructor, size 4, alignment 4; Global is zero-sized with no destructor',
 source_order='drop u32 slice (zero user destructor calls); drop RawVec; current_memory iff capacity nonzero; Global runtime deallocation, layout (4*capacity,4)',
 world='PV_FXM_DropWorld.native/reference; allocator primitive free retains its private state; no claim of cleared freed bytes; invalidates allocation identity',
 limits='Library primitive interpretation on valid owned allocations with returning System deallocation; not a proof of libc internals, machine nonreturn, timing, or deployed binary correspondence. Those are retained P obligations, never T.',
 native_differential='drop-u32-03, finite validation, recorded separately')
(E/'STRUCTURAL-DROP-GATE.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS complete drop chain token checks')
