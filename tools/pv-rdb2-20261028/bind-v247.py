"""Deployed then/Copied/Iter-fold source cone and exact Result-law association."""
from pathlib import Path
import hashlib,json,re,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028');S=D/'src'
L=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'"(?:[^"\\]|\\.)*"|::|=>|\w+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return s[a:i+1]
 raise ValueError(needle)
checks=[]
def check(p,needle,expected,law):
 raw=p.read_bytes();b=body(raw.decode(),needle);assert tokens(b)==tokens(expected),(str(p),needle,b)
 checks.append(dict(path=str(p),file_sha256=hashlib.sha256(raw).hexdigest(),item=needle,body=b,exact_tokens=True,law=law))
check(S/'crates/aspis-statement/src/state_only_semantic.rs','pub fn state_only_copy_helper_sum(',
 '{(h1.len()==TRACE_ROWS).then(||h1.iter().copied().fold(QM31::ZERO,QM31::add))}',
 'SumDeployed.complete/storage_and_value/wrong_length_no_read/installed')
semantic=(S/'crates/aspis-statement/src/state_only_semantic.rs').read_text()
assert re.search(r'use crate::trace_v4::\{[^}]*\bTRACE_ROWS\b[^}]*\}',semantic,re.S)
constant=S/'crates/aspis-statement/src/trace_v4.rs'
assert 'pub const TRACE_ROWS: usize = 1 << 10;' in constant.read_text()
checks.append(dict(path=str(constant),file_sha256=hashlib.sha256(constant.read_bytes()).hexdigest(),constant='TRACE_ROWS=1<<10=1024',import_resolved=True))
check(L/'core/src/bool.rs','pub fn then<','{if self{Some(f())}else{None}}','SumDeployed.wrong_length_no_read; callback evaluated only on true')
check(L/'core/src/iter/adapters/copied.rs','pub(in crate::iter) fn new(', '{Copied{it}}', 'single-field adapter construction; unchanged iterator')
check(L/'core/src/iter/adapters/copied.rs','fn copy_fold<', '{move |acc,&elt| f(acc,elt)}', 'four-limb Copy semantics; SumNative.add_source; backing slice unchanged')
check(L/'core/src/iter/adapters/copied.rs','fn fold<', '{self.it.fold(init,copy_fold(f))}', 'Fold.initial/complete; SumDeployed.fold_value')
check(L/'core/src/slice/iter/macros.rs','fn fold<B, F>(', '''{
 if is_empty!(self){return init;}let mut acc=init;let mut i=0;let len=len!(self);
 loop{acc=f(acc,unsafe{& $($mut_)? *self.ptr.add(i).as_ptr()});
 i=unsafe{i.unchecked_add(1)};if i==len{break;}}acc}''',
 'Fold.complete/initial/increment/qm31_read_bounds/offset_provenance/offset_alignment; SumDeployed.complete')
macro=clean((L/'core/src/slice/iter/macros.rs').read_text())
assert 'unsafe { end.offset_from_unsigned($self.ptr) }' in macro
assert 'end => $self.ptr == end,' in macro
check(L/'core/src/ptr/non_null.rs','pub const unsafe fn offset_from_unsigned(',
 '{unsafe{self.as_ptr().offset_from_unsigned(subtracted.as_ptr())}}',
 'Fold.length_from_pointers; same allocation from NonNull.cast_provenance and Fold.offset_provenance')
check(L/'core/src/ptr/mut_ptr.rs','pub const unsafe fn offset_from_unsigned(',
 '{unsafe{(self as *const T).offset_from_unsigned(origin)}}', 'const/mut pointer cast retains allocation and address')
check(L/'core/src/ptr/const_ptr.rs','pub const unsafe fn offset_from_unsigned(', '''{
 #[rustc_allow_const_fn_unstable(const_eval_select)]
 const fn runtime_ptr_ge(this:*const (),origin:*const ())->bool{
 const_eval_select!(@capture{this:*const (),origin:*const ()}->bool:
 if const{true}else{this>=origin})}
 ub_checks::assert_unsafe_precondition!(check_language_ub,
 "ptr::offset_from_unsigned requires `self >= origin`",
 (this:*const ()=self as *const (),origin:*const ()=origin as *const (),)=>runtime_ptr_ge(this,origin));
 let pointee_size=size_of::<T>();assert!(0<pointee_size&&pointee_size<=isize::MAX as usize);
 unsafe{intrinsics::ptr_offset_from_unsigned(self,origin)}}''',
 'Fold.length_from_pointers; pointee size16; native valid-slice allocation/provenance relation')
out=dict(row='V247',checks=checks,toolchain='rustc1.94.1',
 profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',
 resolved_features_reference='native-sum/receipt.json',
 shared_constructor_laws='V240-deployed-body-binding.json: NonNull.from_ref_complete/cast_complete/iterator_constructor',
 arithmetic_source='same frozen CT add source; SumNative.limb_source/add_source prove complete arbitrary-raw-word law',
 original_result='PV_B1_SumOriginal.op230_source; PV_B1_Close230.selected_callback',
 deployed_result='R1Z.PV_RDB2_SumDeployed.complete/installed',
 mutation_audit='Only acc and i locals are assigned; iter/copy_fold use shared references; every backing-storage return preserved; no backward mutable continuation exists.',
 precise_boundary='bool::then, Slice::iter/Iter::new, Copied::new/copy_fold/fold, Iter::fold, pointer difference/add/as_ptr, QM31::add; no Bound::copied or SIMD dictionary is instantiated here.',
 machine_boundary='Rust reference/Copy/intrinsic/transparent-layout semantics; no compiler, SBF or complete observer correspondence claimed',restored=False)
(D/'V247-deployed-body-binding.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS exact deployed then/Copied/Iter fold, pointer difference wrappers and native sum body')
