"""Complete deployed Default/reference call binding, not an old-body identity test."""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
F=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return s[a:i+1]
 raise ValueError(needle)
vec=(S/'alloc/src/vec/mod.rs').read_text();raw=(S/'alloc/src/raw_vec/mod.rs').read_text()
checks=[]
def check(path,source,anchor,want):
 actual=body(source,anchor);assert tokens(actual)==tokens(want),(anchor,actual)
 checks.append(dict(path=path,anchor=anchor,complete_body=actual,sha256=hashlib.sha256(source.encode()).hexdigest(),tokens_equal=True))
check('alloc/src/vec/mod.rs',vec,'Default for Vec<T>','{fn default() -> Vec<T> {Vec::new()}}')
bundle=json.loads((F/'structural-inputs.json').read_text())
# The owned reference used by the original extraction is tracked in this branch.
ref=(D/'op35-reference.rs').read_text()
check('tools/pv-cblib-20261027/lib.rs',ref,'fn default_reference<T>()','{Vec::new()}')
emission=(D/'op35-reference.lean.txt').read_text()
assert 'def default_reference (T : Type) : Result (alloc.vec.Vec T) := do\n  ok (alloc.vec.Vec.new T)' in emission
checks.append(dict(path='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CBL_Op35Reference.lean',sha256=hashlib.sha256(emission.encode()).hexdigest(),body='ok (alloc.vec.Vec.new T)',source_reference_sha256=hashlib.sha256(ref.encode()).hexdigest()))
# Both calls resolve to the same deployed core/alloc/std, not two modeled copies.
check('alloc/src/vec/mod.rs',vec,'pub const fn new()','{Vec {buf: RawVec::new(),len: 0}}')
check('alloc/src/raw_vec/mod.rs',raw,'pub(crate) const fn new()','{Self::new_in(Global)}')
check('alloc/src/raw_vec/mod.rs',raw,'pub(crate) const fn new_in(alloc: A)','{const {assert!(T::LAYOUT.size() % T::LAYOUT.align() == 0)}; Self {inner: RawVecInner::new_in(alloc, Alignment::of::<T>()),_marker: PhantomData}}')
check('alloc/src/raw_vec/mod.rs',raw,'const fn new_in(alloc: A, align: Alignment)','{let ptr = Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()));Self {ptr,cap: ZERO_CAP,alloc}}')
report=dict(row='V186',evidence_class='structural (K-1 substitute)',checks=checks,shared_callee='The same monomorphization Vec::<T>::new in the same 1.94.1 sysroot and deployed process; no conditional compilation at either call',changed_body='RawVecInner::new_in uses Alignment::as_nonzero rather than as_nonzero_usize. Both callers execute the SAME deployed body; no equality of historical/deployed constructor semantics is required for the row law.',complete_Result_laws=['R1Z.PV_RDB1_V186.complete','R1Z.PV_RDB1_V186.selected_result'],before='default = ok(Vec.new), proven on the prior owned reference; native association suspended for sysroot drift',after='same equation; deployed default and reference are identical calls for every T and every constructor behavior',boundary='Existing op35 library value/Result boundary. No new destructor, allocator, compiler, binary, timing or endpoint theorem.',features=json.loads((F/'units-client-bin/features.json').read_text()),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='1.94.1',kani=False)
(D/'v186-structural.json').write_text(json.dumps(report,indent=2));print('V186 deployed default/reference are the same complete call')
