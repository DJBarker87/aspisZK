"""Exact token/body checks for eight deployed range/fold/index records, NOT a full row checker.
The structural law is the separately compiled owned Lean loop reference.
"""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
def sha(b):return hashlib.sha256(b).hexdigest()
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tokens(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def span(s,context,marker):
 assert s.count(context)==1,(context,s.count(context))
 a=s.index(context);i=s.index(marker,a);left=s.index('{',i);depth=0
 for m in lex.finditer(s,left):
  if m[0]=='{':depth+=1
  elif m[0]=='}':
   depth-=1
   if depth==0:return s[i:m.end()]
 raise AssertionError('unterminated body')
checks=[
 ('iter/range.rs','impl<A: Step> Iterator for ops::Range<A>', 'fn next(&mut self) -> Option<A>',
  'fn next(&mut self) -> Option<A> { self.spec_next() }',
  'Range<usize> dispatch to TrustedStep spec_next; body has no feature cfg'),
 ('iter/range.rs','impl<T: TrustedStep> RangeIteratorImpl for ops::Range<T>', 'fn spec_next(&mut self) -> Option<T>',
  '''fn spec_next(&mut self) -> Option<T> {
    if self.start < self.end {
      let old = self.start;
      self.start = unsafe { Step::forward_unchecked(old, 1) };
      Some(old)
    } else { None }
  }''', 'R1Z.PV_RDCD3_RangeFold.next_active/next_empty/increment_bound'),
 ('iter/range.rs','macro_rules! step_unsigned_methods', 'unsafe fn forward_unchecked(start: Self, n: usize) -> Self',
  '''unsafe fn forward_unchecked(start: Self, n: usize) -> Self {
    unsafe { start.unchecked_add(n as Self) }
  }''', 'usize instantiation, n=1; increment_bound discharges unchecked-add precondition'),
 ('iter/traits/iterator.rs','pub trait Iterator', 'fn fold<B, F>(mut self, init: B, mut f: F) -> B',
  '''fn fold<B, F>(mut self, init: B, mut f: F) -> B
  where Self: Sized, F: FnMut(B, Self::Item) -> B, {
    let mut accum = init;
    while let Some(x) = self.next() { accum = f(accum, x); }
    accum
  }''', 'R1Z.PV_RDCD3_RangeLoop.all_endpoints; callback Result retains panic/divergence'),
]
checks += [
 ('array/mod.rs','const Index<I> for [T; N]', 'fn index(&self, index: I) -> &Self::Output',
  'fn index(&self, index: I) -> &Self::Output { Index::index(self as &[T], index) }',
  'R1Z.PV_RDCD3_Index194.array_complete; array/slice preserve backing elements and length'),
 ('slice/index.rs','const ops::Index<I> for [T]', 'fn index(&self, index: I) -> &I::Output',
  'fn index(&self, index: I) -> &I::Output { index.index(self) }',
  'Concrete I=usize dispatch to the following record; no alternate index dictionary'),
 ('slice/index.rs','const SliceIndex<[T]> for usize', 'fn index(self, slice: &[T]) -> &T',
  'fn index(self, slice: &[T]) -> &T { &(*slice)[self] }',
  'R1Z.PV_RDCD3_Index194.slice_complete/success/failure; Rust intrinsic indexing is the retained compiler semantic boundary'),
 ('iter/traits/collect.rs','impl<I: Iterator> IntoIterator for I', 'fn into_iter(self) -> I',
  'fn into_iter(self) -> I { self }',
  'Identity on the entire iterator state; not allocation, a copy builtin, or a callback'),
]

out=[]
for path,context,marker,expected,law in checks:
 p=root/path;s=p.read_text();actual=span(s,context,marker)
 assert tokens(actual)==tokens(expected),(path,marker,actual)
 # A changed constant or operation must be rejected by the same equality check.
 mutated=expected
 for old,new in [('1)', '2)'),('self.spec_next()', 'self.spec_next_back()'),('unchecked_add','unchecked_sub'),('self.next()', 'self.next_back()'),('index.index(self)','index.index_mut(self)'),('Index::index','IndexMut::index_mut'),('&(*slice)[self]','&(*slice)[0]'),('{ self }','{ changed }')]:
  if old in mutated:
   mutated=mutated.replace(old,new,1);break
 assert tokens(actual)!=tokens(mutated),'negative structural control unexpectedly accepted'
 out.append(dict(path=str(p),file_sha256=sha(p.read_bytes()),context=context,source_body=actual,source_token_sha256=sha('\0'.join(tokens(actual)).encode()),owned_rust_body=expected,law=law,matched_negative_control='rejected'))
# Check usize TrustedStep specialization and that Range does not override fold.
s=(root/'iter/range.rs').read_text()
assert re.search(r'unsafe_impl_trusted_step!\[[^]]*\busize\b',s)
assert '[usize isize]' in s
context='impl<A: Step> Iterator for ops::Range<A>'
block=span(s,context,context)
assert 'fn fold' not in block and 'impl_fold_via_try_fold!' not in block
result=dict(dispatch_checks='usize TrustedStep declared; usize Step macro invocation selected; Range iterator does not override fold',toolchain='1.94.1',records=out,profile=dict(release=True,debug_assertions=False,overflow_checks=False),scope='Eight source records only; not a complete V260 cone and not a full native-body equivalence checker',feature_argument='Selected core records have no cfg/cfg! in their bodies; concrete usize instantiation is independent of client crate features',composition_trust='Structural source-to-owned-reference reclassification within existing Rust/Lean/compiler tool trust; no endpoint premise removed')
(D/'range-source-result.json').write_text(json.dumps(result,indent=2)+'\n');print('Eight exact body checks and eight rejecting mutation controls passed; partial cone only')
