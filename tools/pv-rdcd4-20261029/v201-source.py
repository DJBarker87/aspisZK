"""Statement-level source checks for the first concrete iterator bindings.
This is an own-1 binding preflight, NOT the recovered original checker and NOT
b3p6-1 (the complete extraction hash-chain condition is not established here).
"""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
lib={x['relative']:x for x in json.loads((E/'library-sources.json').read_text())}
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tokens(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def sha(b):return hashlib.sha256(b).hexdigest()
def body(path,context,marker):
 s=lib[path]['text'];assert s.count(context)==1,(path,context,s.count(context))
 a=s.index(marker,s.index(context));b=s.index('{',a);depth=0
 for m in lex.finditer(s,b):
  if m[0]=='{':depth+=1
  elif m[0]=='}':
   depth-=1
   if not depth:return s[a:m.end()]
 raise AssertionError((path,marker))
checks=[
('slice/mod.rs','pub const fn chunks_exact(', 'pub const fn chunks_exact(','''pub const fn chunks_exact(&self,chunk_size:usize)->ChunksExact<'_,T>{assert!(chunk_size!=0,"chunk size must be non-zero");ChunksExact::new(self,chunk_size)}''', 'chunks_exact', ['chunk_size=2, assertion cannot fail','call ChunksExact::new'], 'Chunks194.message_new'),
('slice/iter.rs',"impl<'a, T> ChunksExact<'a, T>", 'pub(super) const fn new(','''pub(super) const fn new(slice:&'a[T],chunk_size:usize)->Self{let rem=slice.len()%chunk_size;let fst_len=slice.len()-rem;let(fst,snd)=unsafe{slice.split_at_unchecked(fst_len)};Self{v:fst,rem:snd,chunk_size}}''', 'ChunksExact.new', ['length modulo two','fst_len subtraction is bounded','split_at_unchecked(fst_len)','store all three fields, chunk_size fixed2'], 'Chunks194.new/new_even'),
('slice/iter.rs',"impl<'a, T> Iterator for ChunksExact<'a, T>",'fn next(','''fn next(&mut self)->Option<&'a[T]>{self.v.split_at_checked(self.chunk_size).and_then(|(chunk,rest)|{self.v=rest;Some(chunk)})}''','ChunksExact.next',['split checked','None: leave entire iterator unchanged','Some: store rest to v, retain rem and chunk_size','yield chunk'], 'Chunks194.next/next_pair/next_empty/next_single'),
('slice/mod.rs','pub const fn split_at_checked(', 'pub const fn split_at_checked(','''pub const fn split_at_checked(&self,mid:usize)->Option<(&[T],&[T])>{if mid<=self.len(){Some(unsafe{self.split_at_unchecked(mid)})}else{None}}''','slice.split_at_checked',['check mid<=length','Some: invoke unchecked split with established precondition','None: no call/store'], 'pending split lemma; Chunks194.next currently interpreted through take/drop'),
('array/iter.rs','impl<T, const N: usize> IntoIterator for [T; N]','fn into_iter(','''fn into_iter(self)->Self::IntoIter{let data:[MaybeUninit<T>;N]=unsafe{transmute_unchecked(self)};let inner=unsafe{InnerSized::new_unchecked(IndexRange::zero_to(N),data)};IntoIter{inner:ManuallyDrop::new(inner)}}''','array.into_iter',['transmute initialized array to MaybeUninit array, same ordered storage at V370','zero_to(N) initializes start0,endN','new_unchecked stores alive,data','ManuallyDrop wrapper initialized'], 'ArrayIter194.new/new_valid; representation primitives retained at V370'),
('array/iter.rs','impl<T, const N: usize> Iterator for IntoIter<T, N>','fn next(','''fn next(&mut self)->Option<Self::Item>{self.unsize_mut().next()}''','IntoIter.next',['unsize_mut retains alive and data','call PolymorphicIter.next'], 'ArrayIter194.next; wrapper binding pending'),
('array/iter/iter_inner.rs','/// Iterator-equivalent methods.','pub(super) fn next(','''pub(super) fn next(&mut self)->Option<T>{self.alive.next().map(|idx|{unsafe{self.data.get_unchecked(idx).assume_init_read()}})}''','PolymorphicIter.next',['advance alive before read','None: no read','Some idx: read initialized data[idx]','alive range updated, backing ordered data retained for Copy'], 'ArrayIter194.next/next_active/next_done'),
('ops/index_range.rs','impl Iterator for IndexRange','fn next(','''fn next(&mut self)->Option<usize>{if self.len()>0{unsafe{Some(self.next_unchecked())}}else{None}}''','IndexRange.next',['len=stop-start','active iff start<stop by valid invariant','None retains start and stop','active invokes next_unchecked'], 'ArrayIter194.next/next_active/next_done'),
('ops/index_range.rs','const unsafe fn next_unchecked(','const unsafe fn next_unchecked(','''const unsafe fn next_unchecked(&mut self)->usize{debug_assert!(self.start<self.end);let value=self.start;self.start=unsafe{value.unchecked_add(1)};value}''','IndexRange.next_unchecked',['release debug assertion disabled','save old start','store start+1 before returning old start','active start<stop<=512 discharges overflow'], 'ArrayIter194.next_active; machine-usize bound pending'),
('ops/index_range.rs','pub(crate) const fn zero_to(', 'pub(crate) const fn zero_to(','''pub(crate) const fn zero_to(end:usize)->Self{IndexRange{start:0,end}}''','IndexRange.zero_to',['store start0','store endN'], 'ArrayIter194.new'),
('array/iter/iter_inner.rs','pub(super) const unsafe fn new_unchecked(', 'pub(super) const unsafe fn new_unchecked(','''pub(super) const unsafe fn new_unchecked(alive:IndexRange,data:[MaybeUninit<T>;N])->Self{Self{alive,data}}''','PolymorphicIter.new_unchecked',['store initialized alive','store initialized data'], 'ArrayIter194.new'),
('array/iter.rs','impl<T, const N: usize> Drop for IntoIter<T, N>','fn drop(','''fn drop(&mut self){if crate::mem::needs_drop::<T>(){unsafe{ManuallyDrop::drop(&mut self.inner)}}}''','IntoIter.drop',['WideExact:Copy has no user Drop','needs_drop<WideExact> false','no PolymorphicIter.drop/partial_drop call on normal completion or unwind'], 'ArrayIter194.drop_copy'),
]
records=[]
for path,context,marker,expected,name,steps,law in checks:
 actual=body(path,context,marker)
 assert tokens(actual)==tokens(expected),(name,actual)
 mut=expected[:expected.index('{')]+'{panic!("negative_control")}'
 assert tokens(actual)!=tokens(mut),name
 records.append(dict(name=name,path=lib[path]['path'],file_sha256=lib[path]['sha256'],body=actual,body_sha256=sha(actual.encode()),token_sha256=sha('\0'.join(tokens(actual)).encode()),expected_body=expected,expected_token_sha256=sha('\0'.join(tokens(expected)).encode()),ordered_steps=steps,lean_target='R1Z.PV_RDCD4_'+law,negative_control='changed whole body rejected by token comparison; syntactic control, not compiled semantic validation',binding_credit='pending complete proof/primitive/wrapper closure; no whole-row credit'))
(E/'v201-source-bindings.json').write_text(json.dumps(dict(records=records,toolchain='1.94.1',profile='release; debug_assertions=false; overflow_checks=false',scope='Own-1 statement binding preflight; pending laws are explicitly labelled. Body hashes before macro expansion; no b3p6-1 inference.',compiler_boundary='V370/D381/D386 retained'),indent=2)+'\n')
print('Matched',len(records),'complete source bodies and rejecting syntactic controls')
