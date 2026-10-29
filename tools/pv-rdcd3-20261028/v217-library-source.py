"""Complete additional reverse-iterator bodies, restricted to the V217 Result cone."""
from pathlib import Path
import runpy,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
a=runpy.run_path(str(D/'range-source.py'));root,span,tokens,sha=(a[k] for k in ['root','span','tokens','sha'])
checks=[
('iter/traits/iterator.rs','pub trait Iterator','fn rev(self) -> Rev<Self>',
 'fn rev(self)->Rev<Self> where Self:Sized+DoubleEndedIterator,{Rev::new(self)}',
 'MaskRootEq.reference; constructor retains the entire iterator'),
('iter/adapters/rev.rs','impl<T> Rev<T>','pub(in crate::iter) fn new(',
 'pub(in crate::iter) fn new(iter:T)->Rev<T>{Rev{iter}}',
 'ReverseRange.before; record constructor, no memory read or hidden state'),
('iter/adapters/rev.rs','impl<I> Iterator for Rev<I>','fn next(&mut self)',
 'fn next(&mut self)->Option<<I as Iterator>::Item>{self.iter.next_back()}',
 'ReverseRange.next_zero/next_pos; full updated inner range retained'),
('iter/range.rs','impl<A: Step> DoubleEndedIterator for ops::Range<A>','fn next_back(&mut self)',
 'fn next_back(&mut self)->Option<A>{self.spec_next_back()}',
 'Receiver ops::Range<usize>; TrustedStep specialization below'),
('iter/range.rs','impl<T: TrustedStep> RangeIteratorImpl for ops::Range<T>','fn spec_next_back(&mut self)',
 'fn spec_next_back(&mut self)->Option<T>{if self.start<self.end{self.end=unsafe{Step::backward_unchecked(self.end,1)};Some(self.end)}else{None}}',
 'ReverseRange.next_zero/next_pos; before e has start zero; predecessor result also becomes new end'),
('iter/range.rs','macro_rules! step_unsigned_methods','unsafe fn backward_unchecked(start: Self, n: usize)',
 'unsafe fn backward_unchecked(start:Self,n:usize)->Self{unsafe{start.unchecked_sub(n as Self)}}',
 'ReverseRange.pred_val; ReverseWrap.pred_eq; n=1 and start>0 discharged by active guard'),
]
records=[]
for path,context,marker,expected,law in checks:
 p=root/path;actual=span(p.read_text(),context,marker)
 assert tokens(actual)==tokens(expected),(path,marker,actual)
 bad=expected[:expected.index('{')]+'{panic!("negative_control")}'
 assert tokens(actual)!=tokens(bad)
 records.append(dict(path=str(p),source_sha256=sha(p.read_bytes()),context=context,source_body=actual,expected_body=expected,law='R1Z.PV_RDCD3_'+law,negative_control='terminal panic substitution rejected; syntactic control, not a compiled fidelity control'))
features=json.load(open(D/'deployed-client-features.json'))
assert all(not x['profile']['overflow_checks'] and not x['profile']['debug_assertions'] for x in features)
j=dict(records=records,source_toolchain='1.94.1',feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()),scope='Additional V217 reverse range source bodies only. Complete application/field binding, named successful proof receipts, coherent DAG and unchanged native finite validation still required.',primitive_boundary='Unchecked integer intrinsic on a proved safe domain and typed array memory retained at V370/Aeneas primitive semantics; diagnostics/world/observer not proved',composition='Reclassification within existing tool trust; no endpoint premise removal')
(D/'v217-library-source-result.json').write_text(json.dumps(j,indent=2)+'\n')
print('Six additional complete reverse-iterator bodies matched')
