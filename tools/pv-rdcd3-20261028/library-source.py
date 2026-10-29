"""Concrete deployed library source bindings; not a whole-row original checker."""
from pathlib import Path
import json,runpy,sys
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
a=runpy.run_path(str(D/'range-source.py'));root,span,tokens,sha=(a[k] for k in ['root','span','tokens','sha'])
checks=[
('convert/mod.rs','impl<T> const From<T> for T','fn from(',
 'fn from(t:T)->T{t}','Control194.into_from; concrete error identity conversion'),
('array/mod.rs','const IndexMut<I> for [T; N]','fn index_mut(&mut self, index: I)',
 'fn index_mut(&mut self,index:I)->&mut Self::Output {IndexMut::index_mut(self as &mut[T],index)}','ArrayWrite194.complete/read_back/frame'),
('slice/index.rs','const ops::IndexMut<I> for [T]','fn index_mut(&mut self, index: I)',
 'fn index_mut(&mut self,index:I)->&mut I::Output {index.index_mut(self)}','Concrete I=usize dispatch to the following record'),
('slice/index.rs','const SliceIndex<[T]> for usize','fn index_mut(self, slice: &mut [T])',
 'fn index_mut(self,slice:&mut[T])->&mut T {&mut(*slice)[self]}','ArrayWrite194.complete/read_back/frame; native checked-write intrinsic boundary'),
('option.rs','pub const fn ok_or<E:', 'pub const fn ok_or<E:',
 'pub const fn ok_or<E:[const] Destruct>(self,err:E)->Result<T,E>{match self {Some(v)=>Ok(v),None=>Err(err),}}','Result194.ok_or_some/ok_or_none; V265.okOr_binding'),
('result.rs','fn branch(self) -> ControlFlow<Self::Residual, Self::Output>', 'fn branch(self) -> ControlFlow<Self::Residual, Self::Output>',
 'fn branch(self)->ControlFlow<Self::Residual,Self::Output>{match self{Ok(v)=>ControlFlow::Continue(v),Err(e)=>ControlFlow::Break(Err(e)),}}','Result194.question_mark'),
('result.rs','fn from_residual(residual: Result<convert::Infallible, E>)', 'fn from_residual(residual: Result<convert::Infallible, E>)',
 'fn from_residual(residual:Result<convert::Infallible,E>)->Self{match residual{Err(e)=>Err(From::from(e)),}}','Result194.residual/question_mark; concrete E=F identity From, empty Infallible Ok case'),
('result.rs','pub const fn unwrap_or_else<F>', 'pub const fn unwrap_or_else<F>',
 'pub const fn unwrap_or_else<F>(self,op:F)->T where F:[const] FnOnce(E)->T+[const] Destruct,{match self{Ok(t)=>t,Err(e)=>op(e),}}','Result194.unwrap_ok/unwrap_error; V265.unwrap_binding'),
('num/uint_macros.rs','macro_rules! uint_impl','pub const fn from_le_bytes(',
 'pub const fn from_le_bytes(bytes:[u8;size_of::<Self>()])->Self{Self::from_le(Self::from_ne_bytes(bytes))}','Endian194.binding; integer-layout/compiler primitive is retained explicitly'),
('num/uint_macros.rs','macro_rules! uint_impl','pub const fn from_ne_bytes(',
 'pub const fn from_ne_bytes(bytes:[u8;size_of::<Self>()])->Self{unsafe{mem::transmute(bytes)}}','Endian194.word/binding at existing transmute primitive boundary'),
('num/uint_macros.rs','macro_rules! uint_impl','pub const fn from_le(',
 'pub const fn from_le(x:Self)->Self{#[cfg(target_endian="little")]{x}#[cfg(not(target_endian="little"))]{x.swap_bytes()}}','Endian194.word/binding; host target little endian, identity branch selected'),
]
records=[]
for path,context,marker,expected,law in checks:
 p=root/path;actual=span(p.read_text(),context,marker)
 assert tokens(actual)==tokens(expected),(path,marker,actual)
 bad=expected.replace('self','changed_receiver',1)
 assert tokens(actual)!=tokens(bad),(path,marker)
 records.append(dict(path=str(p),file_sha256=sha(p.read_bytes()),context=context,body=actual,expected_body=expected,law='PV_RDCD3_'+law,negative_control='changed receiver/dispatch rejected'))
assert sys.byteorder=='little'
features=json.load(open(D/'deployed-client-features.json'))
assert all(not x['profile']['debug_assertions'] and not x['profile']['overflow_checks'] for x in features)
j=dict(records=records,toolchain='1.94.1',target='x86_64-unknown-linux-gnu, little endian',scope='Eleven complete concrete library bodies only; row closure also requires full source binding, matching proof receipts, frozen DAG and same-input finite evidence',destructor_qualification='CirclePointError and captured CircleRow are concrete Copy enums with no user Drop; no claim about arbitrary destructor/world effects',primitive_boundary='Integer casts/transmute/layout and checked typed-memory reads/writes retain existing compiler/Aeneas semantics; no LLVM/world/observer theorem',composition='Reclassification within existing tool trust; zero endpoint premise removal',feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()))
(D/'library-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print('Eleven complete concrete library bodies and rejecting mutation controls matched')
