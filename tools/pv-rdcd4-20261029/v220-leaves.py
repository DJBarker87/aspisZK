"""Selected wrapping/range wrapper source bindings; no extraction credit."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';lib={x['relative']:x for x in json.load(open(E/'v220-library-sources.json'))}
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def toks(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def body(s,c,m):
 assert s.count(c)==1,c;a=s.index(m,s.index(c));b=s.index('{',a);depth=0
 for x in lex.finditer(s,b):
  if x[0]=='{':depth+=1
  elif x[0]=='}':
   depth-=1
   if not depth:return s[a:x.end()]
checks=[
('num/uint_macros.rs','pub const fn wrapping_add(','pub const fn wrapping_add(', 'pub const fn wrapping_add(self,rhs:Self)->Self{intrinsics::wrapping_add(self,rhs)}','add_forward; U32 instantiated by the uint_impl macro; compiler intrinsic retained'),
('num/uint_macros.rs','pub const fn wrapping_sub(','pub const fn wrapping_sub(', 'pub const fn wrapping_sub(self,rhs:Self)->Self{intrinsics::wrapping_sub(self,rhs)}','sub_forward; same operands and result; compiler intrinsic retained'),
('range.rs','impl<T> const From<Range<T>> for legacy::Range<T>','fn from(', 'fn from(value:Range<T>)->Self{Self{start:value.start,end:value.end}}','constructor/fromRange; both endpoints copied without modification'),
('range/iter.rs','impl<A: Step> IntoIterator for Range<A>','fn into_iter(', 'fn into_iter(self)->Self::IntoIter{RangeIter(self.into())}','constructor; Into forwards concrete From, then wrap the complete legacy range'),
('range/iter.rs','impl<A: Step> Iterator for RangeIter<A>','fn next(', 'fn next(&mut self)->Option<A>{self.0.next()}','next_binding/active/exhausted; updated complete inner range retained'),
('convert/mod.rs','impl<T, U> const Into<U> for T','fn into(', 'fn into(self)->U{U::from(self)}','intoLegacy; instantiate From with exactly the endpoint-preserving range conversion')]
rows=[]
for path,ctx,marker,expected,law in checks:
 actual=body(lib[path]['text'],ctx,marker);assert toks(actual)==toks(expected),(path,marker)
 rows.append(dict(path=lib[path]['path'],file_sha256=lib[path]['sha256'],body=actual,expected=expected,token_sha256=hashlib.sha256(json.dumps(toks(actual)).encode()).hexdigest(),law='R1Z.PV_RDCD4_RangeAPI194.'+law))
(E/'v220-leaf-bindings.json').write_text(json.dumps(dict(records=rows,classification='own-1 structural wrapper bindings; no b3p6-1 or native binary claim',pending='Fresh RangeAPI194 kernel receipt required'),indent=2)+'\n');print('Six complete source wrapper bodies match; fresh kernel bindings pending.')
