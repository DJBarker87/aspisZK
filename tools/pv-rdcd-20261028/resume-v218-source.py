"""Concrete usize reverse-iterator source binding; primitive compiler boundary retained."""
from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');O=D/'resume-v218';records=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def tok(s):return re.findall(r'\w+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
def span(s,marker,after=''):
 a=s.index(marker,s.index(after) if after else 0);b=s.index('{',a);e=b+1;depth=1
 while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
for version in ['nightly-2026-06-01','1.94.1']:
 root=Path('/home/dombarker/.rustup/toolchains')/(version+'-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
 r=dict(version=version,files={},bodies={})
 for file,items in {
  'iter/range.rs':[('trusted_back','fn spec_next_back(&mut self) -> Option<T>','impl<T: TrustedStep> RangeIteratorImpl'),('unsigned_back','unsafe fn backward_unchecked(start: Self, n: usize) -> Self','macro_rules! step_unsigned_methods'),('unsigned_forward','unsafe fn forward_unchecked(start: Self, n: usize) -> Self','macro_rules! step_unsigned_methods')],
  'iter/adapters/rev.rs':[('rev_next','fn next(&mut self) -> Option<<I as Iterator>::Item>',''),('rev_new','fn new(iter: T) -> Rev<T>','')],
  'iter/traits/iterator.rs':[('rev','fn rev(self) -> Rev<Self>','')],
  'iter/traits/collect.rs':[('identity_into_iter','fn into_iter(self) -> I','IntoIterator for I')],
 }.items():
  p=root/file;s=p.read_text();r['files'][file]=dict(path=str(p),sha256=sha(p.read_bytes()))
  for key,marker,after in items:
   b=span(s,marker,after);r['bodies'][key]=dict(text=b,token_sha256=sha('\0'.join(tok(b)).encode()))
 s=(root/'iter/range.rs').read_text();assert re.search(r'step_integer_impls!\s*\{[\s\S]*?usize',s)
 if version=='1.94.1':
  assert tok(r['bodies']['trusted_back']['text'])==tok('''fn spec_next_back(&mut self) -> Option<T> { if self.start < self.end { self.end = unsafe { Step::backward_unchecked(self.end, 1) }; Some(self.end) } else { None } }''')
  assert tok(r['bodies']['unsigned_back']['text'])==tok('''unsafe fn backward_unchecked(start: Self, n: usize) -> Self { unsafe { start.unchecked_sub(n as Self) } }''')
 records.append(r)
comparison={k:records[0]['bodies'][k]['token_sha256']==records[1]['bodies'][k]['token_sha256'] for k in records[0]['bodies']}
result=dict(row='V218',cohorts=records,identical=comparison,concrete_dispatch='Range<usize> is TrustedStep integer specialization; Rev.next calls next_back; usize cast is identity; next_back writes end before returning it',laws=['PV_RDCD_Range194.backward_bound','PV_RDCD_Range194.next_back','PV_RDCD_Range194.reverse_dispatch','PV_RDCD_Range194.reverse_new'],primitive_boundary='Rust scalar unchecked subtraction with proved nonoverflow precondition; primitive comparisons, stack array copy/value layout and compiler cohort; no L1/L2/L3 or RunJoin discharge',qualification='Supplemental concrete source/model binding, original route remains pinned extraction; source hash comparison alone never proves native binary refinement')
(O/'source-binding.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(comparison,indent=2))
