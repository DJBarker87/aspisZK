#!/usr/bin/env python3
"""Check exact std-leaf body transport and unchanged generated Lean sources.
This does not validate lowering of Option<&mut T> in the consuming loop.
"""
from pathlib import Path
import hashlib,json,re
here=Path(__file__).resolve().parent;area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019'
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=json.loads((here/'rho-std-source-slices.json').read_text())
assert sources['option.rs']['sha256']=='7cf61204b05d98a95bc2e322d5fbfc1f4f91505109971917d9a7fb47151c50e6'
assert sources['ops/deref.rs']['sha256']=='55d940bd62685513afbc552b96ea42974a45fc16f6db1d4971d56c332074eca5'
def body(s):return s[s.index('{')+1:s.rindex('}')]
def norm(s):return re.sub(r'\s+','',s).replace(',}', '}')
def item(s,anchor):
 i=s.index(anchor);start=s.index('{',i);depth=1;j=start+1
 while depth:
  depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i:j]
local=(here/'rho-local-option-input/lib.rs').read_text()
ident=(here/'rho-reference-deref-identity-input/lib.rs').read_text()
option=sources['option.rs']['items']
for standard,local_anchor in [('pub const fn as_mut(', 'pub fn as_mut<'),('pub const fn map<','pub fn map<')]:
 assert norm(body(option[standard]).replace('self','value'))==norm(body(item(local,local_anchor)))
standard=item(sources['ops/deref.rs']['items']['const impl<T: ?Sized> DerefMut for &mut T'],'fn deref_mut(')
assert norm(body(standard).replace('self','value'))==norm(body(item(ident,'pub fn reborrow<')))
assert norm(body(option['pub const fn as_deref_mut(']))=='self.as_mut().map(DerefMut::deref_mut)'
assert norm(body(item(local,'pub fn as_deref_mut<')))=='map(as_mut(value),deref_mut)'
# Receiver lifting and sized reference specialization are declaration transports;
# full nested-borrow specialization is explicitly NOT certified here.
checks={}
for raw,namespace,attempt in [('rho-option-leaves-generated','AspisR1RhoOptionLeaves','rho-option-leaves-aeneas-a'),('rho-reference-deref-identity-generated','AspisR1RhoReferenceDeref','rho-reference-deref-identity-aeneas-a')]:
 receipt=json.loads((ev/attempt/'receipt.json').read_text());assert receipt['exit_status']==0
 assert receipt['frontend_binary_sha256']=='4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5'
 for name in ['Types.lean','Funs.lean']:
  b=(here/raw/name).read_bytes();assert b==(area/'lean'/namespace/name).read_bytes()
  checks[namespace+'/'+name]=sha(b)
 for p in (here/raw).glob('*.lean'):assert not re.search(rb'(?m)^\s*(axiom|opaque)\s|\b(sorry|admit)\b',p.read_bytes())
print(json.dumps(dict(status='EXACT_STANDARD_LEAF_BODY_TRANSPORT_CHECKED',generated_sources=checks,
 complete_candidate=False,nested_borrow_caller_lowering='OPEN',
 declaration_transports=['runtime const markers removed; receiver lifted to value',
 'DerefMut receiver specialized to &mut &mut T with Sized target',
 'as_deref_mut UFCS call spelling recorded, not accepted as translated nested-borrow source']),indent=2))
