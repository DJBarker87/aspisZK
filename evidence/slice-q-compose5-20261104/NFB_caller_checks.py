"""Exact deployed call guards. This is a caller-domain check, not parent closure."""
from NFB_source_checks import tok,body,REV,R
import hashlib,subprocess,json,re

def frozen(path):return subprocess.check_output(['git','show',REV+':'+path],cwd=R,text=True)
def check(candidate=None,compact=None):
 candidate=frozen('crates/aspis-r1-cost-probe/src/candidate.rs') if candidate is None else candidate
 compact=frozen('crates/aspis-r1-cost-probe/src/compact.rs') if compact is None else compact
 assert tok('pub const SPLIT: usize = 10;') in [tok(line) for line in compact.splitlines()]
 view=re.sub(r'(fn (?:tx1|tx2_common))<[^>]*>',r'\1',candidate)
 tx1=body(view,'tx1');tx2=body(view,'tx2_common')
 for text,guard,call in [(tx1,'if k!=SPLIT{return Err(Error::Parse);}','QueryGeometry::for_range(&p.queries,0,k)?'),(tx2,'if a.next!=SPLIT{return Err(Error::Checkpoint);}','QueryGeometry::for_range(&p.queries,a.next,22)?')]:
  a,b,g=tok(text),tok(call),tok(guard)
  i=next(i for i in range(len(a)) if a[i:i+len(g)]==g)
  j=next(i for i in range(len(a)) if a[i:i+len(b)]==b)
  assert i<j
  # Scalar k / a.next is never assigned between its guard and the call.
  between=a[i+len(g):j]
  if text==tx1:assert not any(between[n:n+2]==['k','='] for n in range(len(between)))
  else:assert not any(between[n:n+4]==['a','.','next','='] for n in range(len(between)))
 return dict(frozen_revision=REV,candidate_sha256=hashlib.sha256(candidate.encode()).hexdigest(),compact_sha256=hashlib.sha256(compact.encode()).hexdigest(),domain=['0..10','10..22'],native_scalar_pair=['NFB_K096','NFB_K097'],qualification='Reached deployed TX1/TX2 sites only; not a certificate for either parent or audit-eight-way/test callers')
if __name__=='__main__':print(json.dumps(check(),indent=1))
