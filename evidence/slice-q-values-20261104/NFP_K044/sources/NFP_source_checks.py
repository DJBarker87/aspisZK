"""Exact frozen/native loop cut comparison; every accepted token is checked."""
import re,hashlib

def body(s,name):
 a=s.index('{',s.index('fn '+name+'('));i=a+1;depth=1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a+1:i-1]
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|>=|<=|=>|==|!=|[^\s]',s)
def loop(frozen,code):
 b=body(frozen,'query_loop');a=b.index('match state');b=b[a:];b=b[:b.rfind('}')].rstrip()
 expected=b.replace('Err(error) => return Err(error),','Err(error)=>Step::Done(Err(error)),').replace('return Ok((a, pending));','return Step::Done(Ok((a,pending)));').replace('state = query_values(proof, p, a, g, obs, geometry, pending);','let state=child(proof,p,a,g,obs,geometry,pending,c);Step::Continue(state)')
 actual=body(code,'NFP_step')
 assert tok(expected)==tok(actual),'exact loop step erasure differs'
 return dict(loop_erasure_exact=True,frozen_body_sha256=hashlib.sha256(body(frozen,'query_loop').encode()).hexdigest(),native_body_sha256=hashlib.sha256(actual.encode()).hexdigest())
