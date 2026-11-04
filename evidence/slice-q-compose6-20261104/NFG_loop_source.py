"""Exact frozen control-body/fission checks. No theorem or native credit by itself."""
from pathlib import Path
import re,subprocess,hashlib,json
E=Path(__file__).resolve().parent
norm=lambda s:re.sub(r'\s+','',s)
def body(source,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\(',source);assert m,name
 i=source.index('{',m.end());start=i;i+=1;depth=1
 while depth:
  if source[i]=='{':depth+=1
  elif source[i]=='}':depth-=1
  i+=1
 return source[start:i]
def check(actual=None,payload=None):
 if actual is None:actual=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs'],cwd=E.parent.parent,text=True)
 if payload is None:payload=(E/'NFG_loop.rs.txt').read_text()
 frozen='''{let mut state = Ok((a, pending));loop {match state {Err(error) => return Err(error),Ok((a, pending)) => {if a.next >= end {return Ok((a, pending));}state = query_values(proof, p, a, g, obs, geometry, pending);}}}}'''
 expected='''{match state {Err(error) => Step::Done(Err(error)),Ok((a, pending)) => {if a.next >= end {return Step::Done(Ok((a, pending)));}let state=oracle.call(proof,p,a,g,geometry,pending);Step::Continue(state)}}}'''
 assert norm(body(actual,'query_loop'))==norm(frozen),'frozen loop control changed'
 assert norm(body(payload,'NFG_step'))==norm(expected),'native step changed'
 assert not re.search(r'\b(static|unsafe)\b',payload),'writable-static/unsafe exposure'
 assert 'Observer' not in payload and 'fn(Phase)' not in payload,'function-pointer exposure'
 assert 'oracle.call(proof,p,a,g,geometry,pending)' in norm(payload)
 return dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_source_sha256=hashlib.sha256(actual.encode()).hexdigest(),native_source_sha256=hashlib.sha256(payload.encode()).hexdigest(),source_body='query_loop',native_body='NFG_step',method='one arbitrary-state native iteration; match body with Step done/cont, fixed None observer forwarding under ruling z; local full-carrier oracle',status='source association only; root packet remains OPEN')
if __name__=='__main__':
 (E/'NFG_LOOP_SOURCE.json').write_text(json.dumps(check(),indent=2)+'\n')
