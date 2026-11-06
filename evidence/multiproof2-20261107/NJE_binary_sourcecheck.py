from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
frozen=subprocess.check_output(['git','show',revision+':crates/aspis-r1-cost-probe/src/multiproof.rs'],text=True)
harness=(E/'NJE_harness.rs').read_text()
def braced(s,start):
 i=s.index('{',start);j=i+1;depth=1
 while depth:
  depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1],j

def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*','',s))
body,_=braced(frozen,frozen.index('while i < n',frozen.index('pub fn verify_in_place')))
branch,end=braced(body,body.index('Arity::Two =>'))
matchstart=body.index('match arity');_,matchend=braced(body,matchstart)
body=body[:matchstart]+branch.strip()+body[matchend:]
body=body.replace('arity.bits()','Arity::Two.bits()').replace('occupied_binary_parent(hash,','NJE_row_occupied(log,').replace('sibling_binary_parent(hash,','NJE_row_sibling(log,')
actual,_=braced(harness,harness.index('if *i<n',harness.index('fn NJE_binary_row(')))
actual=actual.replace('super::','');actual=re.sub(r'\*(i|w|at)\b',r'\1',actual)
assert tokens(body)==tokens(actual), 'source fission differs beyond reviewed substitutions'
(E/'NJE_BINARY_SOURCE_ASSOCIATION.json').write_text(json.dumps({'revision':revision,'frozen_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'cut_body_sha256':hashlib.sha256(actual.encode()).hexdigest(),'token_erasure_equal':True,'substitutions':['binary constructor specialization; Eight branch unreachable on adopted binary domain','callee occupied/sibling -> local SAME-slice call logs, raw reply unchanged','one guarded native iteration, i/w/at local scalars passed by reference'],'callee_prestate':'arbitrary coordinate/byte assertion inside each call log, pointer+index retained; native returned digest raw byte32','whole_buffer_loop':False},indent=2)+'\n')
print('Binary one-step cut source association checked.')
