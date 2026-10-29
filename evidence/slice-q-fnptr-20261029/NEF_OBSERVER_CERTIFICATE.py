"""Fail-closed finite source certificate. No Rust execution or Kani pointer verdict.
This is a narrow checker for the frozen syntax, not a general Rust analyser.
"""
from pathlib import Path
import re,json,subprocess,hashlib
E=Path(__file__).resolve().parent
ROOT=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
V='crates/aspis-r1-cost-probe/src/verifier.rs'
C='crates/aspis-r1-cost-probe/src/candidate.rs'
S='crates/aspis-r1-cost-probe/src/r1_semantic.rs'
P='programs/r1-cost-probe/src/lib.rs'
O='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
A='programs/r1-cost-probe/src/r1_pool_adapter.rs'
F='crates/aspis-core/src/field.rs'
def frozen(n):return subprocess.check_output(['git','show',REV+':'+n],cwd=ROOT,text=True)
# Retain string literals as tokens; discard comments without treating their content as code.
TOKEN=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|=>|!=|==|&&|\|\||[^\s]')
def tok(s):return [m[0] for m in TOKEN.finditer(s) if not m[0].startswith(('//','/*'))]
def functions(s):
 t=tok(s);out={};i=0
 while i<len(t):
  if t[i]!='fn' or i+2>=len(t) or not re.fullmatch('[A-Za-z_][A-Za-z_0-9]*',t[i+1]):i+=1;continue
  name=t[i+1];j=i+2
  nesting=0
  while j<len(t):
   if nesting==0 and t[j] in ['{',';']:break
   nesting+=(t[j] in ['(','['])-(t[j] in [')',']']);j+=1
  if j==len(t) or t[j]==';':i=j+1;continue
  depth=1;k=j+1
  while depth:
   assert k<len(t),'unbalanced body'
   depth+=(t[k]=='{')-(t[k]=='}');k+=1
  out.setdefault(name,[]).append((t[i:j],t[j+1:k-1]))
  i=k
 return out

def body(s,name):
 fs=functions(s)[name];assert len(fs)==1,(name,'ambiguous');return fs[0][1]
def require(a,b,label):assert a==b,label

def uses(b,var):
 """Every occurrence must be a whole call argument, never an alias or write."""
 stack=[];pairs=[]
 for i,x in enumerate(b):
  if x=='(':stack.append(i)
  elif x==')':
   assert stack,'unbalanced call';pairs.append((stack.pop(),i))
 assert not stack
 result=[]
 for i,x in enumerate(b):
  if x!=var:continue
  pairs_here=[(l,r) for l,r in pairs if l<i<r];assert pairs_here,('non-call use',var)
  l,r=min(pairs_here,key=lambda p:p[1]-p[0]);callee=b[l-1];j=l-2
  while j>=1 and b[j]=='::':callee=b[j-1]+'::'+callee;j-=2
  args=[];start=l+1;d=0
  for k in range(l+1,r):
   if b[k] in ['(','[','{']:d+=1
   elif b[k] in [')',']','}']:d-=1
   elif b[k]==',' and d==0:args.append(b[start:k]);start=k+1
  if start<r:args.append(b[start:r])
  hits=[n for n,a in enumerate(args) if a==[var]]
  assert len(hits)==1 and args[hits[0]]==[var],('non-bare argument',var,callee)
  result.append((callee,hits[0],len(args)))
 return result

EXPECTED={
 (C,'query_values'):[('mark',0,2)],
 (C,'query_loop'):[('query_values',4,7)],
 (C,'prepare'):[('crate::r1_semantic::verify_observed',3,4),('mark',0,2)],
 (C,'tx1'):[('mark',0,2),('prepare',3,5),('mark',0,2),('mark',0,2),('query_loop',4,8),('mark',0,2)],
 (C,'tx2_common'):[('mark',0,2),('mark',0,2),('query_loop',4,8),('finish_relation',3,4)],
 (C,'tx2_authenticated'):[('mark',0,2),('tx2_common',4,5)],
 (C,'tx2'):[('mark',0,2),('tx2_common',4,5)],
 (V,'finish_relation'):[('mark',0,2),('mark',0,2)],
 (S,'verify_finish'):[('mark',0,2)]*4,
 (S,'verify_observed'):[('mark',0,2),('mark',0,2),('verify_finish',4,5)],
}

def validate(src,feature_nodes):
 features={x['name']:set(x['features']) for x in feature_nodes}
 program=features['aspis-r1-cost-probe-program'];verifier=features['aspis-r1-cost-probe']
 assert {'default','custom-heap','pool-adapter','private-leaf-salts'} <= program
 assert not {'cu-profiling','no-entrypoint'} & program
 assert {'default','private-leaf-salts','optimized-terminal','program-build'} <= verifier
 assert not {'prover','audit-eight-way','detail-phases'} & verifier
 require(body(src[P],'observer'),tok('''#[cfg(feature="cu-profiling")] {Some(mark)} #[cfg(not(feature="cu-profiling"))] {None}'''),'observer constructor')
 require(body(src[V],'mark'),tok('if let Some(f)=obs {f(p);}'),'mark exact no-effect branch')
 require(body(src[S],'mark'),tok('''#[cfg(feature="detail-phases")] if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));} #[cfg(not(feature="detail-phases"))] let _=(obs,i);'''),'semantic mark release erasure')
 assert 'pub type Observer=Option<fn(Phase)>;' in src[V]
 assert '#[cfg(feature="audit-eight-way")]\n#[path="eight_way.rs"]\npub mod eight_way;' in src[V]
 assert 'pub use candidate::{parse_shape,tx1,tx2,tx2_authenticated};' in src[V]
 edges=[]
 for path in [C,V,S]:
  fs=functions(src[path]);actual={n for n,defs in fs.items() if any('obs' in h+b for h,b in defs)}
  expected={n for p,n in EXPECTED if p==path}|({'mark'} if path in [V,S] else set())
  require(actual,expected,('all observer carriers inventoried',path))
  for (p,n),want in EXPECTED.items():
   if p!=path:continue
   h,b=fs[n][0];assert len(fs[n])==1
   assert 'mut obs' not in ' '.join(h)
   require(h.count('obs'),1,('unique parameter',p,n))
   got=uses(b,'obs');require(got,want,('observer flow',p,n))
   edges.extend(dict(path=p,caller=n,callee=c,argument=i,arity=k) for c,i,k in got)
 # Root construction sites are checked on exact syntax, including the original ABI.
 require(src[P].count('observer()'),3,'all program construction sites') # definition + TX1 + inactive TX2
 require(src[O].count('observer()'),1,'one owned TX2 construction')
 require(src[A].count('observer()'),0,'no extra adapter source')
 assert 'verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)' in src[P]
 assert 'super::super::SolanaDigest,\n        super::super::observer(),' in src[O]
 require(body(src[F],'inv_with'),tok('''let norm = self.a.mul(self.a).add(self.b.mul(self.b)); let inv_norm = inverse(norm); CM31 { a: self.a.mul(inv_norm), b: self.b.neg().mul(inv_norm), }'''),'CM31 inv_with substitution source')
 inv=[b for h,b in functions(src[F])['inv'] if b==tok('self.inv_with(M31::inv)')]
 require(len(inv),1,'CM31 direct inverse backend')
 return dict(observer_value='None at reached deployed candidate/semantic/finish mark calls',edges=edges,mark_effects={'return':'unit','writes':[],'calls':[],'panic':False,'diverges':False},inv_specialisation='CM31::inv -> CM31::inv_with(M31::inv) only',batch_forwarder='outside this certificate: cm31_batch_inverse_with takes caller-supplied backend',feature_nodes=feature_nodes)

def inputs():
 s={n:frozen(n) for n in [P,O,A,V,C,S,F]}
 records=[json.loads(l) for l in (E.parent/'native-featparity-20261028/NCS_I002-stdout.log').read_text().splitlines() if l.startswith('{')]
 nodes=next(x['nodes'] for x in records if x['label']=='program-deployed')
 return s,nodes
if __name__=='__main__':
 src,nodes=inputs();out=validate(src,nodes)
 pins=json.loads((E/'NEF_SOURCE_PINS.json').read_text())
 for n,s in src.items():assert hashlib.sha256(s.encode()).hexdigest()==pins['files'][n]['sha256']
 out.update(frozen_revision=REV,source_pins_sha256=hashlib.sha256((E/'NEF_SOURCE_PINS.json').read_bytes()).hexdigest(),feature_evidence_sha256=hashlib.sha256((E.parent/'native-featparity-20261028/NCS_I002-stdout.log').read_bytes()).hexdigest(),status='STATIC SOURCE CERTIFICATE; P6 source specialisation transport retained; no composed NDT closure')
 (E/'NEF_OBSERVER_CERTIFICATE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(valid=True,edges=len(out['edges']))))
