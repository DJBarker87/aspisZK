"""Pin native encoder/basis control shapes for the structural field route.
This is a source-shape check; the Lean recurrence transport is separate.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  elif s[i]=='}':
   d-=1
   if not d:return s[a:i+1]
 raise ValueError(needle)
expected={
'eval_pair':('crates/aspis-core/src/r0/encoder.rs','pub fn eval_pair', '''{
 let basis=basis::values::<E,512>(x); let mut p0=E::ZERO; let mut p1=E::ZERO;
 for (pair,n) in q.chunks_exact(2).zip(basis) {
 p0=p0.add(pair[0].mul(n)); p1=p1.add(pair[1].mul(n)); }
 (p0,p1)
}'''),
'eval_message':('crates/aspis-core/src/r0/encoder.rs','pub fn eval_message','''{
 let (p0,p1)=eval_pair(q,z.x); p0.add(z.y.mul(p1))
}'''),
'values':('crates/aspis-core/src/r0/basis.rs','pub(crate) fn values','''{
 let mut out=[E::ONE;N];let mut width=1;let mut factor=x;
 while width<N {for j in 0..width.min(N-width) {out[width+j]=out[j].mul(factor);}
 width*=2;factor=double(factor);} out
}'''),
'double':('crates/aspis-core/src/r0/basis.rs','pub(crate) fn double','''{
 let square=x.mul(x); square.add(square).sub(E::ONE)
}''')}
rows=[]
for n,(path,needle,exp) in expected.items():
 p=R/path;s=p.read_text();actual=body(s,needle)
 assert tokens(actual)==tokens(exp),(n,actual)
 rows.append(dict(name=n,path=path,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(actual.encode()).hexdigest(),complete_body_tokens_match=True))
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),native_shapes=rows,chained_field_arithmetic_kani=False,scope='source shape gate only; iterator, recurrence and source/native composition require kernel proofs')
(E/'encoder-native-shapes.json').write_text(json.dumps(j,indent=2)+'\n')
print('four full native bodies pinned; no Kani arithmetic gate')
