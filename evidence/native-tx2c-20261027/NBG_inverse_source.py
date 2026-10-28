"""Audit the frozen inverse's fixed scalar-call DAG against its reused model.
No Rust/Lean source, runtime dictionary or source-to-ELF theorem is generated.
"""
from pathlib import Path
import re,json,subprocess,hashlib
E=Path(__file__).resolve().parent
f=next(x for x in json.loads((E/'NBG_TARGETS.json').read_text())['functions'] if x['name']=='M31::inv')
src=subprocess.check_output(['git','show','4bb3b3f5:'+f['file']]);body=src[f['body_start_byte']:f['body_end_byte']].decode();assert hashlib.sha256(body.encode()).hexdigest()==f['body_sha256']
assert 'assert!(self.0 != 0, "inverse of zero");' in body
native=body.split('assert!(self.0 != 0, "inverse of zero");',1)[1]
native=re.sub(r'//[^\n]*','',native).strip().removesuffix('}').strip()
ops=[];env={'self':'self'}
def add(op,*inputs,count=None):
 n='n'+str(len(ops));d=dict(node=n,op=op,inputs=inputs)
 if count is not None:d['count']=count
 ops.append(d);return n
def expr(text):
 tokens=re.findall(r'[A-Za-z_]\w*|\d+|[().,]',text);pos=0
 assert ''.join(tokens)==re.sub(r'\s+','',text),'unrecognised native expression token'
 def eat(t):
  nonlocal pos
  assert tokens[pos]==t,(tokens,pos,t);pos+=1
 def parse():
  nonlocal pos
  name=tokens[pos];pos+=1
  if name=='square_n':
   eat('(');x=parse();eat(',');count=int(tokens[pos]);pos+=1;eat(')');x=add('square_n',x,count=count)
  else:x=env[name]
  while pos<len(tokens) and tokens[pos]=='.':
   eat('.');eat('mul');eat('(');y=parse();eat(')');x=add('mul',x,y)
  return x
 out=parse();assert pos==len(tokens),(text,tokens[pos:]);return out
statements=[s.strip() for s in native.split(';') if s.strip()]
for statement in statements[:-1]:
 m=re.fullmatch(r'let\s+(\w+)\s*=\s*(.*)',statement,re.S);assert m,statement;env[m[1]]=expr(m[2])
root=expr(statements[-1]);native_ops=ops.copy()
model_path=Path('lean/SAQ_InverseExplicitMul.lean');text=model_path.read_text();model=text.split('def field.M31.inv ',1)[1].split(':= do',1)[1].split('\n\nend AspisR1M31Inverse',1)[0].strip();lines=model.splitlines();assert lines.pop(0).strip()=='massert (self != 0#u32)'
ops=[];env={'self':'self'}
for line in lines:
 line=line.strip()
 if not line:continue
 if m:=re.fullmatch(r'let (\w+) ← mul (\w+) (\w+)',line):env[m[1]]=add('mul',env[m[2]],env[m[3]])
 elif m:=re.fullmatch(r'let (\w+) ← field.square_n mul (\w+) (\d+)#usize',line):env[m[1]]=add('square_n',env[m[2]],count=int(m[3]))
 else:
  m=re.fullmatch(r'mul (\w+) (\w+)',line);assert m,line;model_root=add('mul',env[m[1]],env[m[2]])
assert native_ops==ops and root==model_root
out=dict(native_body_sha256=f['body_sha256'],model_source=str(model_path),model_source_sha256=hashlib.sha256(model_path.read_bytes()).hexdigest(),dag=native_ops,root=root,equal=True,guard='raw self != 0',domain='r0-op-count absent; all raw u32 values; modeled zero panic retained',native_loop='NBG_K028',model_loop='NBG_SquareLoop.square_n_result',field_contract='LPf_BaseMultiply.source',full_result='NBG_InverseBridge.inverse_result',retained='Pure source/P6/compiler association and runtime; no ELF/headline adoption')
(E/'NBG_INV_SOURCE.json').write_text(json.dumps(out,indent=2)+'\n');print('inverse DAG matches:',len(ops),'ordered calls')
