#!/usr/bin/env python3
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];REV='b2727acd3abf79315d18b754a260f58f4b1c6326'
B=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
get=lambda p:subprocess.check_output(['git','-C',str(R),'show',REV+':'+p],text=True)
paths=['crates/aspis-r1-cost-probe/src/compact.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs']
src={p:get(p) for p in paths};defs={};owners={}
for p in paths[:2]:
 for m in re.finditer(r'pub const (\w+)\s*:\s*usize\s*=\s*([^;]+);',src[p]):
  if m[1] in defs:continue
  defs[m[1]]=m[2].strip();owners[m[1]]=dict(path=p,source=m[0],source_sha256=hashlib.sha256(src[p].encode()).hexdigest())
values={};used={};ops=[]
def value(name):
 if name in values:return values[name]
 expr=defs[name].replace('crate::verifier::SEMANTIC_BYTES','SEMANTIC_BYTES')
 def run(n):
  if isinstance(n,ast.Constant) and type(n.value)==int:r=n.value
  elif isinstance(n,ast.Name):r=value(n.id)
  elif isinstance(n,ast.BinOp):
   a,b=run(n.left),run(n.right)
   if isinstance(n.op,ast.Add):r=a+b
   elif isinstance(n.op,ast.Sub):r=a-b
   elif isinstance(n.op,ast.Mult):r=a*b
   else:raise AssertionError(ast.dump(n))
   ops.append(dict(expression=ast.unparse(n),left=a,right=b,result=r))
  else:raise AssertionError(ast.dump(n))
  assert 0<=r<=2**32-1,(name,r)
  return r
 v=run(ast.parse(expr,mode='eval').body);values[name]=v;used[name]=owners[name];return v
expected={'HEADER':16,'COMPACT_SEMANTIC':7015,'COMPACT_Y1':464,'SEMANTIC_BYTES':13831,'OFF_ROUND0':7527,'OFF_SEMANTIC':16,'OFF_Y1':7031,'OFF_INACTIVE':7495,'LOGICAL_SEMANTIC':13831,'LOGICAL_Y1':928,'OFF_FOLDED_ROOT':7751,'OFF_ROUND1':7783,'SPLIT':10}
for n,v in expected.items():assert value(n)==v,(n,values[n])
# Exact source ZERO constructor chain: no arithmetic or hidden callback.
f=src[paths[2]]
zero=[]
for ty in ['M31','CM31','QM31']:
 m=re.search(r'pub const ZERO:\s*'+ty+r'\s*=\s*([\s\S]*?);',f);assert m,ty
 zero.append(dict(type=ty,source=m[0]))
assert re.sub(r'\s+','',zero[0]['source'])=='pubconstZERO:M31=M31(0);'
assert re.sub(r'\s+','',zero[1]['source'])=='pubconstZERO:CM31=CM31{a:M31(0),b:M31(0),};'
assert re.sub(r'\s+','',zero[2]['source'])=='pubconstZERO:QM31=QM31{c0:CM31{a:M31(0),b:M31(0),},c1:CM31{a:M31(0),b:M31(0),},};'
m=re.search(r'pub const ZERO:\s*Self\s*=\s*([\s\S]*?);',src[paths[3]]);assert m
assert re.sub(r'\s+','',m[0])=='pubconstZERO:Self=Self{c0:QM31::ZERO,c1:QM31::ZERO,};'
mapper=re.search(r'impl From<CodecError> for Error \{[\s\S]*?\n\}',get('crates/aspis-r1-cost-probe/src/candidate.rs'))[0]
assert re.sub(r'\s+','',mapper)=='implFrom<CodecError>forError{fnfrom(_:CodecError)->Self{Error::Parse}}'
out=dict(schema='focused-extractor-proof-packet-v1',freeze=REV,source_constants=used,values=values,arithmetic_nodes=ops,machine_bound=2**32-1,zero_constructor_chain=zero+[dict(type='WideExact',source=m[0])],codec_error_mapper=mapper,classification='Exact source expression/leaf inventory, checked scalar execution is proved in CurrentCompactCallerConstantsV1.constants_total; not whole-caller TOTAL')
text=json.dumps(out,indent=2)+'\n';p=B/'source-constant-pins.json'
if '--check' in sys.argv:assert p.read_text()==text
else:p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
print('PASS source constant DAG and zero/error constructors')
