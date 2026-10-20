#!/usr/bin/env python3
"""Validate the 1024 factored constants; not a substitute for a Lean theorem."""
import hashlib, json, pathlib, re, subprocess
repo=pathlib.Path.cwd(); source=repo/'crates/aspis-r1-cost-probe/src/fast_domain.rs'
p=2147483647; g=(2,1268011823)
def mul(a,b): return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def power(n):
 a=(1,0); b=g
 while n:
  if n&1: a=mul(a,b)
  b=mul(b,b); n>>=1
 return a
def rev9(n): return int(f'{n:09b}'[::-1],2)
text=source.read_text(); results=[]
for name in ['A','B']:
 block=re.search(r'const TABLE_'+name+r':.*?= \[(.*?)\];',text,re.S)[1]
 table=[tuple(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+)\)',block)]
 expected=[power(1024+2097152*rev9(i) if name=='A' else 4096*rev9(i)) for i in range(512)]
 assert len(table)==512 and table==expected, name
 results.append({'table':name,'entries':512,'equal':True,'formula':'g^(1024+2097152*rev9(i))' if name=='A' else 'g^(4096*rev9(i))'})
files=['crates/aspis-r1-cost-probe/src/'+x for x in ['fast_domain.rs','verifier.rs','weights.rs','transport.rs']]+['crates/aspis-core/src/r0/domain.rs']
receipt={'status':'PASS','kind':'independent arithmetic constant validation, not formal proof','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'generator':g,'modulus':p,'tables':results,'pins':{f:{'sha256':hashlib.sha256((repo/f).read_bytes()).hexdigest(),'bytes':(repo/f).stat().st_size} for f in files}}
path=pathlib.Path(__file__).with_name('table-validation.json');path.write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt,indent=2))
