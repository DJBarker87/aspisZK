"""Exact native source fission and local-record checks; never infer proof credit."""
from pathlib import Path
import json,re,hashlib,copy
E=Path(__file__).resolve().parent

def body(s,name):
 a=s.index('{',s.index('fn '+name+'('));d=1;b=a+1
 while d:
  d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|==|!=|<=|>=|\+=|[^\s]',s)
def check(payload,frozen):
 s=payload['crates/aspis-r1-cost-probe/src/NFF_dots.rs'];f=frozen['crates/aspis-r1-cost-probe/src/fast_dots.rs']
 assert not re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',s),'static'
 assert 'Option<fn' not in s and '#[kani::stub(' not in body(s,'NFF_step'),'function-pointer or hidden step stub'
 a=f.index('                let scalar',f.index('for term in start..'));b=f.index('\n            }',a)
 reconstructed=body(s,'NFF_step')
 for i in range(8):
  site=f'NFF_product(log, {i}, coefficient[{i}], scalar.0)'
  assert reconstructed.count(site)==1,('product site',i)
  reconstructed=reconstructed.replace(site,f'u64::from(coefficient[{i}]) * u64::from(scalar.0)')
 assert tok(reconstructed)==tok(f[a:b]),'main step drift'
 checked=['main-step: 8 same-operand product sites and original source order']
 if 'fn NFF_fold(' in s:
  a=f.index('            limbs[0] +=');b=f.index('\n        }',a)
  assert tok(body(s,'NFF_fold'))==tok(f[a:b]),'fold drift';checked.append('fold: 8 original shifts/masks/adds in order')
 if 'fn NFF_four(' in s:
  w=body(s,'NFF_four')
  for i in range(4):
   site=f'NFF_child(q,g,{i},log)';assert w.count(site)==1
   w=w.replace(site,f'four_dots_one(q,g,{i})')
  assert tok(w)==tok(body(f,'four_dots')),'wrapper drift';checked.append('wrapper: original 608-byte reference and four ordered same-input child calls')
 return dict(checked=checked,source_sha256=hashlib.sha256(s.encode()).hexdigest(),credit='Exact source fission only, paired native receipts and semantic association still required')
if __name__=='__main__':
 f=json.loads((E/'NFF_FROZEN.json').read_text());reports=[]
 for name in ['NFF_PAYLOAD.json','NFF_CORRECTED_PAYLOAD.json']:
  p=json.loads((E/name).read_text());result=check(p,f);mutations=[]
  key='crates/aspis-r1-cost-probe/src/NFF_dots.rs'
  for i in range(8):
   m=copy.deepcopy(p);m[key]=m[key].replace(f'NFF_product(log, {i}, coefficient[{i}], scalar.0)',f'NFF_product(log, {i}, coefficient[{(i+1)%8}], scalar.0)')
   try:check(m,f)
   except AssertionError:mutations.append(i)
  assert len(mutations)==8
  reports.append(dict(payload=name,result=result,operand_mutations_rejected=mutations))
 (E/'NFF_SOURCE_CHECKS.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports))
