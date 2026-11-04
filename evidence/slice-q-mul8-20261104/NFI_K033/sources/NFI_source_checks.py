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
 s=payload['crates/aspis-r1-cost-probe/src/NFI_dots.rs'];f=frozen['crates/aspis-r1-cost-probe/src/fast_dots.rs']
 assert not re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',s),'static'
 assert 'Option<fn' not in s and '#[kani::stub(' not in body(s,'NFI_step'),'function-pointer or hidden step stub'
 a=f.index('                let scalar',f.index('for term in start..'));b=f.index('\n            }',a)
 reconstructed=body(s,'NFI_step')
 for i in range(8):
  site=f'NFI_product(log, {i}, coefficient[{i}], scalar.0)'
  assert reconstructed.count(site)==1,('product site',i)
  reconstructed=reconstructed.replace(site,f'u64::from(coefficient[{i}]) * u64::from(scalar.0)')
 assert tok(reconstructed)==tok(f[a:b]),'main step drift'
 checked=['main-step: 8 same-operand product sites and original source order']
 if 'fn NFI_fold(' in s:
  a=f.index('            limbs[0] +=');b=f.index('\n        }',a)
  assert tok(body(s,'NFI_fold'))==tok(f[a:b]),'fold drift';checked.append('fold: 8 original shifts/masks/adds in order')
 if 'fn NFI_four(' in s:
  w=body(s,'NFI_four')
  for i in range(4):
   site=f'NFI_child(q,g,{i},log)';assert w.count(site)==1
   w=w.replace(site,f'four_dots_one(q,g,{i})')
  assert tok(w)==tok(body(f,'four_dots')),'wrapper drift';checked.append('wrapper: original 608-byte reference and four ordered same-input child calls')
 if 'fn NFI_select_tail(' in s:
  select=body(s,'NFI_select_tail')
  expected="""match call {
  0 => (g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()),
  1 => {let offset0=480+slot*32+0*16;(g[0+26],QM31::from_le_bytes(&q[offset0..offset0+16]).unwrap())},
  _ => {let offset1=480+slot*32+1*16;(g[1+26],QM31::from_le_bytes(&q[offset1..offset1+16]).unwrap())}
 }"""
  assert tok(select)==tok(expected),'tail decoder window drift'
  for text in ['g[28]','g[0+26]','g[1+26]','slot*120+104..slot*120+120','480+slot*32+0*16','480+slot*32+1*16']:
   assert ''.join(tok(text)) in ''.join(tok(f)),'frozen tail selection differs'
  checked.append('tail selection: one actual parser/coefficient at arbitrary call and slot')
 if 'fn NFI_head(' in s:
  a=f.index('        let mut value =');b=f.index('        let mut tail=',a)
  expected=f[a:b].replace('let mut value =','let value =')+'value'
  assert tok(body(s,'NFI_head'))==tok(expected),'head reduction/constructor drift'
  checked.append('head: exact eight reductions, constructor and returned value')
 if 'crates/aspis-r1-cost-probe/src/NFI_incoming.rs' in payload:
  incoming=payload['crates/aspis-r1-cost-probe/src/NFI_incoming.rs']
  candidate=frozen['crates/aspis-r1-cost-probe/src/candidate.rs']
  a=candidate.index('    let i = a.next;',candidate.index('fn query_values('))
  b=candidate.index('    crate::trace::value',a)
  prefix=candidate[a:b].replace('a.next','next').replace('p.queries','queries')
  prefix=prefix.replace('    let q = opening(proof, i);\n','').replace('crate::fast_dots::four_dots(q, g)','NFI_dots(q,g,log)')
  assert tok(body(incoming,'NFI_prefix'))==tok(prefix+'(i,u,dots)'),'query prefix fission drift'
  assert 'if folded != values[u % 4]' in candidate
  assert tok('if folded!=values[u%4]{return Err(Error::Query);}')==tok(body(incoming,'NFI_guard').split('*calls')[0]),'query guard drift'
  assert 'let node = z.mul(z).double().sub(M31::ONE);' in candidate
  assert 'let node=NFI_mul(z,z,&mut log).double().sub(M31::ONE);' in incoming
  assert not re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',incoming),'incoming static'
  assert 'Option<fn' not in incoming,'incoming function pointer'
  checked.append('incoming: exact query prefix modulo named opening cut; actual guard, node continuation and field/window context. Original whole-proof binding remains OPEN')
 if 'crates/aspis-r1-cost-probe/src/NFI_pairing.rs' in payload:
  pair=payload['crates/aspis-r1-cost-probe/src/NFI_pairing.rs'];frozenPair=frozen['crates/aspis-r1-cost-probe/src/fast_pairing.rs']
  sites=json.loads((E/'NFI_RAW_SITES.json').read_text())['sites']
  raw=body(pair,'NFI_raw').replace('left.0','self.0')
  for i,(a,b) in enumerate(sites):
   site=f'NFI_product(log,{i},{a},{b})';assert raw.count(site)==1
   raw=raw.replace(site,a+'*'+b)
  assert tok(raw)==tok(body(frozenPair,'raw')),'raw arithmetic drift'
  step=body(pair,'NFI_dot_step').replace('dot.sums','self.sums')
  original=body(frozenPair[frozenPair.index('impl Dot {'):],'push')
  a=original.index('self.sums[j]');b=original.index(';',a)+1
  assert tok(step)==tok(original[a:b]),'private loop step drift'
  if 'fn NFI_public_push(' in pair:
   public=body(pair,'NFI_public_push').replace('receiver.','self.')
   for i in range(2):public=public.replace(f'NFI_private_push(log,{i},&mut self.c{i},value_c{i},scalar);',f'self.c{i}.push(value_c{i}, scalar);')
   assert tok(public)==tok(body(frozenPair[frozenPair.index('impl EbyKDot {'):],'push')),'public push drift'
  if 'fn NFI_tail(' in pair:
   tail=body(pair,'NFI_tail')
   for i in range(3):
    a=tail.index('NFI_public_push(&mut tail,');b=tail.index(f',&mut logs[{i}]).unwrap();',a)
    tail=tail[:a]+'tail.push('+tail[a+len('NFI_public_push(&mut tail,'):b]+').unwrap();'+tail[b+len(f',&mut logs[{i}]).unwrap();'):]
   a=f.index('        let mut tail=');b=f.index('\n    \n}',a)
   assert tok(tail)==tok(f[a:b]),'tail call-order or argument drift'
  checked.append('pairing: all 16 raw product sites, exact native private step, exact public checks when present')
 return dict(checked=checked,source_sha256=hashlib.sha256(s.encode()).hexdigest(),credit='Exact source fission only, paired native receipts and semantic association still required')
if __name__=='__main__':
 f=json.loads((E/'NFI_FROZEN.json').read_text());reports=[]
 for name in ['NFI_PAYLOAD.json','NFI_CORRECTED_PAYLOAD.json','NFI_ORDERED_PAYLOAD.json','NFI_PAIRING_PAYLOAD.json','NFI_PUBLIC_PAYLOAD.json','NFI_PUBLIC_FIXED_PAYLOAD.json','NFI_TAIL_PAYLOAD.json','NFI_TAIL_SPLIT_PAYLOAD.json','NFI_ARGUMENT_PAYLOAD.json']:
  p=json.loads((E/name).read_text());result=check(p,f);mutations=[]
  key='crates/aspis-r1-cost-probe/src/NFI_dots.rs'
  for i in range(8):
   m=copy.deepcopy(p);m[key]=m[key].replace(f'NFI_product(log, {i}, coefficient[{i}], scalar.0)',f'NFI_product(log, {i}, coefficient[{(i+1)%8}], scalar.0)')
   try:check(m,f)
   except AssertionError:mutations.append(i)
  assert len(mutations)==8
  reports.append(dict(payload=name,result=result,operand_mutations_rejected=mutations))
 (E/'NFI_SOURCE_CHECKS.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports))
