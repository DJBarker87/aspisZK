from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
sources=json.loads((E/'KDX_SOURCE_SNAPSHOTS.json').read_text())['sources'];rows=json.loads((E/'KDX_PASS_INVENTORY.json').read_text())
def functions(t):
 # Explicitly expand the two macro families used by LPi; this is inspection only.
 for macro,prefix,bound,stub in [('qcase','check_q',18,'cbytes'),('ccase','check_c',10,'mbytes')]:
  for m in list(re.finditer(macro+r'!\((\w+),(\d+),(\d+)\);',t)):
   t+='\n#[kani::proof] #[kani::stub(X,'+stub+')] #[kani::unwind('+str(bound)+')] fn '+m[1]+'(){'+prefix+'::<'+m[2]+','+m[3]+'>();}\n'
 for macro,stub in [('kproof','qbytes'),('eproof','ebytes')]:
  for m in list(re.finditer(macro+r'!\((\w+),\{(.*?)\}\);',t,re.S)):
   t+='\n#[kani::proof] #[kani::stub(X,'+stub+')] #[kani::unwind(1740)] fn '+m[1]+'(){'+m[2]+'}\n'
 out={}
 for m in re.finditer(r'\bfn\s+(\w+)\s*(?:<[^{};]*>)?\s*\(',t):
  start=t.find('{',m.end());end=t.find(';',m.end())
  if start<0:continue
  depth=1;i=start+1
  while depth and i<len(t):
   if t[i]=='{':depth+=1
   if t[i]=='}':depth-=1
   i+=1
  # Attributes extend from previous definition ending or blank line (allow stubs).
  prev=max(t.rfind('}',0,m.start()),t.rfind(';',0,m.start()))
  attrs=t[prev+1:m.start()]
  out[m[1]]=dict(body=t[m.start():i],attrs=attrs)
 return out
out=[];review=[]
for row in rows:
 fs={};where={}
 for sha in (row.get('source_hashes') or {}).values():
  if sha in sources:
   for k,v in functions(sources[sha]['text']).items():fs[k]=v;where[k]=sources[sha]['path']
 for h in row['harnesses']:
  name=h.split('::')[-1];f=fs.get(name)
  if not f:review.append(dict(receipt=row['receipt'],harness=h,reason='definition missing'));continue
  seen=set();todo=[name]+[v for v in re.findall(r'kani::stub\([^,]+,([^)]*)\)',f['attrs']) for v in [v.strip().split('::')[-1]] if v in fs]
  while todo:
   k=todo.pop()
   if k in seen:continue
   seen.add(k)
   for call in re.findall(r'\b(\w+)\b',fs[k]['body']):
    if call in fs and call not in seen:todo.append(call)
  marks=[]
  for k in sorted(seen):
   b=fs[k]['body']
   copy=re.findall(r'.{0,45}(?:copy_from_slice|clone_from_slice|copy_nonoverlapping|to_vec|extend_from_slice|ptr::copy|\.clone\().{0,70}',b)
   loops=re.findall(r'.{0,15}(?:\bfor\s+\w+\s+in|\bwhile\b|\.iter\(|\.into_iter\().{0,90}',b)
   if copy or loops:marks.append(dict(function=k,copies=copy,loops=loops))
  cmd=row['command'];bound=None
  for opt in ['--default-unwind','--unwind']:
   if opt in cmd:bound=int(cmd[cmd.index(opt)+1])
  attr=re.findall(r'kani::unwind\((\d+)\)',f['attrs'])
  if attr and '--unwind' not in cmd:bound=int(attr[-1])
  out.append(dict(receipt=row['receipt'],harness=h,bound=bound,disabled=any(x in cmd for x in ['--no-unwinding-checks','--no-default-checks']),marks=marks,source=where[name],attrs=f['attrs'],body=f['body'],reachable=sorted(seen),command=cmd))
(E/'KDX_HARNESS_SCAN.json').write_text(json.dumps(out,indent=2)+'\n');(E/'KDX_SCAN_REVIEW.json').write_text(json.dumps(review,indent=2)+'\n')
print('matched',len(out),'missing',len(review),'memory/loops',sum(bool(x['marks']) for x in out))
with (E/'KDX_SCAN.txt').open('w') as f:
 for r in out:
  if r['marks']:f.write(r['receipt']+' '+r['harness']+' unwind='+str(r['bound'])+' disabled='+str(r['disabled'])+'\n'+json.dumps(r['marks'])+'\n')
