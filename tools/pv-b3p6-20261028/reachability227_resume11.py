"""Conservative, exhaustive inventory classification; absent symbols never prove dead code.
Source identifier supergraph includes method/function-value edges, all same-name targets,
and cfg-selected nested items. MIR inlined scopes and optimized LLVM are supporting witnesses.
Unknown external callbacks remain explicit obligations rather than deleted edges.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'resume11';inv=json.loads((D/'resume9/body-inventory.json').read_text())
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def toks(s):return [(m[0],m.start(),m.end())for m in lex.finditer(s)if not m[0].startswith(('//','/*'))]
def end(ts,i,left,right):
 depth=1;j=i+1
 while depth:depth+=(ts[j][0]==left)-(ts[j][0]==right);j+=1
 return j
def truth(ts):
 p=0
 def go():
  nonlocal p
  t=ts[p];p+=1
  if t=='test':return False
  if t in ['feature','target_os']:
   assert ts[p]=='=';p+=1;v=ts[p].strip('"');p+=1
   if t=='target_os':return v=='linux'
   assert v in ['optimized-terminal','prover','r0','ct-host-prover','r0-op-count','r0-r91-audit','r0-e4-reference'],v
   return v in ['prover','r0','ct-host-prover']
  assert t in ['any','all','not'],t
  assert ts[p]=='(';p+=1;a=[]
  while ts[p]!=')':
   a.append(go())
   if ts[p]==',':p+=1
  p+=1
  return any(a)if t=='any'else all(a)if t=='all'else not a[0]
 r=go();assert p==len(ts);return r

def configured(s):
 ts=toks(s);removed=[]
 for i in range(len(ts)-3):
  if [t[0]for t in ts[i:i+4]]!=['#','[','cfg','(']:continue
  k=end(ts,i+3,'(',')');expr=[t[0]for t in ts[i+4:k-1]]
  if truth(expr):continue
  j=k+1
  while ts[j][0]not in ['{',';']:j+=1
  stop=end(ts,j,'{','}')if ts[j][0]=='{'else j+1
  removed.append((ts[i][1],ts[stop-1][2],''.join(expr)))
 chars=list(s)
 for a,b,_ in removed:
  for i in range(a,b):
   if chars[i]!='\n':chars[i]=' '
 return ''.join(chars),removed

files={r['family']:r for r in inv['files']};source={};owned={};nodes={};rows=[]
for fam,f in files.items():
 for side,cache in [('source',source),('owned',owned)]:
  p=Path(f[side]);s=p.read_text();cfg,removed=configured(s);cache[fam]=(s,cfg,removed)
for i,r in enumerate(inv['bodies']):
 for side,cache in [('source',source),('owned',owned)]:
  b=r[side]
  if not b:continue
  fam=r['family'];s,cfg,removed=cache[fam]
  if b.get('source_file'):
   s=Path(b['source_file']).read_text();cfg,removed=configured(s)
  a=sum(len(l)for l in s.splitlines(keepends=True)[:b['line']-1]);z=sum(len(l)for l in s.splitlines(keepends=True)[:b['end_line']]);chunk=cfg[a:z]
  disabled=any(x<=a<y for x,y,_ in removed)
  # Macro templates are accounted for as enclosing source text, not callable bodies.
  template=b['name']=='$'
  key=f'{side}:{fam}:{r["key"]}'
  nodes[key]=dict(inventory_index=i,name=b['name'],disabled=disabled,template=template,identifiers=sorted(set(v for v,_,_ in toks(chunk) if re.fullmatch(r'[A-Za-z_]\w*',v))),source_line=b['line'],cfg_exclusions=[dict(start=x,end=y,expression=e)for x,y,e in removed if x<=a<y])

def graph(side,roots):
 active={k:v for k,v in nodes.items()if k.startswith(side+':')and not v['disabled']and not v['template']};byname={}
 for k,v in active.items():byname.setdefault(v['name'],[]).append(k)
 reached=set(roots);parent={k:None for k in roots};queue=list(roots)
 while queue:
  k=queue.pop(0)
  for name in active[k]['identifiers']:
   for v in byname.get(name,[]):
    if v not in reached:reached.add(v);parent[v]=k;queue.append(v)
 return active,reached,parent
sa,sr,sp=graph('source',['source:terminal:terminal_qm31#0'])
oa,orr,op=graph('owned',['owned:terminal:reference227#0'])
for i,r in enumerate(inv['bodies']):
 key='source:'+r['family']+':'+r['key'];ok='owned:'+r['family']+':'+r['key'];node=nodes.get(key);path=[];p=key
 if p in sr:
  while p is not None:path.append(p);p=sp[p]
  path.reverse()
 state='reachable-conservative'if key in sr else 'owned-support'if not node else 'cfg-excluded'if node['disabled']else'macro-template'if node['template']else'unreachable-source-supergraph'
 rows.append(dict(inventory_index=i,family=r['family'],key=r['key'],status=r['status'],classification=state,source_path=path,source_node=node,owned_reached=ok in orr,binding='pending',reason='Every identifier occurrence is an edge to every enabled same-name inventory body, including method and function-value references. No absence-of-symbol inference.'if state=='unreachable-source-supergraph'else'No deployed Rust source counterpart; reconstruction helper obligations remain with consuming changed body.'if state=='owned-support'else'cfg selection: deployed optimized-terminal=false, prover=true, test=false'if state=='cfg-excluded'else'body occurs within macro_rules template; expansion constants/control require separate binding'if state=='macro-template'else'conservative source call path; unresolved external dispatch remains in dependency closure'))
support=O/'mir-inventory-resume11.json'
mir=json.loads(support.read_text()) if support.exists() else None
if mir:
 for row,witness in zip(rows,mir['bodies'],strict=True):
  assert (row['family'],row['key'])==(witness['family'],witness['key'])
  row['deployed_support']=dict(record='mir-inventory-resume11.json',mir_occurrences=len(witness['mir_witnesses']),llvm_occurrences=len(witness['llvm_symbol_witnesses']),inlining_included=True,used_to_exclude=False)
result=dict(exhaustive_inventory_classification=True,exact_deployed_reachable_count_proved=False,closure_warning='The79 count is a conservative candidate cone, not an exact deployed-call count. Source graph covers the four inventory families; re-entry through external dependencies and macro expansion still requires whole-cone reconciliation before24 unreferenced bodies may be finally pruned. cfg-disabled bodies are excluded by deployed selection. No unmatched symbol absence is a proof of unreachability.',deployed_support_sha256=hashlib.sha256(support.read_bytes()).hexdigest() if mir else None,method='cfg-selected source identifier supergraph plus deployed optimized MIR inlining and LLVM/symbol support; conservative overapproximation',feature_authority='resume7/llvm227-features-resume7.json',deployed_features=dict(optimized_terminal=False,prover=True,test=False),roots=['source:terminal:terminal_qm31#0'],external_dispatch='Source graph does not prune external library calls or possible indirect dispatch. Complete dependency/pre-inline own-1 binding remains open.',semantic_use='reclassification within existing Charon/Aeneas tool trust',boundary='V370 compiler preservation / pending owner D381,D386 retained',inventory_sha256=hashlib.sha256((D/'resume9/body-inventory.json').read_bytes()).hexdigest(),bodies=rows,summary={c:sum(r['classification']==c for r in rows)for c in sorted(set(r['classification']for r in rows))},reachable_by_status={s:sum(r['classification']=='reachable-conservative'and r['status']==s for r in rows)for s in ['identical','changed','source-only','owned-only']})
p=O/'reachability.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==result
else:p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(summary=result['summary'],reachable_by_status=result['reachable_by_status'])))
