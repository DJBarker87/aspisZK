"""Refine exact reached std mappings without weakening body token identity.
No compiler runs. Preserve prior evidence. Compiler-generated items fail closed.
"""
from pathlib import Path
import re,json,hashlib,sys
sys.path.insert(0,'/private/tmp/pv-d540-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
parser=Parser(Language(tree_sitter_rust.language()))
D=Path('evidence/pv-b3p6-20261028/resume17')
def tokens(s):
 b=s.encode();root=parser.parse(b).root_node
 def leaf(n):
  if n.type in ('line_comment','block_comment'):return []
  if not n.children:return [b[n.start_byte:n.end_byte].decode()]
  return [v for c in n.children for v in leaf(c)]
 return leaf(root)
def index(s):
 b=s.encode();z=bytearray(b)
 # Tree-sitter supplies comment/string spans, including raw strings; preserve offsets.
 def erase(n):
  if n.type in ('line_comment','block_comment','string_literal','raw_string_literal','char_literal'):
   for k in range(n.start_byte,n.end_byte):
    if z[k]!=10:z[k]=32
  else:
   for c in n.children:erase(c)
 erase(parser.parse(b).root_node);z=z.decode('latin1')
 def endbrace(i):
  depth=1;j=i+1
  while depth and j<len(z):depth+=(z[j]=='{')-(z[j]=='}');j+=1
  return j
 macros=[]
 for m in re.finditer(r'\bmacro_rules!\s*(\w+)',z):
  p=z.find('{',m.end());macros.append((m.start(),endbrace(p),m[1]))
 scopes=[]
 for m in re.finditer(r'\b(?:impl|trait)\b',z):
  p=z.find('{',m.end())
  if p>=0:scopes.append((m.start(),endbrace(p),b[m.start():p].decode()))
 out=[]
 for m in re.finditer(r'\bfn\s+(\w+)\b',z):
  p=m.end();bracket=paren=0
  while p<len(z):
   c=z[p]
   if c=='{':break
   if c==';' and bracket==0 and paren==0:break
   bracket+=(c=='[')-(c==']');paren+=(c=='(')-(c==')');p+=1
  if p==len(z) or z[p]!='{':continue
  e=endbrace(p)
  out.append(dict(name=m[1],start=b.count(b'\n',0,m.start())+1,end=b.count(b'\n',0,e)+1,signature=b[m.start():p].decode(),body=b[p:e].decode(),context=[v for a,c,v in scopes if a<m.start()<e<=c],macros=[v for a,c,v in macros if a<m.start()<e<=c]))
 return out
# Only normalize const eligibility in source-context matching, NEVER body tokens.
def context_key(f):
 return [tokens(re.sub(r'\bconst\b','',s)) for s in f['context']]
indices={}
for name in ['STD-PARITY.json','K3-STD-PARITY.json']:
 old=json.loads((D/name).read_text());rows=[]
 for row in old['rows']:
  r=dict(row);rel=r['source']
  if rel not in indices:
   p=D/'std-sources'/rel
   aa=p.with_suffix(p.suffix+'.kani').read_bytes();bb=p.with_suffix(p.suffix+'.deployed').read_bytes()
   assert hashlib.sha256(aa).hexdigest()==old['files'][rel]['kani_sha256']
   assert hashlib.sha256(bb).hexdigest()==old['files'][rel]['deployed_sha256']
   indices[rel]=(index(aa.decode()),index(bb.decode()))
  aa,bb=indices[rel]
  if re.search(r'::runtime(?:$|::)',r['name']):
   r['status']='COMPILER-GENERATED / UNRESOLVED';r['classification']='V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity';rows.append(r);continue
  line=int(r['location'].get('line',0));cand=[f for f in aa if f['start']<=line<=f['end']]
  if cand:
   size=min(f['end']-f['start'] for f in cand);cand=[f for f in cand if f['end']-f['start']==size]
  if len(cand)!=1:
   r['status']='COMPILER-GENERATED / UNRESOLVED';r['classification']='V370 compiler-cohort item (owner D381/D386); source body not established';r['resolution_candidates']=cand;rows.append(r);continue
  a=cand[0];bs=[f for f in bb if f['name']==a['name'] and f['macros']==a['macros'] and context_key(f)==context_key(a)]
  # Exact signature resolves overloads within an enclosing impl/macro.
  exact=[f for f in bs if tokens(f['signature'])==tokens(a['signature'])]
  if exact:bs=exact
  if not bs and rel=='core/src/array/drain.rs' and a['name']=='drop':
   bs=[f for f in bb if f['name']=='drop'];assert len(bs)==1
  if not bs and rel=='core/src/array/mod.rs' and a['name']=='drop' and any("Guard<'_" in c for c in a['context']):
   bs=[f for f in bb if f['name']=='drop' and any("Guard<'_" in c for c in f['context'])];assert len(bs)==1
  r['kani_item']=a;r['deployed_candidates']=bs
  if bs and (len(bs)==1 or all(tokens(f['body'])==tokens(bs[0]['body']) for f in bs)):
   r['deployed_item']=bs[0];r['status']='IDENTICAL' if tokens(a['body'])==tokens(bs[0]['body']) else 'DIFFERENT'
   r['mapping']='same declaration name, enclosing impl/trait and macro; const eligibility ignored only in context; body tokens unchanged'
   r['signature_identical']=tokens(a['signature'])==tokens(bs[0]['signature'])
  else:
   r['status']='ABSENT DEPLOYED DECLARATION' if not any(f['name']==a['name'] for f in bb) else 'UNRESOLVED DEPLOYED ITEM'
   if rel=='core/src/slice/cmp.rs' and a['name'] in ('ne','not_equal'):r['status']='ABSENT DEPLOYED DECLARATION' # exact SlicePartialEq / PartialEq<[U]> contexts removed; retained default PartialEq::ne requires a distinct binding
   r['same_name_deployed_contexts']=[dict(name=f['name'],start=f['start'],context=f['context']) for f in bb if f['name']==a['name']]
  r['intrinsics']=sorted(set(re.findall(r'\bintrinsics::(\w+)',a['body'])))
  if re.search(r'::\{closure#\d+\}$',r['name']):
   r['comparison_unit']='enclosing source function; generated closure requires compiler lowering evidence, not just identical enclosing tokens'
   r['status']='COMPILER-GENERATED / SOURCE CHANGED' if r['status']=='DIFFERENT' else 'COMPILER-GENERATED / UNRESOLVED'
  r['classification']=('V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity' if re.search(r'::\{closure#\d+\}$',r['name']) else 'ordinary standard-library source item')
  rows.append(r)
 groups={}
 for g in sorted({r['group'] for r in rows}):
  rr=[r for r in rows if r['group']==g];groups[g]=dict(counts={s:sum(r['status']==s for r in rr) for s in sorted({r['status'] for r in rr})},parity_pass=all(r['status']=='IDENTICAL' for r in rr),blocking_items=sorted({r['name']+' ['+r['status']+']' for r in rr if r['status']!='IDENTICAL'}))
 out=dict(prior_report=name,prior_sha256=hashlib.sha256((D/name).read_bytes()).hexdigest(),method=__doc__,files=old['files'],compiler_boundary='V370 compiler-cohort items; owner D381/D386; retained, not discharged',groups=groups,rows=rows)
 dest=D/(name.removesuffix('.json')+'-D540.json');dest.write_text(json.dumps(out,indent=2)+'\n')
 print(dest,[(g,v['counts']) for g,v in groups.items()])
