"""Strict function-body token identity for Kani's exact symbol-list set.
No alpha renaming or semantic equivalence is accepted in place of identity.
Ambiguous/missing mappings fail closed. Rust tokens are parsed by tree-sitter.
"""
from pathlib import Path
import sys,re,json,hashlib
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
parser=Parser(Language(tree_sitter_rust.language()))
D=Path('evidence/pv-b3p6-20261028/resume17');x=json.loads((D/'std-reached.json').read_text())
def tokens(s):
 b=s.encode();t=parser.parse(b)
 def leaves(n):
  if n.type in ('line_comment','block_comment'):return []
  if not n.children:return [b[n.start_byte:n.end_byte].decode()]
  return [v for c in n.children for v in leaves(c)]
 return leaves(t.root_node)
def index(s):
 b=s.encode();mask=bytearray(b)
 for m in re.finditer(rb'//[^\n]*|/\*.*?\*/|r(#+)".*?"\1|"(?:\\.|[^"\\])*"',b,re.S):
  for i in range(m.start(),m.end()):
   if mask[i]!=10:mask[i]=32
 z=mask.decode('latin1');out=[]
 def endbrace(i):
  dep=1;j=i+1
  while dep and j<len(z):dep+=(z[j]=='{')-(z[j]=='}');j+=1
  return j
 scopes=[]
 for m in re.finditer(r'\b(?:impl|trait)\b',z):
  p=z.find('{',m.end())
  if p>=0:scopes.append((m.start(),endbrace(p),b[m.start():p].decode()))
 for m in re.finditer(r'\bfn\s+(\w+)\s*(?:<[^{};]*>)?\s*\(',z):
  p=z.find('{',m.end())
  if p<0:continue
  # A trait declaration ending at ';' has no body.
  if ';' in z[m.end():p] and ')' in z[m.end():p]:continue
  e=endbrace(p);ctx=[v for a,c,v in scopes if a<m.start()<e<=c]
  out.append(dict(name=m[1],start=b.count(b'\n',0,m.start())+1,end=b.count(b'\n',0,e)+1,signature=b[m.start():p].decode(),body=b[p:e].decode(),context=ctx))
 return out
indices={};files={};rows=[]
for rel,r in x['files'].items():
 if 'error'in r:continue
 p=D/'std-sources'/rel
 a=p.with_suffix(p.suffix+'.kani').read_text();b=p.with_suffix(p.suffix+'.deployed').read_text()
 assert hashlib.sha256(a.encode()).hexdigest()==r['kani_source_sha256'];assert hashlib.sha256(b.encode()).hexdigest()==r['deployed_source_sha256']
 indices[rel]=(index(a),index(b));files[rel]=dict(kani_sha256=r['kani_source_sha256'],deployed_sha256=r['deployed_source_sha256'])
for item in x['rows']:
 row=dict(item);rel=item['source'];name=item['name'].split('::')[-1];line=int(item['location'].get('line','0'))
 if rel not in indices:row['status']='MISSING SOURCE';rows.append(row);continue
 aa,bb=indices[rel];candidates=[f for f in aa if f['start']<=line<=f['end']]
 named=[f for f in candidates if f['name']==name]
 if named:candidates=named
 if not candidates:row['status']='UNRESOLVED KANI ITEM';rows.append(row);continue
 size=min(f['end']-f['start']for f in candidates);candidates=[f for f in candidates if f['end']-f['start']==size]
 if len(candidates)!=1:row['status']='AMBIGUOUS KANI ITEM';rows.append(row);continue
 a=candidates[0];bs=[f for f in bb if f['name']==a['name']and tokens(f['signature'])==tokens(a['signature'])]
 if len(bs)>1:
  scoped=[f for f in bs if [tokens(t)for t in f['context']]==[tokens(t)for t in a['context']]]
  if scoped:bs=scoped
 row['kani_item']=a
 if len(bs)==1:
  row['deployed_item']=bs[0];row['status']='IDENTICAL'if tokens(a['body'])==tokens(bs[0]['body'])else'DIFFERENT'
 elif bs and all(tokens(f['body'])==tokens(a['body'])for f in bs):row['status']='IDENTICAL';row['all_candidate_bodies_identical']=True;row['deployed_candidates']=bs
 else:row['status']='UNRESOLVED DEPLOYED ITEM';row['deployed_candidates']=bs
 row['intrinsics']=sorted(set(re.findall(r'\bintrinsics::(\w+)',a['body'])))
 rows.append(row)
groups={}
for g in sorted({r['group']for r in rows}):
 rr=[r for r in rows if r['group']==g];groups[g]=dict(symbol_entries=len(rr),unique_standard_items=len({(r['name'],r['source'],r['location'].get('line'))for r in rr}),counts={s:sum(r['status']==s for r in rr)for s in sorted({r['status']for r in rr})},parity_pass=all(r['status']=='IDENTICAL'for r in rr),blocking_items=sorted({r['name']+' ['+r['status']+']'for r in rr if r['status']!='IDENTICAL'}),intrinsics=sorted({v for r in rr for v in r.get('intrinsics',[])}))
out=dict(method='Strict tree-sitter leaf tokens of the complete body at each code-symbol source span; exact signature and enclosing source context select overloads. No renaming, inference or semantic substitute.',source_authority=x['source_recovery'],bundled_compiler=x['actual_bundled_rustc'],compiler_intrinsic_boundary='V370 / owner D381,D386 retained; intrinsic names recorded, no new T field',files=files,groups=groups,rows=rows)
(D/'STD-PARITY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({g:{k:v for k,v in r.items()if k not in ('blocking_items','intrinsics')}for g,r in groups.items()},indent=2))
