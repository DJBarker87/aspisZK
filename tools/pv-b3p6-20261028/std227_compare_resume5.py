"""Source-level comparisons; ambiguity and missing mappings remain obligations."""
import json,lzma,sys,re,hashlib
from pathlib import Path
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
parser=Parser(Language(tree_sitter_rust.language()))
D=Path('evidence/pv-b3p6-20261028');variant=sys.argv[1];capture=D/('std227-'+variant+'-resume5.json.xz');x=json.loads(lzma.open(capture).read())
def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def text(n,b):return b[n.start_byte:n.end_byte].decode()
def tokens(s):
 b=s.encode();t=parser.parse(b)
 def leaves(n):
  if n.type in ('line_comment','block_comment'):return []
  if not n.children:return [text(n,b)]
  return sum((leaves(c) for c in n.children),[])
 return leaves(t.root_node)
def index(source):
 b=source.encode();tree=parser.parse(b);mask=bytearray(b)
 for m in re.finditer(rb'//[^\n]*|/\*.*?\*/|r(#+)".*?"\1|"(?:\\.|[^"\\])*"',b,re.S):
  for i in range(m.start(),m.end()):
   if mask[i]!=10:mask[i]=32
 masked=mask.decode("latin1");out=[]
 for m in re.finditer(r'\bfn\s+(\w+)\s*(?:<[^{};]*>)?\s*\(',masked):
  start=m.start();pos=masked.find('{',m.end());
  if pos<0:continue
  header=masked[m.end():pos];depth_header=0;terminated=False
  for ch in header:
   if ch in '([':depth_header+=1
   elif ch in ')]':depth_header-=1
   elif ch==';' and depth_header<=-1:terminated=True
  if terminated:continue
  depth=1;end=pos+1
  while depth and end<len(masked):
   depth+=(masked[end]=='{')-(masked[end]=='}');end+=1
  impls=list(re.finditer(rb'\bimpl(?:\s|<)',b[:start]));ctx=[]
  if impls:
   ib=impls[-1].start();ie=b.find(b'{',ib);ctx=[b[ib:ie].decode()]
  out.append(dict(name=m[1],start=b.count(b'\n',0,start)+1,end=b.count(b'\n',0,end)+1,context=ctx,signature=b[start:pos].decode(),body=b[pos:end].decode(),item=b[start:end].decode()))
 return out

indices={p:{c:index(v['text']) for c,v in cs.items()}for p,cs in x['files'].items()};rows=[]
for d in x['declarations']:
 path=d['file'];begin=d['span']['beg']['line'];end=d['span']['end']['line'];name=d['name'].split('::')[-1]
 aa=[f for f in indices[path]['extractor'] if f['start']<=begin and f['end']>=end and f['name']==name]
 r=dict(d,status='unresolved-source-location')
 if len(aa)==1:
  a=aa[0];r['extractor']=a
  bb=[f for f in indices[path]['deployed'] if f['name']==a['name'] and tokens(f['signature'])==tokens(a['signature'])]
  if not bb and path=='core/src/convert/num.rs':
   def signature_key(t):
    t=re.sub(r'\$(\w+)',lambda m:'$'+m[1].lower(),t)
    t=re.sub(r'\bfn from\(\w+:', 'fn from(ARG:',t)
    return tokens(t)
   bb=[f for f in indices[path]['deployed'] if f['name']==a['name'] and signature_key(f['signature'])==signature_key(a['signature'])]
   r['signature_mapping']='macro formal case / argument binder alpha renaming; original sources retained'
  if len(bb)>1:
   cc=[f for f in bb if [[v for v in tokens(t) if v!='const']for t in f['context']]==[[v for v in tokens(t) if v!='const']for t in a['context']]]
   if cc:bb=cc
  if len(bb)==1:
   b=bb[0];r['deployed']=b;r['status']='identical-body' if tokens(a['body'])==tokens(b['body']) else 'different-body-law-required'
  elif bb and all(tokens(b['body'])==tokens(a['body']) for b in bb):r['status']='identical-all-candidate-bodies';r['deployed_candidates']=bb
  else:r['status']='unresolved-deployed-mapping';r['deployed_candidates']=bb
 else:r['extractor_candidates']=aa
 rows.append(r)
out=dict(capture_sha256=hashlib.sha256(capture.read_bytes()).hexdigest(),variant=variant,method='AST function item at LLBC span; matching function signature and enclosing impl/trait source; compare leaf tokens excluding comments; no compiler-cohort equivalence claimed',scope='standard declarations explicitly present in the LLBC; transitive opaque-body closure not yet claimed',counts={s:sum(r['status']==s for r in rows)for s in sorted({r['status']for r in rows})},rows=rows)
(D/('std227-comparison-'+variant+'-resume5.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['counts']))
