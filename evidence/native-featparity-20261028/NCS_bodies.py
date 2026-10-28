"""Cfg evaluation of frozen Rust bodies; source audit, never compilation."""
import sys,json,re,subprocess,pathlib,hashlib,collections
sys.path.insert(0,'/private/tmp/NBI2-parser')
from tree_sitter import Language,Parser
import tree_sitter_rust
P=Parser(Language(tree_sitter_rust.language()))
E=pathlib.Path(__file__).parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
graphs={j['label']:j for l in (E/'NCS_I002-stdout.log').read_text().splitlines() if (j:=json.loads(l))}
features={k:{n['name']:set(n['features']) for n in j['nodes']} for k,j in graphs.items()}
def parts(s):
 out=[];depth=0;start=0
 for i,c in enumerate(s):
  if c=='(':depth+=1
  if c==')':depth-=1
  if c==',' and depth==0:out.append(s[start:i]);start=i+1
 out.append(s[start:]);return [x.strip() for x in out if x.strip()]
def cfg(s,fs):
 s=s.strip();m=re.fullmatch(r'(all|any|not)\((.*)\)',s,re.S)
 if m:
  op,inner=m.groups();v=[cfg(x,fs) for x in parts(inner)]
  if None in v:return None
  return all(v) if op=='all' else any(v) if op=='any' else not v[0]
 m=re.fullmatch(r'feature\s*=\s*"([^"]+)"',s)
 if m:return m[1] in fs
 if s=='kani':return True
 if s in ('test','debug_assertions'):return False # common profile for FEATURE comparison only
 if s in ('target_os="solana"','target_os = "solana"'):return False # host fixed; target separate
 if s in ('target_arch = "x86_64"','target_pointer_width = "64"','target_endian = "little"'):return True
 return None

def walk(n):
 yield n
 for c in n.named_children:yield from walk(c)
def text(n,b):return b[n.start_byte:n.end_byte].decode()
def attrs(n,b):
 out=[];p=n.prev_named_sibling
 while p and p.type in ('attribute_item','line_comment','block_comment'):
  if p.type=='attribute_item':out.append(p)
  p=p.prev_named_sibling
 return list(reversed(out))
def select(n,b,fs):
 edits=[];unknown=[];decisions=[]
 def visit(x):
  aa=attrs(x,b)
  for a in aa:
   s=text(a,b);m=re.fullmatch(r'#\[cfg\((.*)\)\]',s,re.S)
   if m:
    v=cfg(m[1],fs);decisions.append(dict(line=a.start_point.row+1,predicate=m[1],value=v))
    if v is None:unknown.append(s)
    if v is False:
     edits.append((aa[0].start_byte,x.end_byte,b''));return
    edits.append((a.start_byte,a.end_byte,b''))
   elif 'cfg_attr' in s:unknown.append(s)
  if x.type in ('line_comment','block_comment'):edits.append((x.start_byte,x.end_byte,b''));return
  if x.type=='macro_invocation' and text(x.child_by_field_name('macro'),b)=='cfg':
   s=text(x,b);m=re.fullmatch(r'cfg!\s*\((.*)\)',s,re.S)
   if m:
    v=cfg(m[1],fs)
    if v is None:unknown.append(s)
    else:edits.append((x.start_byte,x.end_byte,str(v).lower().encode()));return
  for c in x.named_children:
   if c.type!='attribute_item':visit(c)
 visit(n)
 # Only edits inside the body. Parent/item cfg availability is evaluated separately.
 edits=sorted(set((a,z,r) for a,z,r in edits if a>=n.start_byte and z<=n.end_byte), key=lambda e:(e[0],-e[1]))
 out=b'';pos=n.start_byte
 for a,z,r in edits:
  if a<pos:continue
  out+=b[pos:a]+r;pos=z
 out+=b[pos:n.end_byte]
 # Token stream preserves literal contents; never removes whitespace inside string literals.
 toks=re.findall(rb'br?\#*".*?"\#*|b?"(?:\\.|[^"\\])*"|\b\w+\b|[^\s]',out,re.S)
 return b'\x00'.join(toks),unknown,decisions,out
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'crates','programs']).decode().splitlines()
paths=[p for p in paths if p.endswith('.rs') and '/src/' in p]
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
records={};changed_sources={};files={};errors=[]
for path in paths:
 proc.stdin.write((REV+':'+path+'\n').encode());proc.stdin.flush();hdr=proc.stdout.readline();b=proc.stdout.read(int(hdr.split()[2]));proc.stdout.read(1)
 files[path]=sha(b);tree=P.parse(b)
 if tree.root_node.has_error:errors.append(path)
 pkg=path.split('/')[1]
 for n in walk(tree.root_node):
  if n.type!='function_item':continue
  body=n.child_by_field_name('body')
  if not body:continue
  parents=[];q=n.parent
  while q:parents.append(q);q=q.parent
  scopes=[]
  for q in reversed(parents):
   field='type' if q.type=='impl_item' else 'name' if q.type in ('function_item','mod_item') else None
   if field and (a:=q.child_by_field_name(field)):scopes.append(text(a,b))
  name='::'.join(scopes+[text(n.child_by_field_name('name'),b)]);key=path+'::'+name
  if key in records:key+='@'+str(n.start_point.row+1)
  r=dict(id=key,file=path,name=name,line=n.start_point.row+1,body_sha256=sha(b[body.start_byte:body.end_byte]),configurations={})
  for label,fsmap in features.items():
   fs=fsmap.get(pkg,set());selected,unknown,decisions,raw=select(body,b,fs)
   avail=True
   for item in [n]+parents:
    for a in attrs(item,b):
     m=re.fullmatch(r'#\[cfg\((.*)\)\]',text(a,b),re.S)
     if m:
      v=cfg(m[1],fs)
      if v is False:avail=False
      if v is None:unknown.append(text(a,b))
   r['configurations'][label]=dict(sha256=sha(selected) if avail else None,available=avail,unknown=sorted(set(unknown)),decisions=decisions)
   if label in ('library-default','library-deployed'):changed_sources.setdefault(key,{})[label]=raw.decode()
  records[key]=r
proc.stdin.close();proc.wait()
changes=[]
for r in records.values():
 a=r['configurations']['library-default'];z=r['configurations']['library-deployed']
 if a['sha256']!=z['sha256'] and a['available'] and z['available']:
  changes.append(r['id'])
(E/'NCS_BODY_HASHES.json').write_text(json.dumps(dict(revision=REV,method='SHA256 of NUL-separated lexical tokens after AST cfg attribute/cfg! evaluation; common host target, kani=true, debug_assertions=false for FEATURE-only comparison. Macro expansion and type/const selection outside bodies are not certified.',files=files,parse_errors=errors,bodies=list(records.values()),changed_library_bodies=changes),indent=2)+'\n')
(E/'NCS_CHANGED_BODIES.json').write_text(json.dumps({k:v for k,v in changed_sources.items() if k in changes},indent=2)+'\n')
print('files',len(files),'functions',len(records),'changed shared library bodies',len(changes),'parse errors',len(errors))
