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
