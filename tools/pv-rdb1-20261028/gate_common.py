"""Fail-closed complete-body binding for the deployed pop library boundary.
Primitive pointer/load/copy meanings retain the original structural boundary.
No Kani, compiler, allocator internals or machine adequacy credit is claimed.
"""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
checks=[]
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tok(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def end(s,a):
 d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return i+1
 raise ValueError('unclosed body')
def body(s,anchor):
 s=clean(s);a=s.index('{',s.index(anchor));return s[a:end(s,a)]
def release(s):
 # Exactly two cfg-gated debug-only items in ptr::add and one in ptr::read.
 # Remove only complete annotated declarations or macro statements.
 marker='#[cfg(debug_assertions)]'
 while marker in s:
  a=s.index(marker);brace=s.find('{',a);semi=s.find(');',a)
  z=brace if brace >= 0 and (semi < 0 or brace < semi) else -1
  if z>=0:
   b=end(s,z)
  else:
   b=s.index(');',a)+2
  s=s[:a]+s[b:]
 return s

def check(file,anchor,want,law,select=False):
 p=S/file;s=p.read_text();actual=body(s,anchor);selected=release(actual) if select else actual
 assert tok(selected)==tok(want),(file,anchor,selected,want)
 # Matched source negative control: changing an operation is rejected.
 assert tok(selected+';')!=tok(want)
 checks.append(dict(file=str(p),file_sha256=hashlib.sha256(s.encode()).hexdigest(),anchor=anchor,complete_body=actual,selected_release_body=selected,tokens_equal=True,law=law))

