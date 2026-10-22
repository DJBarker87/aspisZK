#!/usr/bin/env python3
"""Read-only hash/text repin overlay. No extraction, compiler or release replay."""
from pathlib import Path
import collections, hashlib, json, re, subprocess, sys, time
R=Path(__file__).resolve().parents[5]
E=Path(__file__).resolve().parent
B=E.parent
BASE='b2727acd3abf79315d18b754a260f58f4b1c6326'
ADOPT='29cbab431742f7e899870595167efa193a379f0a'
TARGET='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(x):return hashlib.sha256(x).hexdigest()
def write(name,obj):
 s=json.dumps(obj,indent=2,sort_keys=True)+'\n'
 if '--check' in sys.argv:assert (E/name).read_text()==s,name
 else:(E/name).write_text(s)
def selected(n):
 return n.startswith(('s7-','s8-','repin-s7','repin-s8','s10-','ckpt-','multiproof-cone','frozen-order')) or ('parser' in n and not n.startswith(('s1','s2','s3','s4','s5','s6','s9')))
scopes=sorted(p for p in B.iterdir() if p.is_dir() and selected(p.name))
# Exact balanced item slicing follows the retained generators, without normalization.
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:
  d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e].encode(),s[:a].count('\n')+1,s[:e].count('\n')+1
rows=[];inputs={};unresolved=[]
tracked=set(git('ls-files').decode().splitlines())
def norm(p):
 if not isinstance(p,str):return None
 p=p.removeprefix('./')
 if p.startswith('/'):
  for prefix in ['crates/','programs/','tools/','docs/']:
   k=p.find('/'+prefix)
   if k>=0:p=p[k+1:];break
 return p if p in tracked and (R/p).is_file() else None
def add(src,loc,path,h,marker=None):
 if not re.fullmatch('[0-9a-f]{64}',str(h)):return
 p=norm(path)
 if p is None:return
 data=(R/p).read_bytes();start=end=None
 if marker:
  try:data,start,end=item(data.decode(),marker)
  except (ValueError,IndexError,UnicodeDecodeError):
   unresolved.append({'receipt':src,'location':loc,'path':p,'marker':marker});return
 rows.append({'receipt':src,'location':loc,'path':p,'marker':marker,'old_sha256':h,'current_sha256':sha(data),'status':'unchanged' if sha(data)==h else 'HISTORICAL','start_line':start,'end_line':end})
def walk(o,src,loc='$'):
 if isinstance(o,dict):
  path=o.get('path') or o.get('retained_source') or o.get('source_path')
  if path:
   for h in ['sha256','source_sha256','hash','expected']:
    if isinstance(o.get(h),str):add(src,loc,path,o[h])
  for k,v in o.items():
   if isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):
    if ':' in k and k.split(':',1)[0].endswith('.rs'):
     path,marker=k.split(':',1);add(src,loc+'.'+k,path,v,marker)
    else:add(src,loc+'.'+k,k,v)
   if isinstance(v,dict) and ':'.join(k.split(':')[:1]).endswith('.rs') and ':' in k and 'sha256' in v:
    path,marker=k.split(':',1);add(src,loc+'.'+k,path,v['sha256'],marker)
   walk(v,src,loc+'.'+k)
 elif isinstance(o,list):
  for i,v in enumerate(o):walk(v,src,loc+f'[{i}]')
for scope in scopes:
 for p in sorted(scope.rglob('*.json')):
  # Huge LLBC/census graphs carry declarations, not file pins; accounted separately.
  if p.stat().st_size>12000000:continue
  src=str(p.relative_to(R));raw=p.read_bytes();inputs[src]=sha(raw)
  try:walk(json.loads(raw),src)
  except (json.JSONDecodeError,UnicodeDecodeError):pass
# Independent full frozen source census, every entry; no source is silently re-labelled.
old=json.loads((B/'s10-inventory-20261021/source-hashes.json').read_text())
census=[]
for rec in old['files']:
 p=rec['path'];data=(R/p).read_bytes() if (R/p).is_file() else None
 census.append({'path':p,'old_sha256':rec['sha256'],'new_sha256':sha(data) if data is not None else None,'status':'unchanged' if data is not None and sha(data)==rec['sha256'] else 'HISTORICAL'})
# Function-level comparison, disambiguated by occurrence in lexical source order.
functions=[]
for name in ['fast_dots','fast_pairing','weights']:
 path=f'crates/aspis-r1-cost-probe/src/{name}.rs'
 def funcs(raw):
  s=raw.decode();counts=collections.Counter();out={}
  for m in re.finditer(r'\b(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?fn\s+(\w+)\s*(?:<|\()',s):
   n=m.group(1);counts[n]+=1;marker=s[m.start():s.index('{',m.start())]
   b,_,_=item(s[m.start():],marker);lo=s[:m.start()].count('\n')+1;hi=lo+b.decode().count('\n');out[(n,counts[n])]=(b,lo,hi)
  return out
 a=funcs(git('show',BASE+':'+path));b=funcs((R/path).read_bytes())
 for key in sorted(a.keys()|b.keys()):
  x=a.get(key);y=b.get(key)
  functions.append({'path':path,'function':key[0],'occurrence':key[1], 'old_sha256':sha(x[0]) if x else None,'new_sha256':sha(y[0]) if y else None,'old_lines':list(x[1:]) if x else None,'new_lines':list(y[1:]) if y else None,'status':'unchanged' if x and y and x[0]==y[0] else 'HISTORICAL' if x else 'new'})
grouped={}
for r in rows:
 key=(r['path'],r['marker'],r['old_sha256'])
 if key not in grouped:
  grouped[key]={k:v for k,v in r.items() if k not in ['receipt','location']}
  grouped[key]['receipts']=set()
 grouped[key]['receipts'].add(r['receipt'])
checks=[]
for r in grouped.values():
 r['receipts']=sorted(r['receipts']);checks.append(r)
write('pin-checks.json',{'target_revision':TARGET,'scopes':[p.name for p in scopes],'input_sha256':inputs,'checks':checks,'unresolved_markers':unresolved,'note':'Only locally resolvable explicit SHA-256 file/item pins; temporary host/binary paths are not claimed checked. All JSON inputs hashed; old receipts immutable. Snapshot hashes are not execution-equivalence certificates.'})
write('source-census.json',{'old_revision':BASE,'adoption_revision':ADOPT,'target_revision':TARGET,'files':census})
write('function-checks.json',{'old_revision':BASE,'target_revision':TARGET,'method':'Exact UTF-8 function text from fn signature through balanced final brace, no whitespace normalization; lexical occurrence distinguishes repeated method names. Attributes outside the slice are covered by file census.','functions':functions})
print(json.dumps({'scopes':len(scopes),'json_inputs':len(inputs),'pin_checks':len(rows),'pin_status':dict(collections.Counter(r['status'] for r in rows)),'unresolved_markers':len(unresolved),'census_changes':[r['path'] for r in census if r['status']!='unchanged'],'function_changes':[r['function'] for r in functions if r['status']!='unchanged']},indent=2))
