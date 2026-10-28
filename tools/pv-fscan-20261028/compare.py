from pathlib import Path
import re,json,hashlib,difflib,sys,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');S=D/'src';O=D/'comparison';O.mkdir(exist_ok=True)
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def impl(m):
 p,line=m.group(1),int(m.group(2));p=p.replace(str(S)+'/', '');f=S/p
 if not f.exists():return m.group(0)
 lines=f.read_text().splitlines();v=lines[line-1].strip()
 if not v.startswith('impl'):return m.group(0)
 v=' '.join(lines[line-1:line+5]).split('{')[0].strip();return '<'+p+'::'+v+'>'
def normalize(s):
 s=re.sub(r'<impl at (.+?):(\d+):\d+: \d+:\d+>',impl,s)
 s=s.replace(str(S)+'/', '')
 # rustc allocation IDs are presentation labels; rename within each body in first-use order.
 ids={}
 s=re.sub(r'\balloc\d+\b',lambda m:ids.setdefault(m[0],'alloc'+str(len(ids))),s)
 return s
maps={};hashes={};duplicates=[]
for p in D.glob('*/crate.mir'):
 text=p.read_text();b={}
 for m in re.finditer(r'^fn ([^\n]+)\{\n.*?^}\n',text,re.M|re.S):
  value=normalize(m[0]);header=value.split('\n',1)[0];arg=re.search(r'\((?=_\d+:|\))',header);assert arg,header
  key=header[3:].removesuffix(' {').strip()
  if 'MIR FOR CTFE' in text[max(0,m.start()-60):m.start()]:key+=' [CTFE]' 
  if key in b:duplicates.append([p.parent.name,key])
  b[key]=value
 maps[p.parent.name]=b;hashes[p.parent.name]={k:sha(v) for k,v in b.items()}
pairs=[('core-old-dev','core-old-release','profile'),('core-ct-dev','core-ct-release','profile'),('core-ct-unchecked','core-ct-release','profile-unchecked'),('core-old-release','core-ct-release','ct-host-prover'),('statement-old-dev','statement-old-release','profile'),('statement-old-release','statement-ct-release','ct-host-prover'),('probe-default-dev','probe-default-release','profile'),('probe-default-release','probe-ct-release','prover/r1p-check/ct-host-prover')]
pairs += [('serialize-old-dev-fixed','serialize-deployed','feature/profile concrete serialization')]
pairs += [(a,'std-deployed','profile' if a=='std-same-compiler-dev' else 'compiler/sysroot/profile') for a in ['std-same-compiler-dev','std-kani-profile','std-charon-profile'] if a in maps]
pairs += [(p+'-charon-release',p+'-ct-release','compiler1.98-to1.94') for p in ['core','statement','probe'] if p+'-charon-release' in maps]
for n in ['statement-optimized2-release','probe-optimized-release']:
 if n in maps:pairs.append((n,n.split('-')[0]+'-ct-release','optimized-terminal'))
all=[];diffs=[]
for a,b,selector in pairs:
 if a not in maps or b not in maps:continue
 aa,bb=maps[a],maps[b];entries=[]
 for k in sorted(set(aa)|set(bb)):
  status='identical' if aa.get(k)==bb.get(k) else 'different' if k in aa and k in bb else 'only-old' if k in aa else 'only-deployed'
  row=dict(function=k,status=status,old_sha256=sha(aa[k]) if k in aa else None,new_sha256=sha(bb[k]) if k in bb else None)
  if status!='identical':
   row['selects_difference']=selector
   if selector=='profile':row['overflow_assertions_old']=len(re.findall(r'overflow|WithOverflow',aa.get(k,'')));row['overflow_assertions_new']=len(re.findall(r'overflow|WithOverflow',bb.get(k,'')))
   diffs.append(dict(pair=[a,b],function=k,old=aa.get(k),deployed=bb.get(k)))
  entries.append(row)
 all.append(dict(old=a,deployed=b,selector=selector,counts={status:sum(x['status']==status for x in entries) for status in ['identical','different','only-old','only-deployed']},functions=entries))
(O/'function-comparisons.json').write_text(json.dumps(dict(method='rustc1.94.1 emitted MIR at mir-opt-level0; impl source locations normalized to exact impl headers and per-body allocation labels alpha-renamed; locals/basic-blocks/calls/checks untouched',duplicates=duplicates,pairs=all),indent=2))
with lzma.open(O/'changed-bodies.json.xz','wt') as f:json.dump(diffs,f)
(O/'all-function-hashes.json').write_text(json.dumps(hashes,indent=2))
print(json.dumps([dict(old=p['old'],new=p['deployed'],counts=p['counts']) for p in all],indent=2));print('duplicate keys',len(duplicates))
