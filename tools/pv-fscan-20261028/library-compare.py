from pathlib import Path
import re,json,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');O=D/'library-comparison';O.mkdir(exist_ok=True);sources={}
def sha(x):return hashlib.sha256(x.encode()).hexdigest()
def pathnorm(s):
 s=re.sub(r'/home/dombarker/\.rustup/toolchains/[^/]+/lib/rustlib/src/rust/library/','library/',s)
 s=re.sub(r'/home/dombarker/\.cargo/registry/src/[^/]+/','registry/',s)
 s=re.sub(r'registry/zeroize-[0-9.]+/','registry/zeroize/',s)
 # Existing byte-array/Zeroizing row domains are Sized; the 1.9 ?Sized relaxation changes no body on that retained domain.
 s=s.replace('Zeroize + ?Sized','Zeroize')
 return s.replace(str(D)+'/','audit/')
def impl(m):
 p,line=m.group(1),int(m.group(2));f=Path(p)
 if not f.exists():return pathnorm(m[0])
 if p not in sources:sources[p]=f.read_text().splitlines()
 lines=sources[p];v=lines[line-1].strip()
 if not v.startswith('impl'):return pathnorm(m[0])
 v=' '.join(lines[line-1:line+12]).split('{')[0].strip();return '<'+pathnorm(p)+'::'+v+'>'
def parse(p):
 text=p.read_text();b={}
 for m in re.finditer(r'^fn ([^\n]+)\{\n.*?^}\n',text,re.M|re.S):
  s=re.sub(r'<impl at (.+?):(\d+):\d+: \d+:\d+>',impl,m[0]);s=pathnorm(s);ids={};s=re.sub(r'\balloc\d+\b',lambda m:ids.setdefault(m[0],'alloc'+str(len(ids))),s);key=s.split('\n')[0][3:].removesuffix(' {').strip()
  if 'MIR FOR CTFE' in text[max(0,m.start()-60):m.start()]:key+=' [CTFE]'
  if key in b:
   # Preserve macro-expanded bodies with identical printed headers separately.
   i=2
   while key+' [occurrence '+str(i)+']' in b:i+=1
   key+=' [occurrence '+str(i)+']'
  b[key]=s
 return b
variants=['libraries-client194-exact','libraries-charon','libraries-dev','libraries-default','libraries-deployed','libraries-client194-dev-exact'];maps={};manifest=[]
for n in variants:
 maps[n]={}
 for lib in ['std','alloc','core','sha2','digest','block_buffer','zeroize','generic_array','typenum','crypto_common','subtle']:
  ps=list((D/n).glob(lib+'-*.mir'))
  if n.endswith('-exact'):
   am=json.loads((D/n/'mir-manifest.json').read_text());ps=[D/n/x['path'] for x in am if x['path'].startswith(lib+'-')]
  if not ps and n=='libraries-charon':
   ps=list((D/'library-target-nightly-2026-06-01/x86_64-unknown-linux-gnu/release/deps').glob(lib+'-*.mir'))
   if len(ps)==1:
    import shutil
    shutil.copy2(ps[0],D/n/ps[0].name);ps=[D/n/ps[0].name]
   else:ps=[]
  if not ps:continue
  # Default-feature build may retain both Cargo fingerprints; choose original target mtime.
  target=D/('library-target-1.94.1' if n!='libraries-charon' else 'library-target-nightly-2026-06-01')/'x86_64-unknown-linux-gnu'/('debug' if n=='libraries-dev' else 'release')/'deps'
  if n=='libraries-default':ps.sort(key=lambda p:(target/p.name).stat().st_mtime)
  else:ps.sort(key=lambda p:p.stat().st_mtime)
  p=ps[-1];maps[n][lib]=parse(p);b=p.read_bytes();manifest.append(dict(variant=n,library=lib,file=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b),functions=len(maps[n][lib])))
all=[];diff=[]
for old in variants[1:]:
 for lib,aa in maps[old].items():
  bb=maps['libraries-client194-exact'][lib];entries=[]
  for k in sorted(set(aa)|set(bb)):
   status='identical' if aa.get(k)==bb.get(k) else 'different' if k in aa and k in bb else 'only-old' if k in aa else 'only-deployed'
   entries.append(dict(function=k,status=status,old_sha256=sha(aa[k]) if k in aa else None,deployed_sha256=sha(bb[k]) if k in bb else None))
   if status!='identical' and lib in ['alloc','std','sha2','digest','block_buffer','zeroize']:
    diff.append(dict(old_configuration=old,library=lib,function=k,old=aa.get(k),deployed=bb.get(k)))
  all.append(dict(old=old,deployed='libraries-client194-exact',library=lib,selector='debug_assertions/overflow_checks' if old=='libraries-client194-dev-exact' else 'compiler/sysroot+resolved features+dependency versions' if old=='libraries-charon' else 'features/versions/profile control; see input manifests',counts={s:sum(x['status']==s for x in entries) for s in ['identical','different','only-old','only-deployed']},functions=entries))
with lzma.open(O/'library-comparisons.json.xz','wt') as f:json.dump(all,f)
with lzma.open(O/'changed-library-bodies.json.xz','wt') as f:json.dump(diff,f)
(O/'library-mir-manifest.json').write_text(json.dumps(manifest,indent=2));print(json.dumps([{k:v for k,v in p.items() if k!='functions'} for p in all],indent=2))
