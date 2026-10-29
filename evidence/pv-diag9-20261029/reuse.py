from pathlib import Path
import json,lzma,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag9-20261029');R=D.parent/'codex-pv-runjoin-20261026/runjoin32-lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.load(lzma.open(D/'runjoin52-preflight.json.xz'));pj={r['module']:r for r in a['projects']};deps={}
for r in a['dependencies']:deps.setdefault(r['module'],[]).append(r)
roots=['R1Z.PV_RunJoin_CanonicalHonest31','R1Z.PV_RunJoin_HonestIdentification26','R1Z.PV_RunJoin_PreparedCaller32','R1Z.PV_RunJoin_CallerSuccess43','R1Z.PV_RunJoin_SemanticComplete40','R1Z.PV_RunJoin_EncodedComplete41','R1Z.ProverCommitRetry34','R1Z.ProverRwRetryModel','R1Z.PV_RunJoin_ResultPost41']
seen={}
def visit(m):
 if m in seen:return
 if m not in pj:return
 r=pj[m];src=R/'sources'/(m.replace('.','/')+'.lean');obj=R/'objects'/(m.replace('.','/')+'.olean')
 assert sha(src)==r['source_sha256'],m+' source'
 assert sha(obj)==r['object_sha256'],m+' object'
 seen[m]=dict(r,source_path=str(src),path=str(obj),dependencies=deps.get(m,[]))
 text=src.read_text(); clean=''; depth=0; i=0
 while i<len(text):
  if text[i:i+2]=='/-':depth+=1;i+=2
  elif text[i:i+2]=='-/' and depth:depth-=1;i+=2
  else:
   if not depth:clean+=text[i]
   i+=1
 imports=[x for line in re.findall(r'^import ([^\n]+)',clean,re.M) for x in line.split()]
 assert set(imports)<={q['dependency'] for q in deps.get(m,[])},(m,imports)
 for q in deps.get(m,[]):
  assert sha(Path(q['path']))==q['expected'],(m,q)
  visit(q['dependency'])
for m in roots:visit(m)
for m,r in seen.items():
 src=Path(r['path']);dst=D/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for p,q in [(src,dst),(Path(str(src)+'.private'),Path(str(dst)+'.private')),(Path(str(src)+'.server'),Path(str(dst)+'.server')),(src.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if p.exists() and not q.exists():q.symlink_to(p)
(D/'reuse.json').write_text(json.dumps(dict(roots=roots,rows=seen,checked=len(seen),authority='h6 read-only runjoin52 accepted coherent source/object/import preflight',toolchain='lean4:v4.32.0',prefix='private objects with identical selected object closure then identical external'),indent=2)+'\n')
print('reused',len(seen))
