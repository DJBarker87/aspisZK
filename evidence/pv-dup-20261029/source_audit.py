from pathlib import Path
import json,hashlib,collections
B=Path(__file__).resolve().parent;H=B.parent
sha=lambda p:hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
seeds=json.load(open(B/'source-seeds.json'));cohort={x['module']:x for x in json.load(open(H/'codex-pv-evhc2-20261029/resume3/COHORT-MANIFEST.json'))['entries']}
mods=set(m for x in json.load(open(B/'collisions.json')) for m in x['modules'])
cache=json.load(open(H/'codex-cx-l188-cache-20261028/NDJ_CACHE_PINS.json'))
old={x['module']:x for x in cache['objects'] if x.get('selection')=='union'}
package=H/'ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages'
libroots={'Init':Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean'),'Lean':Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean'),'Std':Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean'),'Mathlib':package/'mathlib','Batteries':package/'batteries','Aeneas':H/'aspis-r1-j17-port-20261015/backend','AeneasMeta':H/'aspis-r1-j17-port-20261015/backend'}
result={};gaps=[];errors=[]
for m in sorted(mods):
 e=seeds.get(m)
 if e:
  e=dict(e)
  if e['source'].startswith('/home/'):
   p=Path(e['source']);assert p.exists(),str(p)
   if e.get('sha256'):assert sha(p)==e['sha256'],('host source mismatch',m,str(p))
   e['host_file_verified']=True
  elif e.get('host_source'):
   p=Path(e['host_source']);assert p.exists() and sha(p)==e['sha256'],('event source mismatch',m)
   e['host_file_verified']=True
 elif m in old and old[m].get('source') and old[m]['sha256']==cohort[m]['sha256']:
  x=old[m];p=Path(x['source']);assert sha(p)==x['source_sha256']
  e=dict(source=str(p),sha256=x['source_sha256'],basis='NDJ_CACHE_PINS source/object association; object hash matches READY',host_file_verified=True)
 elif m.split('.')[0] in libroots:
  p=libroots[m.split('.')[0]]/(m.replace('.','/')+'.lean')
  if p.exists():e=dict(source=str(p),sha256=sha(p),basis='pinned library module source path; source name follows module mapping',kind='Lean/library; no Rust extraction run',host_file_verified=True)
 if not e and m in old:
  original=Path(old[m]['original']);p=original.with_suffix('.lean')
  if p.exists():e=dict(source=str(p),sha256=sha(p),basis='NDJ retained object origin plus adjacent source snapshot',qualification='adjacent retained source; compiler source binding not independently recovered here',host_file_verified=True)
 if not e:gaps.append(m);e=dict(source=None,basis='source association not yet recovered',original_object=old.get(m,{}).get('original'))
 e['object_path']=cohort[m]['path'];e['object_sha256']=cohort[m]['sha256'];result[m]=e
(B/'SOURCES.json').write_text(json.dumps(result,indent=2)+'\n');(B/'SOURCE-GAPS.json').write_text(json.dumps(gaps,indent=2)+'\n')
print(json.dumps({'providers':len(mods),'source_associations':len(mods)-len(gaps),'gaps':gaps}),flush=True)
# Distinguish strict syntax differences in the two generated PublicCodec proof types.
proofs={}
for line in (B/'divergent-expressions.jsonl').open():
 x=json.loads(line)
 if x['name'].startswith('AspisR1.PublicCodecAgreement.u64_emit_eq_index_encode._proof_'):
  gs=x['groups'];a=json.loads(gs[0]['type']);b=json.loads(gs[1]['type'])
  an=list(map(json.loads,a['nodes']));bn=list(map(json.loads,b['nodes']));diff=[];seen=set()
  def visit(i,j):
   if (i,j) in seen:return
   seen.add((i,j));l=an[i];r=bn[j]
   if l[0]!=r[0]:diff.append({'left':l,'right':r});return
   tag=l[0];children={'app':[1,2],'lam':[2,3],'forallE':[2,3],'letE':[2,3,4],'mdata':[2],'proj':[3]}.get(tag,[])
   if [v for k,v in enumerate(l) if k not in children]!=[v for k,v in enumerate(r) if k not in children]:diff.append({'left':l,'right':r})
   for k in children:visit(l[k],r[k])
  visit(a['root'],b['root']);proofs[x['name']]={'modules':[g['modules'] for g in gs],'type_node_differences':diff[:30]}
(B/'CODEC-TYPE-DIFFS.json').write_text(json.dumps(proofs,indent=2)+'\n')
print('codec type differences',json.dumps(proofs)[:1800],flush=True)
