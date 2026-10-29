from pathlib import Path
import json,subprocess,hashlib,re
E=Path('evidence/pv-evhc2-20261029');old=Path('evidence/pv-evhc-20261029')
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
events={v['module']:v for v in json.load(open(old/'evh-cohort-pins.json'))};ndr={v['module']:v for v in json.load(open(old/'NDR_FINAL_COHORT_PINS.json'))['entries']}
ndr['NDR_CombinedAudit']=dict(module='NDR_CombinedAudit',object_path='/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects/NDR_CombinedAudit.olean',object_sha256=json.load(open(old/'NDR_FINAL_OUTPUT_PINS.json'))['objects/NDR_CombinedAudit.olean']['sha256'])
# CallerLive is a direct consumer import omitted from the old event headline audit.
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','b51b1040f2','evidence/pv-rj4idb-20261029'],text=True).splitlines()
build_modules=json.loads(git('b51b1040f2','evidence/pv-rj4idb-20261029/build-plan.json'))['modules']
for p in tracked:
 if '/modules-' not in p or not p.endswith('.json'):continue
 for v in json.loads(git('b51b1040f2',p)):
  if not v.get('accepted') or v['module'] in events:continue
  m=v['module'];path=build_modules[m]['path']
  events[m]=dict(module=m,path='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029/objects/'+m.replace('.','/')+'.olean',sha256=v['object_sha256'],source=dict(path=path,revision=build_modules[m]['revision'],source_sha256=v['source_sha256']),receipt=p)
base=json.loads(git('b51b1040f2','evidence/pv-rj4idb-20261029/source-resolution.json'))['projects']
checks={v['module']:v for v in json.loads(git('b51b1040f2','evidence/pv-rj4idb-20261029/h6-result.json'))['result']['checks']}
for m,v in base.items():
 if m in events:continue
 c=checks[m];events[m]=dict(module=m,path=c['object_path'],sha256=c['object_sha256'],source=v)
conflicts={v['module'] for v in json.load(open(old/'cohort-overlap.json'))['differences']}
identity=[]
files=subprocess.check_output(['git','ls-tree','-r','--name-only','b51b1040f2'],text=True).splitlines()
manifest=[]
for p in files:
 if p in ['AspisFormal/lake-manifest.json','AspisFormal/lean-toolchain','aeneas-verif/lean432/lake-manifest.json','aeneas-verif/proof/lake-manifest.json','aeneas-verif/proof/lean-toolchain']:
  a,b=git('b51b1040f2',p),git('06f74c902f',p);assert a==b,p
  manifest.append(dict(path=p,sha256=sha(a)))
for m in sorted(conflicts):
 v=events[m];s=v.get('source')
 if s:
  p=s['path'];a,b=git('b51b1040f2',p),git('06f74c902f',p);assert a==b,m
  identity.append(dict(module=m,path=p,event_git_blob=subprocess.check_output(['git','rev-parse','b51b1040f2:'+p],text=True).strip(),ndr_git_blob=subprocess.check_output(['git','rev-parse','06f74c902f:'+p],text=True).strip(),sha256=sha(a),identical=True,kind='project'))
 else:
  # External dependency identity is anchored by identical package revisions.
  suffix=m.replace('.','/')+'.lean';candidates=[p for p in files if p.endswith('/'+suffix)]
  snapshots=[]
  for p in candidates:
   a,b=git('b51b1040f2',p),git('06f74c902f',p);assert a==b,(m,p)
   snapshots.append(dict(path=p,sha256=sha(a)))
  identity.append(dict(module=m,kind='external',identical=True,method='identical package lock revisions/toolchain at both cohort revisions; tracked source snapshots where available; host source hash follows',snapshots=snapshots))
(E/'source-identity.json').write_text(json.dumps(dict(revisions=['b51b1040f2','06f74c902f'],modules=identity,manifests=manifest),indent=2)+'\n')
# Resolve all project inputs using the predecessor's committed source resolution.
sources={};edges={}
for m,v in events.items():
 if m in ndr:continue
 s=v.get('source')
 if not s and 'source_path'in v:s=dict(path=v['source_path'],revision=v['source_revision'],source_sha256=v['source_sha256'])
 if s:
  b=git(s['revision'],s['path']);assert sha(b)==s['source_sha256'],m
  sources[m]=dict(path=s['path'],revision=s['revision'],sha256=sha(b),text=b.decode())
  text=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);text=re.sub(r'--[^\n]*','',text)
  edges[m]=re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',text,re.M)
# Libraries absent on NDR side are separately pinned below.
only=set(events)-set(ndr)
external_only=only-set(sources)
assert external_only=={'Mathlib.Data.FinEnum'},external_only
# FinEnum is the sole event-only external; its dependencies are resolved from host source before launch.
consumer=git('b51b1040f2','lean/PV_EVH_FixtureConsumer.lean');assert sha(consumer)=='2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4'
roots=re.findall(r'^import (\S+)',consumer.decode(),re.M)
visited=set();order=[];affected={}
def visit(m):
 if m in visited:return affected[m]
 if m in ndr:visited.add(m);affected[m]=m in conflicts;return affected[m]
 if m=='Mathlib.Data.FinEnum':visited.add(m);affected[m]=False;order.append(m);return False
 assert m in sources,('unresolved',m)
 visited.add(m);hit=False
 for d in edges[m]:hit=visit(d) or hit
 affected[m]=hit;order.append(m);return hit
for m in roots:visit(m)
plan=dict(consumer_sha256=sha(consumer),roots=roots,conflicts=sorted(conflicts),rebuild=[m for m in order if affected[m]],reuse=[m for m in order if not affected[m]],event_only_not_needed=sorted(only-set(order)),edges={m:edges.get(m,[]) for m in order},sources={m:sources[m] for m in order if m in sources},events={m:events[m] for m in order},ndr_manifest_sha256=sha((old/'NDR_FINAL_COHORT_PINS.json').read_bytes()))
(E/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print('identity',len(identity),'rebuild',len(plan['rebuild']),'reuse',plan['reuse'],'not needed',len(plan['event_only_not_needed']))
