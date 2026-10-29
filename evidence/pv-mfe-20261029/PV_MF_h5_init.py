from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');R=D.parent/'codex-pv-replay-20261027';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();j=json.load(open(D/'h5-input.json'));plan=json.load(open(D/'replay-cohort-plan.json'));integrity={x['module']:x for x in json.load(open(D/'replay-cohort-integrity.json'))['project_results']};env=json.load(open(R/'env/J.json'));nodes=plan['nodes'];project={};source={}
for m,v in nodes.items():
 p=R/'sources'/(m+'.lean');q=R/'objects'/(m+'.olean');h=j['modules'][m.replace('/','.')]['sha256'];assert sha(p)==h==integrity[m]['source_sha256'];assert sha(q)==integrity[m]['object_sha256'];project[m]=dict(object_path=str(q),object_sha256=sha(q));source[m]=dict(source_path=v['source_path'],source_sha256=h,head_sha256=h,imports=v['imports']);dst=D/'h5-objects'/(m+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(q)
# Preserve exactly the recorded replay environment; only the private output overlay is new.
f=dict(environment=env,source_closure=source,project=project);(D/'h5-preflight-input.json').write_text(json.dumps(f,indent=2)+'\n')
affected={m for mode,m in json.load(open(D/'jobs-h5.json'))};j['modules']={m:v for m,v in j['modules'].items() if m in affected};(D/'h5-rebuild-input.json').write_text(json.dumps(j,indent=2)+'\n')
for m,v in j['modules'].items():
 p=R/'sources'/(m.replace('.','/')+'.lean');q=D/'h5-sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
print('verified all',len(nodes),'replay project source/object hashes; staged',len(affected),'unchanged consumers')
