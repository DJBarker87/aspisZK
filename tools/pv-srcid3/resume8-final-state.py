#!/usr/bin/env python3
import pathlib,json,hashlib,subprocess,re
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';host='dombarker@100.108.41.90'
research=subprocess.check_output(['git','rev-parse','research'],cwd=root,text=True).strip();prior=json.loads((e/'resume8-shared-check.json').read_text());rows=[]
for old in prior['rows']:
 m=old['module'];a=subprocess.check_output(['git','show',research+':'+old['path']],cwd=root);b=subprocess.check_output(['ssh','-o','ConnectTimeout=10',host,'cat /home/dombarker/project-offloads/aspis-joint-20261019/sources/'+m.replace('.','/')+'.lean']);rows.append(dict(module=m,path=old['path'],research_sha=hashlib.sha256(a).hexdigest(),shared_sha=hashlib.sha256(b).hexdigest(),equal=a==b))
(e/'resume8-shared-final-check.json').write_text(json.dumps(dict(research_revision=research,rows=rows),indent=2)+'\n')
for name,path in [('env-J','/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'),('lake-manifest','/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/lake-manifest.json')]:
 b=subprocess.check_output(['ssh','-o','ConnectTimeout=10',host,'cat '+path]);(e/('resume8-'+name+'.json')).write_bytes(b);assert b==(e/('resume7-'+name+'.json')).read_bytes(),name+' environment changed'
env=json.loads((e/'resume8-env-J.json').read_text());summary=dict(env_J_sha256=hashlib.sha256((e/'resume8-env-J.json').read_bytes()).hexdigest(),lake_manifest_sha256=hashlib.sha256((e/'resume8-lake-manifest.json').read_bytes()).hexdigest(),toolchain=env['ELAN_TOOLCHAIN'],lean_githash=env['LEAN_GITHASH'],env_and_manifest_match_previous=True)
(e/'resume8-final-environment.json').write_text(json.dumps(summary,indent=2)+'\n')
rev=subprocess.check_output(['git','rev-parse','codex/pv-runjoin-20261026'],cwd=root,text=True).strip();paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/pv-runjoin12-20261027'],cwd=root,text=True).splitlines();pins=[]
for path in paths:
 if not re.search(r'/receipt-\d+\.json$',path):continue
 r=json.loads(subprocess.check_output(['git','show',rev+':'+path],cwd=root));target=r.get('target','')
 if r.get('accepted') and ('PV_RunJoin_RootModelCell' in target or target.endswith('PV_RunJoin_RootModelTable')):
  source='docs/research/v8-r0-zk-20261009/lean/'+target+'.lean';b=subprocess.check_output(['git','show',rev+':'+source],cwd=root);assert hashlib.sha256(b).hexdigest()==r['source_sha256'];assert r['exit']==0
  names={s.strip() for line in r['axioms'] for g in re.findall(r'depends on axioms: \[([^\]]*)\]',line) for s in g.split(',') if s.strip()};assert names<={'propext','Classical.choice','Quot.sound'}
  (e/('resume8-readonly-receipt-'+str(r['attempt'])+'.json')).write_text(json.dumps(r,indent=2)+'\n');pins.append(dict(module=target.replace('/','.'),revision=rev,source_path=source,source_sha256=r['source_sha256'],receipt=path,attempt=r['attempt'],axioms_standard=True,classification='Mathematical nodeCompress cells/table only; actual source-parent refinement remains open'))
assert sum('RootModelCell' in p['module'] for p in pins)==21
(e/'resume8-runjoin-all-model-cell-pins.json').write_text(json.dumps(pins,indent=2)+'\n');(e/'resume8-runjoin-root-model-final-stage.md').write_bytes(subprocess.check_output(['git','show',rev+':evidence/pv-runjoin12-20261027/stage-root-model.md'],cwd=root))
print('Final source mismatches',sum(not r['equal'] for r in rows),'; environment unchanged; read-only model cells21/21 and table receipts pinned')
