from pathlib import Path
import json,re,subprocess,hashlib,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin54-20261029';plan=json.loads((E/'build-plan.json').read_text())
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
assert len(receipts)==100 and {x['attempt'] for x in receipts}==set(range(66900,67000))
mods={v['module']:v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text()) if v['accepted']}
assert all(x['swaps']==0 for x in receipts)
for m,v in mods.items():
 assert hashlib.sha256((R/v['source']['path']).read_bytes()).hexdigest()==v['source_sha256'],m
 assert plan['modules'][m]['sha256']==v['source_sha256'],m
for x in receipts:assert x['reservation']['allowed'] and x['admission_exit']==0 and x['admission_and_launch_same_shell']
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 for d in plan['modules'].get(m,{}).get('imports',[]):closure(d,seen)
 return seen
logs=json.loads(lzma.decompress((E/'original-module-logs.json.xz').read_bytes()));audit={}
for kind,a in [('Neutral',66997),('Model',66998),('Source',66999)]:
 m='R1Z.PV_RunJoin_'+kind+'Audit54';c=closure(m);assert m in mods
 assert 'R1Z.PV_AL_CircleOwnedTypes' not in c
 if kind=='Neutral':assert 'AspisR72Sampler.Types' not in c
 out=next(v['output'] for v in logs if v['attempt']==a);names={}
 for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out,re.S):
  axioms=[x.strip() for x in (match[2] or '').split(',') if x.strip()]
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(match[1],axioms)
  names[match[1]]=axioms
 design=json.loads((E/'audit-design.json').read_text())[kind];assert set(design['names'])<=set(names)
 audit[kind]=dict(module=m,closure_count=len(c),names=names)
covered=set().union(*(closure('R1Z.PV_RunJoin_'+k+'Audit54') for k in audit));assert set(mods)<=covered,set(mods)-covered
(E/'audit-closure-check.json').write_text(json.dumps(dict(all_accepted_modules_covered=True,audits=audit),indent=2)+'\n')
summary=dict(attempts=100,accepted_attempts=sum(x['accepted'] for x in receipts),failed_attempts=sum(not x['accepted'] for x in receipts),accepted_modules=len(mods),peak_rss_bytes=max(x['peak_rss_bytes'] for x in receipts),swaps=0,rows_removed=[],discharged_links=['PV_RunJoin_Link_R24Sampler'],retained_links=['PV_RunJoin_Link_CommonSample','PV_RunJoin_Link_BackendInput','PV_RunJoin_Link_FinishContext','PV_RunJoin_Link_QueryAppend','PV_RunJoin_Link_NodeAppend','PV_RunJoin_Link_PublishOrder'],endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0),skeleton_attempt=66904,unchanged_failed_resubmission=66939,audits=[{k:x[k] for k in ['attempt','modules','exit','host_wall_seconds','peak_rss_bytes','swaps','source_revision','accepted']} for x in receipts if x['attempt']>=66997])
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','1adf3ca50f..HEAD'],cwd=R,text=True));print(json.dumps(summary,indent=2))
