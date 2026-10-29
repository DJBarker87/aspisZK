from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin51-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[dict(v,attempt=int(p.stem.split('-')[1])) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
accepted={v['module']:v for v in rows if v['accepted']};status=[]
for p in sorted(L.glob('PV_RunJoin_*51.lean')):
 m='R1Z.'+p.stem;sha=hashlib.sha256(p.read_bytes()).hexdigest();v=accepted.get(m);ok=bool(v and v['source_sha256']==sha)
 status.append(dict(module=m,path=str(p.relative_to(R)),sha256=sha,compiled=ok,status='accepted' if ok else 'rejected import-cohort draft; no credit',attempt=v['attempt'] if v else next((x['attempt'] for x in reversed(rows) if x['module']==m),None)))
assert [x['module'] for x in status if not x['compiled']]==['R1Z.PV_RunJoin_CircleInstalled51']
(E/'new-source-credit-status.json').write_text(json.dumps(status,indent=2)+'\n')
plan=json.loads((E/'build-plan.json').read_text())
def closure(root):
 seen=set()
 def walk(m):
  if m in seen:return
  seen.add(m)
  if m in plan['modules']:
   for d in plan['modules'][m]['imports']:walk(d)
 walk(root);return seen
model=closure('R1Z.PV_RunJoin_CombinedAudit51');circle=closure('R1Z.PV_RunJoin_CircleAudit51')
assert not model.intersection({'R1Z.PV_RunJoin_CircleInstalled51','R1Z.PV_RunJoin_PrepareClaimInputs50','R1Z.PV_RunJoin_ClaimModelCell49','R1Z.PV_RunJoin_ClaimModelStream49','R1Z.PV_AL_CircleOwnedTypes'})
assert 'AspisR72Sampler.Types' not in circle
assert set(accepted)<=model|circle
(E/'audit-closure-check.json').write_text(json.dumps(dict(model_root='R1Z.PV_RunJoin_CombinedAudit51',circle_root='R1Z.PV_RunJoin_CircleAudit51',all_current_accepted_covered=True,single_joint_closure=False,reason='checked generated-instance conflict retained',model_closure=sorted(model),circle_closure=sorted(circle)),indent=2)+'\n')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();changed=subprocess.check_output(['git','diff','--name-only','908c552a4e',head],cwd=R,text=True).splitlines()
protected=[p for p in changed if Path(p).name.startswith(('PV_RJDec_','PV_OWN'))];assert not protected
(E/'protected-prefixes-unchanged.json').write_text(json.dumps(dict(base='908c552a4ebd76c73a07e2572eae0b00561bbf04',head=head,protected_prefixes=['PV_RJDec_','PV_OWN*'],changed_protected_paths=protected,byte_identical=True),indent=2)+'\n')
for x in status:
 s=(R/x['path']).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b|set_option\s+max(?:Heartbeats|RecDepth|RecursionDepth)',s),x['module']
(E/'source-shape-check.json').write_text(json.dumps(dict(checked=[x['path'] for x in status],forbidden_terms=[],limits_raised=False,symbolic_aggregations=['ByteArrayList51.loop','RoundCanonicalPhase51.complete'],generated_inherited_circle_options='retained unchanged, circle-prerequisite-authority.json'),indent=2)+'\n')
(E/'local-input-corrections.json').write_text(json.dumps([dict(kind='postprocessing',detail='Copied boundary helper initially contained a prefix-replaced malformed old base hash. Corrected to exact entry before running boundary checks; no compiler or boundary result used it.'),dict(kind='source before first compile',detail='SemanticSourceSuccess51 residual branch and SemanticDigest51 implicit signature were corrected before their first launch; only committed launched revisions receive credit.')],indent=2)+'\n')
print('Own sources',len(status),'accepted',sum(x['compiled'] for x in status),'uncredited',sum(not x['compiled'] for x in status),'accepted module union covered',len(accepted))
