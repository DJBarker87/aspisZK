"""Record current source credit and audit closure; never promote failed drafts."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin50-20261029'
rows=[dict(v,attempt=int(p.stem.split('-')[1])) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
accepted={v['module']:v for v in rows if v['accepted']};status=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RunJoin_*50.lean')):
 m='R1Z.'+p.stem;sha=hashlib.sha256(p.read_bytes()).hexdigest();v=accepted.get(m);ok=bool(v and v['source_sha256']==sha)
 status.append(dict(module=m,path=str(p.relative_to(R)),sha256=sha,compiled=ok,status='accepted' if ok else 'rejected current draft; no credit',attempt=v['attempt'] if v else next((x['attempt'] for x in reversed(rows) if x['module']==m),None)))
assert [x['module'] for x in status if not x['compiled']]==['R1Z.PV_RunJoin_PrepareClaimInputs50']
(E/'new-source-credit-status.json').write_text(json.dumps(status,indent=2)+'\n')
plan=json.loads((E/'build-plan.json').read_text());seen=set()
def walk(m):
 if m in seen:return
 seen.add(m)
 if m in plan['modules']:
  for d in plan['modules'][m]['imports']:walk(d)
walk('R1Z.PV_RunJoin_CombinedAudit50')
assert not seen.intersection({'R1Z.PV_RunJoin_PrepareClaimInputs50','R1Z.PV_RunJoin_ClaimModelCell49','R1Z.PV_RunJoin_ClaimModelStream49'})
assert set(accepted)<=seen
(E/'audit-closure-check.json').write_text(json.dumps(dict(root='R1Z.PV_RunJoin_CombinedAudit50',all_current_accepted_covered=True,rejected_current_and_inherited_drafts_excluded=True,closure=sorted(seen)),indent=2)+'\n')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only','e8fb711bc5',head],cwd=R,text=True).splitlines()
assert not [p for p in changed if '/PV_RJDec_' in p or '/PV_OWN_' in p]
(E/'protected-prefixes-unchanged.json').write_text(json.dumps(dict(base='e8fb711bc52fad638e0b7d85d86a9170791210e0',head=head,protected_prefixes=['PV_RJDec_','PV_OWN_'],changed_protected_paths=[],byte_identical=True),indent=2)+'\n')
for x in status:
 s=(R/x['path']).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b|set_option\s+max(?:Heartbeats|RecDepth|RecursionDepth)',s),x['module']
(E/'source-shape-check.json').write_text(json.dumps(dict(checked=[x['path'] for x in status],forbidden_terms=[],limits_raised=False,claim_aggregation='PV_RunJoin_ClaimStreamCongruence49.complete, induction over abstract cells',gamma_aggregation='GammaSourceCell50 and GammaCellTransport50 lane induction; PrefixFold50 row induction'),indent=2)+'\n')
(E/'local-input-corrections.json').write_text(json.dumps([dict(kind='preflight exclusion list',detail='Initial own preflight omitted four inherited rejected drafts; corrected explicit exclusions before any compiler. No launch or ID consumed.'),dict(kind='copied evidence metadata',detail='Updated tally and boundary metadata from runjoin49 IDs/base to assigned runjoin50 IDs and actual entry. Compiler wrapper was already correct for every launch.'),dict(kind='uncompiled source correction',detail='ScalarResultModel50 used a newly isolated generic ResultMap50.bind before its first compile; no compiler was launched for that intermediate source.'),dict(kind='postprocessing',detail='Initial status collector expected an attempt key in per-module records. Corrected by reading the enclosing modules-ID filename. This happened after all 100 launches and consumed no ID.')],indent=2)+'\n')
print('source statuses',len(status),'accepted',sum(x['compiled'] for x in status),'uncredited',sum(not x['compiled'] for x in status),'closure',len(seen))
