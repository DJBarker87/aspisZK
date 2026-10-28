from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent; R=E.parents[1];P=E.parent/'native-reconcile-20261028'
plan=json.loads((P/'NDO_RETARGET_PLAN.json').read_text());seed=json.loads((P/'NDO_SEED_PINS.json').read_text())['objects'];pairs=json.loads((P/'NDO_DUPLICATES.json').read_text())['pairs']
graph={r['module']:r['imports'] for r in seed};seen=set();rows=[]
for r in plan:
 s=(R/'lean'/(r['module']+'.lean')).read_text();imports=[n for line in re.findall(r'^import\s+([^\n]+)',s,re.M) for n in line.split()];graph[r['module']]=imports
 assert set(imports)==set(r['imports'])|({'NDO_PhaseIdentity'} if r['module']=='NDO_JGi_FinishFields' else set()),r['module']
 code=re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
 assert not re.search(r'^\s*(?:axiom|opaque)\s|\b(?:sorry|admit|native_decide)\b',code,re.M),r['module']
 rows.append(dict(module=r['module'],sha256=hashlib.sha256(s.encode()).hexdigest()))
graph['NDO_PhaseIdentity']=['RPz7_PhaseIso'];graph['NDO_InstalledIdentity']=['NDO_JHe_InstalledData','NDO_JHe_FinalInstallation','RPv_IDa_Deployed']
def walk(m):
 if m in seen:return
 seen.add(m)
 assert m in graph,m
 for n in graph[m]:walk(n)
for m in ['RPx_Deployed','NDO_Joint','NDO_InstalledIdentity']:walk(m)
gaps=[]
for p in pairs:
 if p['historical_producer_provenance']:continue
 used=p['historical'] in seen
 assert not used,p['historical']
 gaps.append(dict(historical=p['historical'],historical_object_sha256=p['historical_object_sha256'],historical_source_sha256=p['historical_sha256'],status='historical object not used by retargeted combined closure',replacement=p['replay'],replacement_used=p['replay'] in seen,replacement_object_sha256=p['replay_object_sha256']))
assert len(gaps)==76
(E/'NDR_PROVENANCE.json').write_text(json.dumps(dict(method='Static dependency traversal from both roots plus installed identity, using pinned seed object imports and current NDO source imports. Historical source-to-object pins are not claimed recovered.',closure_count=len(seen),entries=gaps),indent=2)+'\n')
(E/'NDR_SOURCE_PINS.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NDR_PREFLIGHT.json').write_text(json.dumps(dict(modules=len(plan),dependency_graph_check=True,forbidden_proof_tokens_absent=True,closure_count=len(seen),historical_gaps_excluded=len(gaps),status='static checks only; no kernel replay credit'),indent=2)+'\n')
# Inventory exact observer changes already selected in the headline closure.
with (E/'NDR_ADAPTATIONS.md').open('a') as f:
 f.write('\n## The 23 upstream body differences\n\nThese selected replay modules are reused unchanged, rather than copied or patched.\nThe carrier change is `verifier.Phase` (historical alias) → `RPz7_PhaseIso.Phase`\n(retained FirstCaller carrier), except the two special cases stated below.\nNo theorem conclusion or non-observer quantifier is deliberately changed.\n\n')
 for p in pairs:
  if p['body_equal_ignoring_comments_whitespace_imports']:continue
  special={'S1SemanticPhaseV1':'Historical alias `verifier.Phase := FirstCaller.Phase` moves to retained `RPz7_PhaseIso.Phase`; no producer carrier equality.', 'FIr_FinishComparison':'FinishModel calls/proof applications change `obs` → `RPz7_PhaseIso.observerToFirst obs`. A callback map is explicit; this is not a new adaptive execution proof.'}.get(p['historical'],'Observer annotation: `Option (verifier.Phase → Result Unit)` → `Option (RPz7_PhaseIso.Phase → Result Unit)`; other bodies as inventoried by NDO_SOURCE_DIFFS.txt.')
  f.write('- `'+p['historical']+'` → `'+p['replay']+'`: '+special+'\n')
print('preflight passed; 76 unused historical objects; closure',len(seen))
