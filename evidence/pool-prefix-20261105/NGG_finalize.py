from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((E/n).read_text())
pairs=[(2,[3]),(4,[5]),(6,[7]),(8,[9]),(10,[11]),(12,[13]),(14,[15]),(22,[23,24,25]),(26,[27,28]),(29,[30]),(31,[32])]+[(n,[n+1]) for n in range(33,89,2)]+[(89,[91])]+[(n,[n+1]) for n in range(92,114,2)]+[(114,[115]),(118,[119])]
matched=[]
for p,ns in pairs:
 a=f'NGG_K{p:03}';pos=read(a+'/receipt.json');assert pos['exit_status']==0,a
 for n in ns:
  b=f'NGG_K{n:03}';neg=read(b+'/receipt.json');log=(E/b/'stdout.log').read_text();checks=[l.strip() for l in log.splitlines() if 'Failed Checks:' in l]
  assert neg['exit_status']==1 and checks and all('assertion' in l or (b=='NGG_K040' and 'placeholder message' in l and 'NGG_DecodeCut.rs", line 41' in log and 'panic!("request kind changed")' in read(b+'-shape.json')['source'].splitlines()[40]) for l in checks),(b,checks)
  assert pos['copy_patch_sha256']==neg['copy_patch_sha256'] and pos['program_features']==neg['program_features']
 matched.append(dict(positive=a,controls=[f'NGG_K{n:03}' for n in ns],classification='matched local fixture ONLY; no production domain/modifies/composed credit'))
(E/'NGG_MATCHED_CONTROLS.json').write_text(json.dumps(dict(pairs=matched,unpaired_positive='NGG_K120 (corrected byte predicate; K116/K117 compile failures)',excluded=['NGG_K001 (length-four branch skipped)','NGG_K016','NGG_K017','NGG_K018 (stopped accidental unchanged submission)','NGG_K019','NGG_K020','NGG_K021','NGG_K090','NGG_K116','NGG_K117'],no_production_credit=True),indent=1)+'\n')
raw=lambda n:[json.loads(l.split('NEP_RESULT ',1)[1]) for l in (E/n/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
fixtures=raw('NGG_B056');roots=raw('NGG_B057');assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert len(roots)==30 and all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in roots)
loaded=[json.loads(l) for l in (E/'NGG_LOADED.jsonl').read_text().splitlines()];own=[r for r in loaded if r['module'].startswith('NGG_')];bad=[r for r in loaded if r['dangling']]
assert len(own)==27 and all(not r['dangling'] for r in own)
metrics={n:{k:read(n+'/receipt.json')[k] for k in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes']} for n in ['NGG_B052','NGG_B053','NGG_B054','NGG_B055','NGG_B056','NGG_B057','NGG_B058','NGG_B059','NGG_B060']}
audit=dict(status='LOCAL RAW AUDIT PASS; COMBINED HEADLINE FAILED; COHERENCE QUALIFIED',production_association='OPEN',composed_rows=0,combined_import={'target':'NGG_COMBINED_IMPORT.lean','attempt':'NGG_B053','exit_status':1,'reason':(E/'NGG_B053/stdout.log').read_text().strip(),'missing_dependency_predecessor':'NGG_B052 (resolved by private retained-object copy)'},raw={'attempt':'NGG_B057','roots':roots,'standard_axioms_only':True,'walker_byte_identical_to_NEP':True,'walker_sha256':read('NGG_AUDIT_PLAN.json')['walker_sha256'],'reachable_artifacts':[dict(path=p.name,sha256=sha(p)) for p in sorted(E.glob('NEP_final_*_REACHABLE.txt'))]},fixtures={'attempt':'NGG_B056','results':fixtures,'same_compiled_driver':True},coherence={'attempt':'NGG_B060','exit_status':1,'modules':len(loaded),'own_modules':len(own),'own_dangling':0,'dangling_references':sum(len(r['dangling']) for r in loaded),'inherited_modules':len(bad),'waived':False,'details':'NGG_LOADED.jsonl','resolved_objects':'NGG_RESOLVED_OBJECTS.json.xz','headline_included':False},metrics=metrics,failed_elaborations_excluded=True,uncompiled_templates=['NGG_CLAIM_AUDIT.lean.txt','NGG_Manifest.lean.txt','NGG_STATEMENTS.lean.txt'],full_frozen_manifest_replay=False)
(E/'NGG_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
closed=dict(status='OPEN',composed_rows=[],native_credit=[],partial_inputs={'matched_local_observation_families':len(matched),'raw_audited_roots':30,'new_loaded_modules':27,'production_domain_evidence':False,'full_emitted_prefix_model':False},excluded_incident='NGG_K018; see NGG_K018-STOP.json',remaining='NGG_REMAINING.md')
(E/'NGG_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n')
delta=dict(prefix='NGG_',rows=[],status='OPEN',basis={'path':'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz','sha256':'01de8c9429d5a2ab14b6d11aa5d8ce3c27e6a9ef72d2489f17eb7293224d4280','rows':599},validator_checks_added=['unchanged NDT.validate_invariants on historical ledger','empty additive delta and no status upgrades','per-receipt caps, swap, source/graph/lock/KMX/feature/optimization gates','matched semantic assertion/panic failures for partial fixtures (K040 source-located panic)','same-driver raw/summary axioms plus eight fidelity fixtures','complete loaded-module dangling scan; 650 defects retained','frozen shipped source and three ELF read-only hash recheck'],validator='NGG_validate.py',new_runtime_trust_used=False,pending_unused_runtime_proposal='NGG_RUNTIME_CPI_PROPOSAL.md',release_claim=False)
(E/'NGG_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
print(json.dumps(dict(matched_families=len(matched),raw_roots=len(roots),new_modules=len(own),dangling=audit['coherence']['dangling_references'],composed_rows=0)))
