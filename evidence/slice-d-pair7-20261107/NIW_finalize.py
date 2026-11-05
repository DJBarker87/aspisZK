"""Summarize completed receipts without promoting open roots."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
rows=[json.loads(l)for l in(E/'NIW_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt']for r in rows})==len(rows)
lean=[r for r in rows if r['attempt'].startswith('NIW_L')];kani=[r for r in rows if r['attempt'].startswith('NIW_K')]
assert len(lean)==51 and len(kani)==10
scoped=[r for r in lean if r.get('launched') is not False]
assert len(scoped)==50
final=json.loads((E/'NIW_final_audit/RESULT.json').read_text());assert final['status']=='PASS' and final['roots']==54
fixtures=[json.loads(l[11:])for l in(E/'NIW_L027/stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
assert len(fixtures)==8 and all(r['equal']for r in fixtures)
retained=json.loads((E/'NIW_RETENTION.json').read_text())
validation=json.loads((E/'NIW_VALIDATION.json').read_text());assert validation['status']=='PASS'
def metric(a):
 r=next(r for r in rows if r['attempt']==a)
 return {k:r.get(k)for k in ['attempt','module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','source_hashes','deps_fingerprint']}
audit=dict(status='PASS_SUPPORTING_OBJECTS_ROOTS_OPEN',headline='AspisR1.RPx_Deployed.deployed',headline_established=False,promoted_rows=[],combined=metric('NIW_L050'),final_raw_ax2_and_NFX=metric('NIW_L051'),result=final,fixtures={'attempt':'NIW_L027','count':8,'all_expected':True,'same_proof_binary':True},native_pairs=validation['positive_control_pairs'],accepted_sources=validation['accepted_sources'],standard_axioms=['propext','Classical.choice','Quot.sound'],native_timeouts_excluded=['NIW_K005','NIW_K007'],other_exclusions=['NIW_K001 compile failure','NIW_K003 count-only control, no copy-specific credit'],budgets={'kani_used':10,'kani_limit':10,'lean_link_audit_charged':51,'lean_link_audit_scopes':50,'lean_link_audit_limit':160,'lean_remaining':109,'extraction_used':0,'extraction_limit':0},audit_cadence='L038 checks the prior 42-root closure; L039-L042 add/check whole-Vec decoding. L043-L048 add the supplied-native guard projection/control/actual rejection witnesses; L049/L050 compile that changed root/combined closure and L051 checks its 54 roots. Prior audits/graphs are retained under NIW_L038 and NIW_L042. Each replay follows changed semantic source; no unchanged regression.',retained={'workspace':retained['workspace'],'cargo_target_dir':retained['cargo_target_dir'],'modules':retained['modules'],'closure_files':len(retained['closure_files']),'manifest':'NIW_RETENTION.json','seed':'NIW_SEED.json','native_seed':'NIW_NATIVE_SEED.json','no_cache_deleted':True},trust='No additions/removals; local cut transcriptions are retained P6/D188 option-A semantic-transport reclassification. Pending runtime rows/exporter predicates unused.',scope='Focused cached proofs and supporting coherent closure/audit, not a full frozen release replay or new ELF reproduction.',remaining='NIW_OPEN_EDGE.md / NIW_REMAINING.md; clarification pending on CLOSED per-child call graphs versus the endpoint-equality premise ban')
(E/'NIW_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
# Complete exact final statements are retained as Lean sources plus per-target
# source snapshots/prints; the open roots have no invented positive theorem.
(E/'NIW_STATEMENTS.json').write_text(json.dumps({'accepted_source_attempts':validation['accepted_sources'],'roots_manifest':'NIW_AUDIT_ROOTS.json','open_obligation_statements':'NIW_CLOSED.json','positive_native_root_theorems':[]},indent=2)+'\n')
print(json.dumps({'status':audit['status'],'raw_roots':54,'modules':final['modules'],'lean_charged':51,'kani':10}))
