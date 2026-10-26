"""Read-only final evidence validation. No builds, infrastructure or source writes."""
from pathlib import Path
import json,hashlib,re,subprocess
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-next'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((e.parent/'success-resume/final-state.json').read_text());audit=json.loads((e/'audit-targets.json').read_text());summary=json.loads((e/'summary.json').read_text());accepted=[]
for rel in [*audit['files'],'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessNextAudit.lean']:
 p=r/rel;digest=sha(p);matches=[]
 for ip in e.glob('*-input.json'):
  x=json.loads(ip.read_text())
  if x['source_sha256']==digest:
   z=json.loads(ip.with_name(ip.name.replace('-input','-receipt')).read_text())
   if z['exit_status']==0:matches.append(z['attempt'])
 assert matches,(rel,digest)
 accepted.append(dict(path=rel,sha256=digest,accepted_attempts=matches))
roots=old['root_targets']
for x in roots:assert sha(r/x['path'])==x['sha256']
rec=json.loads((e/'12829-receipt.json').read_text());assert rec['exit_status']==0 and len(rec['print_axioms'])==audit['count']==39
native=[];critical=['crates/aspis-core/src/r0/scalar.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/field/wide_exact.rs']
for p in sorted((e/'translation').glob('*/receipt.json')):
 x=json.loads(p.read_text());row=dict(attempt=x['attempt'],command=x['target'],exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],limits=x['limits'])
 row['raw_source_revision_label']=x['source_revision']
 row['note']='Historical host label; exact source hashes identify inputs. No native release/adoption evidence.'
 for q in critical:
  assert x['source_sha256'].get(q)==sha(r/q),(p,q)
 row['critical_native_source_matches_worktree']=True
 native.append(row)
# Retain the exact old proof-entrypoint snapshots, checked against immutable receipts.
lib=(r/'tools/prover-rw-20261023/success-install/ports/lib.rs').read_text().splitlines(keepends=True)
entrypoints=[]
for name,n,receipt in [('wide',4,'success-ports-charon-001'),('vectors',8,'success-vectors-charon-001'),('compression',len(lib),'success-compress-charon-001')]:
 text=''.join(lib[:n]);x=json.loads((e/'translation'/receipt/'receipt.json').read_text());key='tools/prover-rw-20261023/success-install/ports/lib.rs';digest=hashlib.sha256(text.encode()).hexdigest();assert digest==x['source_sha256'][key],(name,digest,x['source_sha256'][key])
 (e/f'{name}-entrypoints.rs.txt').write_text(text);entrypoints.append(dict(kind=name,sha256=digest,receipt=receipt))
# The host receipt resolver uses root-relative lib.rs; correct only the evidence interpretation.
x=json.loads((e/'translation/success-ports-aeneas-002/receipt.json').read_text());artifact=next(iter(x['input_artifacts'].values()));binding=artifact['source_bindings']['lib.rs'];assert binding['llbc_source_sha256']==entrypoints[0]['sha256']
remaining=[i for i in old['selector']['remaining_source_successful_body_refs'] if i not in [81,100,109,256]]
assert len(remaining)==39
result=dict(proof_checkpoint=audit['proof_checkpoint'],accepted_sources=accepted,root_targets=roots,conjunct1_premises_removed=0,headline_premises_removed=0,target_established=False,
 selector=dict(source_interpretation_count=107,candidate_interpretation_count=111,total=262,new_source_equations=[81,100,109,256],remaining_source_successful_body_refs=remaining,remaining_source_count=39,remaining_candidate_unselected_count=35,remaining_logical_ports=[33,34,35,36],partial255_counted=False,qualification='Source equations under unchanged retained primitive bindings; these are not whole native execution, ABI or compiler adequacy certificates.'),
 lean=dict(compiles=summary['lean_compiles'],passes=summary['passes'],failures=summary['lean_compiles']-summary['passes'],budget=100,remaining=100-summary['lean_compiles'],next_unused_id=12830,audit_attempt=12829,audit_theorems=39,audit_time=rec['time_log'],limits=rec['limits'],scope='Focused accepted-source audit only; no full manifest'),
 native=dict(kani_runs=0,kani_budget=15,kani_remaining=15,source_extraction_and_translation_receipts=native,entrypoint_snapshots=entrypoints,relative_source_resolver_correction='Raw receipt marks source-map consistency false because lib.rs was resolved against workspace root. Its immutable LLBC content hash equals the exact ports/lib.rs snapshot and original preflight pin. Dependency source/ABI/feature/artifact association remains open; no raw receipt overwritten.'),
 open_obligations=['39 successful-body source references, including four unassociated Vec ports and partial255','Whole native adequacy of primitive field/pow/option bindings and representation/compiler/feature association','Actual proof/audit data equality against the security model; concrete BodyContract/PrefixContract','E1/E2, entropy/Drop/callback extraction, physical ordered ROM/TLS and observer histories','Per-adversary/per-witness real RunJoin with both exact marginals and fixed bad-event transport','Frozen artifact/release association and adoption; 28 type associations remain with sibling owner'],
 stopped_items=dict(checked_mask117='Checked/release raw overflow counterexample retained; source not installed',pole258='Inherited backend cannot join nested-loop contexts',vec_default35='Unsupported Alignment-to-NonNull pointer transmute in native standard library',vec_empty34='Cannot retrieve variants of non-ADT opaque Vec carrier',compression223='Internal Not_found in InterpReduceCollapse.collapse_ctx_following_sequence; no certificate'),
 infrastructure='Only authorized launcher ID range extended; exact diff retained. No backend, monitor or resource-cap changes; race exception not needed.',security='No changed security contract, adversary, failure event or metric. No release/privacy result. No key altered.')
(e/'final-state.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(accepted_sources=len(accepted),lean=result['lean'],remaining_source_references=39,root_premises_removed=0),indent=2))
