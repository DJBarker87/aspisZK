"""Fail-closed finalization of a host-health stop: never promote on a partial gate."""
from pathlib import Path
import json,lzma,hashlib,collections,copy
E=Path(__file__).resolve().parent;P=E.parent/'ledger17-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1)+'\n').encode();(E/n).write_bytes(raw)
required=J(E/'NKH_AUDIT_ROOTS.json')['roots'];results=[];groups=[]
for i in range(30):
 p=E/f'NKH_audit/batch{i}/proof{i}.json'
 if not p.exists()or not p.stat().st_size:continue
 x=J(p);assert x['exit_status']==0;results+=x['results'];groups.append(i)
assert groups==list(range(16));assert len({r['root']for r in results})==len(results)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results)
missing=sorted(set(required)-{r['root']for r in results});assert missing
scan=[json.loads(l)for l in(E/'NKH_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
put('NKH_SCAN.json',dict(status='PASS_SCAN_ONLY_FULL_GATE_INCOMPLETE',exit_status=0,attempt='NKH_L008',full_combined_import='NKH_COMBINED_IMPORT',modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,canonical_duplicate_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan)))
fx=J(E/'NKH_audit/fixtures/fixtures.json');assert fx['results']==J(P/'NKC_audit/fixtures/fixtures.json')['results']and len(fx['results'])==8
rs=[json.loads(l)for l in(E/'NKH_ATTEMPTS.jsonl').read_text().splitlines()];prior_unresolved=[r for r in rs if r['attempt']=='NKH_L025'];rs=[r for r in rs if r['attempt']!='NKH_L025'];assert len(rs)==24 and len(prior_unresolved)<=1
x=J(E/'NKH_L025.json');ad=J(E/'NKH_L025-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True
entry=dict(attempt='NKH_L025',kind='audit',module='batch16',sources=x['sources'],command=x['command'],source_revision=x['source_revision'],source_tree_dirty=x['source_tree_dirty'],deps_fingerprint_reference='NKH_L025.json',exit_status=None,launcher_exit_status=1,wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms=[],axioms_status='UNAVAILABLE; host ENOSPC left stdout/time/receipt/proof16 JSON empty',requested_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),full_receipt='NKH_L025/receipt.partial.json.txt',host_finding='NKH_HOST_FINDING.json',submitted=True,resubmitted=False)
if prior_unresolved:assert prior_unresolved==[entry]
else:
 with(E/'NKH_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(entry)+'\n')
resources=dict(submitted_scopes=25,complete_receipts=24,budget_scopes=40,unused_scopes=15,stop_reason='local-lean.txt rule5 host health: S2W_run_host.py receipt write ENOSPC; host free0; no further formal launches permitted',complete_scope_wall_seconds=sum(r['wall_seconds']for r in rs),complete_scope_peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),complete_scope_swaps=sum(int(r['swaps'])for r in rs),unresolved_metrics=['NKH_L025 wall/peakRSS/swap/childexit/axioms unavailable'],kinds_complete=dict(collections.Counter(r['kind']for r in rs)),kani=0,extraction=0,aggregation16G_scopes=0)
put('NKH_RESOURCES.json',resources)
binary=J(E/'NKH_L006/NKH_ProofDriver_BINARY_PIN.json')['sha256']
for r in rs:
 p=E/r['attempt']/'NKH_ProofDriver_BINARY_PIN.json'
 if p.exists():assert J(p)['sha256']==binary
put('NKH_AUDIT.json',dict(status='INCOMPLETE_HOST_DISK_FULL_NO_ADMISSIONS',full_composition_pass=False,combined_import_pass=True,combined='NKH_COMBINED_IMPORT',combined_attempt='NKH_L001',headline='AspisR1.RPx_Deployed.deployed',required_roots=len(required),audited_raw_roots=len(results),complete_groups=groups,missing_groups=list(range(16,30)),missing_roots=missing,all_required_raw_roots_present=False,partial_raw_standard_axioms_only=True,raw_standard_axioms_only=False,partial_axioms=sorted({a for r in results for a in r['walked_axioms']}),collect_axioms_disagreements=[r for r in results if not r['equal']],inherited_collector_disagreement=dict(root='NHC_DecodeModel.decoder_error',ruling="(ab')(3)",status='RETAINED_FROM_NKC; current group not completed, no verdict relabelled'),same_optimized_proof_binary_sha256=binary,fixtures=fx['results'],scanner='NKH_SCAN.json',resources=resources,security_target_established=False,cold_release_replay=False,gate_blocker='Incomplete all-root raw ax2 + uncompiled L039 complete-hypothesis/matcher-owner print + unrun L040 closure pin/export'))
basis=J(P/'NKC_LEDGER.json.xz')
# Exact unchanged NKC snapshot: existing PASS belongs to NKC, not this refresh.
(E/'NKH_LEDGER.json.xz').write_bytes((P/'NKC_LEDGER.json.xz').read_bytes());(E/'NKH_LEDGER.json.sha256').write_text(H(lzma.decompress((E/'NKH_LEDGER.json.xz').read_bytes()))+'\n')
review=J(E/'NKH_CANDIDATE_REVIEW.json');proposals=[r['row']for r in review['rows']];assert len(proposals)==len(set(proposals))==28
put('NKH_LEDGER_DELTA.json',dict(schema_version=1,basis='evidence/ledger17-20261108/NKC_LEDGER.json.xz',basis_sha256=H((P/'NKC_LEDGER.json.xz').read_bytes()),snapshot_byte_identical_to_basis=True,before=dict(CLOSED=514,QUALIFIED=0,OPEN=85),after=dict(CLOSED=514,QUALIFIED=0,OPEN=85),new_count=0,new_closed_rows=[],rows=[],proposed_rows=proposals,rejected_for_this_gate=[dict(row=r['row'],module=r['primary_root'],missing_clause='Full all-root combined audit incomplete after host ENOSPC',additional_missing_roots=r['missing_kernel_roots'])for r in review['rows']],no_double_count=True,no_other_status_change=True,gate='INCOMPLETE_HOST_HEALTH_STOP',supplement_status=dict(id='NJW-aw-TX2:115-off-domain',status='OPEN',proposed='NJU generalized all-current-word complete115 law',missing='Required combined all-root gate incomplete; no supplement promotion'),explicit_parent_clause_proposals=J(E/'NKH_PARENT_CLAUSES.json'),reviewed_transcription_additions=[],pending_reviewed_transcription_items=J(E/'NKH_COVERAGE.json')['trust_additions'],trust_rows_changed=False,security_target_established=False))
sup=J(E/'NKH_SUPPLEMENT_REVIEW.json');sup['status']='OPEN_GATE_INCOMPLETE_HOST_DISK_FULL';sup['missing']='Complete all-root gate/closure pins not obtained; generalized candidate not admitted';put('NKH_SUPPLEMENT_REVIEW.json',sup)
put('NKH_TRUST_INVENTORY.json',dict(runtime_cryptographic_rows_unchanged=True,added_reviewed_transcription_items=[],pending_reviewed_transcription_items=J(E/'NKH_COVERAGE.json')['trust_additions'],removed=[],classification='Option-A P6/D188 RECLASSIFICATION only if subsequently gated; zero actual changes here',runtime_rows_sha256=H(json.dumps(basis['trust_rows'],sort_keys=True).encode())))
print(json.dumps(dict(status='NO_ADMISSIONS_GATE_INCOMPLETE',closed=514,open=85,qualified=0,audited_roots=len(results),missing_roots=len(missing),submitted_scopes=25)))
