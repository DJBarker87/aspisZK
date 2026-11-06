from pathlib import Path
import json,lzma,hashlib,re,collections,subprocess
E=Path(__file__).resolve().parent
load=lambda p:json.loads((E/p).read_text())
receipts={p.parent.name:json.loads(p.read_text())for p in E.glob('NKM_[LKE][0-9][0-9][0-9]/receipt.json')}
def results(a):return [json.loads(l[11:])for l in(E/a/'stdout.log').read_text().splitlines()if l.startswith('NEP_RESULT ')]
roots=load('NKM_AUDIT_ROOTS.json')['roots'];raw=results('NKM_L033')+results('NKM_L034');fixtures=results('NKM_L031')
std={'propext','Classical.choice','Quot.sound'}
assert {r['root']for r in raw}==set(roots) and len(raw)==len(roots)
assert all(r['equal']and set(r['walked_axioms'])<=std and set(r['collect_axioms'])==set(r['walked_axioms'])for r in raw)
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
assert len(fixtures)==8 and all(r['equal']and r['walked_axioms']==expected[r['root']]for r in fixtures)
scan=[json.loads(l)for l in(E/'NKM_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
for a in ['NKM_L050','NKM_L024','NKM_L031','NKM_L032','NKM_L033','NKM_L034','NKM_L010']:assert receipts[a]['exit_status']==0
pairs=[('NKM_K004','NKM_K005'),('NKM_K006','NKM_K007'),('NKM_K008','NKM_K009'),('NKM_K017','NKM_K018'),('NKM_K019','NKM_K020'),('NKM_K021','NKM_K022'),('NKM_K026','NKM_K028'),('NKM_K029','NKM_K030')]
for p,n in pairs:
 assert receipts[p]['exit_status']==0 and receipts[n]['exit_status']==1
 s=(E/n/'stdout.log').read_text();assert 'VERIFICATION:- FAILED'in s and 'CBMC timed out'not in s
for a in ['NKM_K025','NKM_K027']:assert 'CBMC timed out'in(E/a/'stdout.log').read_text()
for a in [f'NKM_K{i:03}'for i in range(2,31)]:
 x=load(a+'-graph-check.json');assert x['graph_matches_frozen']
 y=load(a+'-lock-check.json');assert y['unchanged']
# Record dispositions independent of harness exit code: controls/timeouts are never passes.
dispositions=[]
for a,r in sorted(receipts.items()):
 s=(E/a/'stdout.log').read_text();status='TIMEOUT'if'CBMC timed out'in s else 'PASS'if r['exit_status']==0 else 'ASSERTION_FAIL'if'VERIFICATION:- FAILED'in s else 'ERROR'
 dispositions.append(dict(attempt=a,kind=r['kind'],module=r['module'],status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],receipt=a+'/receipt.json'))
(E/'NKM_RESULTS.json').write_text(json.dumps(dispositions,indent=2)+'\n')
stats=dict(modules=len(scan),declarations=sum(r['declarations']for r in scan),references=sum(r['edges']for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r['cached_replicas'])for r in scan))
audit=dict(status='PASS',combined=dict(attempt='NKM_L050',exit=0,headline='AspisR1.RPx_Deployed.deployed'),statement_review=dict(attempt='NKM_L024',exit=0,inventory='NKM_HYPOTHESES.md'),scan=dict(attempt='NKM_L032',exit=0,**stats),raw_ax2=dict(attempts=['NKM_L033','NKM_L034'],exit=0,own_roots=86,headline_roots=1,standard_axioms_only=True,all_equal_collectAxioms=True,results=raw),fixtures=dict(attempt='NKM_L031',exit=0,results=fixtures,same_binary=load('NKM_FINAL_STATE.json')['binary_pins']['NKM_native/NKM_ProofDriver']),walker=load('NKM_TOOL_INPUT_PINS.json'),full_audits=1,focused_combined_imports=[dict(attempt='NKM_L046',exit=0,scope='before explicit emitted multiplication supplement'),dict(attempt='NKM_L023',exit=1,scope='new supplement imported duplicate JFv owner; excluded'),dict(attempt='NKM_L050',exit=0,scope='canonical-owner repaired final import')],cold_release_replay=False)
(E/'NKM_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
base=load('NKM_BASELINE.json');functions=[]
configs={
 'TX1:NGB006':dict(lean_roots=['NKM_Roots.circle','NKM_CircleModel.circle_source','NKM_Trace.complete','NKM_Domains.all_arguments','NKM_EmittedMul.emitted_exact'],native_pairs=[list(pairs[0]),list(pairs[3]),list(pairs[6]),list(pairs[7])],root_domain='all canonical QM31 parameters; exact field quantifier includes poles; no nonzero denominator premise',route='(y)/(ai)(5)/(aq)(5); universal canonical-reply parent cut and contract, split natural-spec field boundary after K025 timeout, CLOSED child laws'),
 'TX1:NGB004':dict(lean_roots=['NKM_Roots.ood','NKM_Adopted.ood','NKM_OuterTrace.complete','NKM_OuterTrace.error_order'],native_pairs=[list(pairs[1]),list(pairs[4]),list(pairs[7])],root_domain='same canonical parameter as 006; full child Result before c1 comparison',route='(y)/(aq)/(aq)(5); source-ordered full-Result child substitution'),
 'TX1:NGB002':dict(lean_roots=['NKM_Roots.fallback','NKM_Adopted.fallback','NKM_FallbackTrace.complete','NKM_FallbackTrace.error_arm_unreachable','NKM_FallbackCertificate.certificate0','NKM_FallbackCertificate.certificate1','NKM_FallbackModel.caller_domain'],native_pairs=[list(pairs[2]),list(pairs[5]),list(pairs[7])],root_domain='native all usize; composed source domain First->0 / Second->1 established at frozen r0_transcript.rs:179',route='(y)/(aq)/(aq)(5); fixed parameter certificates; both Err arms modeled and proved unreachable on caller domain')
}
for row in base['rows']:
 item=dict(rows=[row['row']],function=row['function'],canonical_callees=row['canonical_callees'],baseline_obligation_statement_hash=row['obligation_statement_hash'],frozen_body_sha256=row['frozen_body_sha256'],complete_carrier=True,premise_policy='NKM_HYPOTHESES.md; all child Result/domain clauses discharged, no endpoint/success/free Ops premise',trust='P6/D188 option A RECLASSIFICATION only; no added runtime/crypto trust; explicit reviewed native callee cuts',status='GATED_CANDIDATE_AWAITING_NEXT_LEDGER',**configs[row['row']]);functions.append(item)
closed=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',headline='AspisR1.RPx_Deployed.deployed',functions=functions,admission=audit,status='GATED_CANDIDATE_AWAITING_NEXT_LEDGER',validation=dict(native_timeout_exclusions=['NKM_K025','NKM_K027'],unresolved=['NKM_L005'],no_timeout_or_memory_cap_increase=True,source_assessment=load('NKM_SOURCE_ASSESSMENT.json'),postflight=load('NKM_POSTFLIGHT.json')),target_established=False)
(E/'NKM_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
delta=dict(baseline='evidence/ledger18-20261108/NKH_LEDGER.json.xz',baseline_sha256=base['baseline_sha256'],baseline_counts=dict(CLOSED=542,QUALIFIED=0,OPEN=57,total=599),authoritative_counts_changed=False,credited_rows=0,submitted_candidates=3,rows=[dict(row=r['rows'][0],previous_status='OPEN',candidate_status=r['status'],baseline_obligation_statement_hash=r['baseline_obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],canonical_callees=r['canonical_callees'],root_owners=r['lean_roots'],source_packet='NKM_CLOSED.json')for r in functions],pending_action='Next authoritative ledger gate reviews split-field replacement and composes the three submitted rows; no direct ledger modification',target_established=False)
(E/'NKM_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
summary=dict(receipts=len(receipts),budget=dict(Kani_slots=30,Kani_invocations=29,Kani_setup=1,Lean_slots=50,Lean_receipts=48,Lean_unresolved='NKM_L005',Lean_prelaunch_missing_alias='NKM_L021',extraction_slots=2,actual_extractions=1,preflight_failures=1),total_wall_seconds=sum(float(r['wall_seconds'])for r in receipts.values()),peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts.values()),swaps=sum(int(r['swaps'])for r in receipts.values()),audit=stats)
(E/'NKM_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
# Verify every lossless raw-walk evidence pair before final staging.
for p in E.glob('NEP_*_REACHABLE.txt.xz'):
 raw=lzma.decompress(p.read_bytes());assert hashlib.sha256(raw).hexdigest()==p.with_suffix('.sha256').read_text().strip(),str(p)
print(json.dumps(dict(audit='PASS',candidates=3,credited=0,scopes=len(receipts),scan=stats)))
