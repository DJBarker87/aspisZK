"""Verify retained proof receipts and report boundaries; never launches builds."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume'
base='49bf51d3e9afab9691df3d2aacbba4905dda4a05'
def sha(b):return hashlib.sha256(b).hexdigest()
summary=json.loads((e/'summary.json').read_text())
assert summary['lean_compiles']==85
assert [x['attempt'] for x in summary['attempts']]==list(range(12416,12501))
receipts=[json.loads(p.read_text()) for p in sorted(e.glob('*-receipt.json'))]
assert len(receipts)==85
keys=[(x['source_sha256'],x['deps_fingerprint']) for x in receipts]
assert len(keys)==len(set(keys)), 'Repeated unchanged proof input'
assert all(not x['swaps'] or x['swaps']==['0'] for x in summary['attempts'])
accepted=[]
audit=json.loads((e/'audit-targets.json').read_text())
for rel in audit['modules']+['docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessResumeAudit.lean']:
 p=r/rel;s=p.read_text();h=sha(p.read_bytes());module='R1Z/'+p.stem
 matches=[x for x in receipts if x['module']==module and x['source_sha256']==h and x['exit_status']==0]
 assert matches,rel
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),rel
 assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',s),rel
 accepted.append(dict(path=rel,source_sha256=h,accepted_attempts=[x['attempt'] for x in matches],axiom_reports=len(matches[-1]['print_axioms'])))
final=next(x for x in receipts if x['attempt']==12500)
assert final['source_sha256']==audit['audit_sha256']
reported={re.match(r"'([^']+)'",s)[1] for s in final['print_axioms']}
assert reported==set(audit['theorems'])
assert len(reported)==129
roots=[]
for name in ['ProverCommitDeployedFuel22','PrivacyR1HeadlineDeployedReal']:
 rel=f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean'
 old=subprocess.check_output(['git','show',base+':'+rel],cwd=r)
 new=(r/rel).read_bytes();assert old==new
 roots.append(dict(path=rel,unchanged=True,sha256=sha(new),before_after='Byte-identical statements, quantifiers, carriers and conclusions; zero root premises removed'))
inherited=json.loads((e.parent/'success-install/final-state.json').read_text())['selected_source_dictionary']
new_source={37,101,105,107,114,118,260}
ports={33,34,35,36,100,109}
source=set(inherited['installed'])|new_source
candidate=source|ports
open_before=set(inherited['successful_body_unselected_refs'])
assert len(source)==103 and len(candidate)==109 and len(open_before)==50
assert len(open_before-new_source)==43 and len(open_before-new_source-ports)==37
native=json.loads((e/'native/summary.json').read_text())
assert (native['invocations'],native['passed'],native['timeouts'],native['compile_rejections'])==(11,6,4,1)
changed_rust=subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','crates'],cwd=r,text=True).splitlines()
assert changed_rust==['crates/aspis-prover/src/state_only_entropy_prover_rw_stream_kani.rs']
report=dict(base_revision=base,proof_checkpoint=final['source_revision'],accepted_sources=accepted,
 root_targets=roots,conjunct1_premises_removed=0,headline_premises_removed=0,target_established=False,
 selector=dict(name='R1Z.ProverRwSuccessBodyInterpretation.selected',inherited_count=96,
   new_retained_source_entries=sorted(new_source),retained_source_count=103,
   logical_port_entries=sorted(ports),candidate_count=109,full_entry_total=262,
   remaining_source_successful_body_refs=sorted(open_before-new_source),
   remaining_candidate_successful_body_refs=sorted(open_before-new_source-ports),
   partial_entry=dict(id=255,branches=['S1','S2'],retained_callback_branch='D',
     native_array_from_fn_association='OPEN',counted_full=False),
   caution='Interpretation coverage only; native/ABI/feature/library adequacy is separate. Source count is not root premise removal.'),
 lean=dict(attempts=85,passes=summary['passes'],failed_changed_inputs=85-summary['passes'],
   audit_attempt=12500,audit_theorems=129,audit_exit=0,
   audit_wall=summary['attempts'][-1]['wall'],audit_peak_rss_kib=summary['attempts'][-1]['peak_rss_kib'],
   max_peak_rss_kib=max(int(x['peak_rss_kib'][0]) for x in summary['attempts'] if x['peak_rss_kib']),
   swaps=0,limits=final['limits'],remaining_attempts=0,next_unused_id=12501,
   replay='Focused modules then one combined axiom audit; no release or package replay'),
 native=dict(invocations=11,passes=6,timeouts=4,compile_rejections=1,remaining_runs=0,
   scope=native['scope'],production_prefix_unchanged=native['production_prefix_unchanged']),
 resource_barrier='No vanished-cgroup failure in this continuation; race retry exception not used. Infrastructure unchanged.',
 open_obligations=['43 successful-body source references, including partial op255',
   'Native/library adequacy of six logical value ports and ordered array-from-function',
   'Complete proof/audit data equality for the actual BodyContract and native prefix/effects',
   'History-conditioned entropy E1/E2, full terminal coverage and physical Drop/extractor association',
   'Ordered physical ROM/TLS observation and joint oracle/observer transport',
   'Actual per-adversary/per-witness RunJoin, with both marginals and bad-event transport',
   'Frozen release source/feature/artifact association and adoption gates',
   '28 type associations and off-path entries remain with sibling PDict_ owner'],
 security='No reduction in security target, adversary scope, failure event or metric. No new cryptographic assumptions or admitted axioms.')
(e/'final-state.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(accepted),axiom_reports=len(reported),Lean=85,Kani=11,root_premises_removed=0)))
