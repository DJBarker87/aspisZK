"""Record the checked-counterexample stop. This script launches no build."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-batch2-20261027/batch2b');L=Path('docs/research/v8-r0-zk-20261009/lean')
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];latest={}
for n in range(52000,52008):
 r=json.loads((E/f'{n}.json').read_text());ax=r.get('parsed_axioms',[])
 good=all(set(q['axioms'])<=allowed for q in ax)
 j={k:r[k] for k in ['module','attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_sha256','worktree_source_dirty','deps_fingerprint','dependency_objects','limits','cgroup_memory_peak_bytes']}
 j.update(print_axioms=ax,standard_axioms=good,formal_accepted=r['exit_status']==0 and r['accepted_axioms'] and good,receipt=f'{n}.json')
 receipts.append(j)
 if j['formal_accepted']:latest[j['module']]=j
(E/'LEAN-RECEIPTS.json').write_text(json.dumps(receipts,indent=2)+'\n')
checks=[]
for module,r in latest.items():
 p=L/(module+'.lean');checks.append(dict(module=module,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),matches_success=hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],attempt=r['attempt']))
assert all(c['matches_success'] for c in checks)
for c in checks:
 s=Path(c['path']).read_text();assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|implemented_by)\b',s)
(E/'ACCEPTED-CHECK.json').write_text(json.dumps(dict(passed=True,scope='accepted partial modules and counterexample only; no privacy/adoption manifest',sources=checks,drafts='ARCHIVED-DRAFTS.json'),indent=2)+'\n')
tp=E/'TALLY.json';t=json.loads(tp.read_text());t.update(lean_charged=len(receipts),lean_attempts=len(receipts),kani_charged=0,used_ids=[r['attempt'] for r in receipts],remaining_lean_budget=100-len(receipts),stop='checked counterexample to op253 arbitrary-input complete-Result copy equality; no repair permitted',next_env_j_id=52008);tp.write_text(json.dumps(t,indent=2)+'\n')
stages=[]
for stage,prefix in [(1,'build'),(2,'build2'),(3,'build3'),(4,'build4'),(5,'build5')]:
 rows=[]
 for p in sorted((E/'candidate').glob(f'batch2b-{prefix}-*/comparison.json')):
  j=json.loads(p.read_text());r=json.loads((p.parent/'receipt/receipt.json').read_text());j.update({k:r[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']});j['receipt']=str(p.parent.relative_to(E)/'receipt/receipt.json');rows.append(j)
 assert len(rows)==3 and all(r['matches'] and r['exit_status']==0 for r in rows)
 stages.append(dict(stage=stage,source_revision=rows[0]['source_revision'],rows=rows))
(E/'ELF-STAGES.json').write_text(json.dumps(stages,indent=2)+'\n')
scopes=[];holds=[]
for p in sorted((E/'candidate').glob('batch2b-*')):
 q=p/'receipt/receipt.json'
 if q.exists():
  j=json.loads(q.read_text());j['receipt']=str(q.relative_to(E));j['target']=p.name
  j['actual_role']='Lean focused check' if 'lean-' in p.name else 'SBF optimized compilation' if 'build' in p.name else 'optimized finite row/copy native comparison' if 'rowcheck' in p.name else 'optimized Charon compilation and pinned Aeneas extraction'
  assert j['limits']['memory.max']=='8589934592' and j['limits']['memory.high']=='6442450944' and j['limits']['memory.swap.max']=='0' and j['limits']['pids.max']=='64'
  assert j['swaps']==0
  scopes.append(j)
 elif (p/'reservation.json').exists():holds.append(dict(target=p.name,reservation=str((p/'reservation.json').relative_to(E)),allowed=json.loads((p/'reservation.json').read_text())['allowed']))
assert all(h['allowed'] is False for h in holds)
(E/'SCOPE-RECEIPTS.json').write_text(json.dumps(dict(scopes=scopes,admission_holds=holds),indent=2)+'\n')
cex=dict(status='CHECKED; STOP; candidate not repaired',operation=253,row='V260',desired='For every input, copied raw equals the frozen original as a complete Result, including its failure constructor.',witness=dict(variant='D',kind=0,index=1024,weights='any typed factors/points/extra with variant D'),observed=dict(copy='fail Error.assertionFailure',frozen_original='fail Error.arrayOutOfBounds'),kernel_theorem='PV_B2_ErrorCounterexample.op253_copy_error_counterexample',proof_source='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_ErrorCounterexample.lean',certificate_receipt='52007.json',runtime_probe='52005-stdout.log',native_panic_evidence='candidate/batch2b-rowcheck-001/receipt/stderr.log',original_source='crates/aspis-r1-cost-probe/src/transport.rs:11 and weights.rs::Weights::raw(kind0)',copy_source='crates/aspis-r1-cost-probe/src/host_weights.rs::host_row and raw_value',original_table_dependency='The theorem holds for every 1024-element table and every continuation, so no table entries or continuation values are assumed.',scope='The proposed copy/original equivalence obligation fails. All endpoint/deployment statements and ledger rows are retained.')
(E/'COUNTEREXAMPLE.json').write_text(json.dumps(cex,indent=2)+'\n')
summary=dict(branch='codex/pv-batch2-20261027',worktree='/Users/dominic/ZK/.worktrees/pv-canon',start_revision='1fc8463dacad5e75011c0dfbc1ce08cd8ee17a3d',merge=dict(requested_branch='codex/cx-prover-rw-20261023',result='fast-forward, no conflicts',tip='aa27e73f99c51f8399d631e75a9bb517c3d03575'),applied_rust_revision=stages[-1]['source_revision'],stop=cex['status'],target='not yet established',counterexample='COUNTEREXAMPLE.json',elf_gate=dict(all_five_source_stages_passed=True,latest=stages[-1],receipts='ELF-STAGES.json'),source_identity='SOURCE-IDENTITY.json',extraction=dict(current='EXTRACTION-10.json',op251='full 57-function closure and root emitted; types checked, Funs archived uncompiled at counterexample stop',op253='full 39-function closure and root emitted and type-checked; no external template; three unsigned shift literals and one Usize-to-U32 shift-count API cast are explicit adaptations',pinned_tools_unchanged=True),d188=dict(no_copy_writes_through_mutable_iterator_borrow=True,inspection='materialize loop carries Array.update result into next iteration and returns the updated array; shared powers restoration is used in both branches; no discarded mutable restoration found in the new closure',native='Two optimized finite tests passed: all1024 D-table cells, valid output comparisons for 9 constructor cases including malformed raw limbs, boundary panics, and all-ones output cases.',emission_value_differential='NOT RUN: stopped on checked failure-constructor counterexample; full D188 credit is not claimed'),per_op=[dict(op=249,row='V256',proved='prior GammaCarrier complete-Result carrier transport retained',open='gamma rank, original/copy equality, row bridge'),dict(op=250,row='V257',proved='prior unconditional canonical digit and rank-residue laws retained',open='original/copy equality and row bridge'),dict(op=251,row='V258',proved='new full extraction; raw type module checks',open='full function typecheck, totality, allocation/mutation/error transport, original/copy equality and row bridge'),dict(op=252,row='V259',proved='prior field/statement-point totality retained',open='five fixed factor-row proof drafts archived uncompiled; constructor value/totality, original/copy equality and row bridge'),dict(op=253,row='V260',proved='new full extraction/typecheck and kernel-checked error counterexample',open='proposed universal original/copy equality is false for the current candidate; row bridge remains open')],lean_attempts=len(receipts),lean_budget=100,kani_attempts=0,kani_budget=0,used_envj_ids=[r['attempt'] for r in receipts],audit=dict(counterexample_declarations=5,permitted_axioms=sorted(allowed),counterexample_receipt='52007.json',accepted_current_sources='ACCEPTED-CHECK.json',adoption_or_full_manifest='NOT RUN: checked counterexample stop',audit_id_collision='ID-PREFLIGHT.json;52497-52499 already occupied; none used'),fixture_byte_gate='NOT RUN: copy/error/row stage failed; frozen comparison target remains73070ddd51',premises=dict(removed=[],retained=['V256','V257','V258','V259','V260','all existing privacy endpoint and deployment conditions, including native effects and L1/L2/L3'],added_to_endpoint=[],weakened=[],transferred_to_T=[],trust_fields=['entropy_law','entropy_kernel','observation']),new_proof_work=['tuple powers adapter and field canonicalization/from_limbs totality','owned-array mutation and caller allocation transport','closed-form D row association and exact failure behavior','static/dynamic shift-count adapter association'],keys='KEY-RETENTION.json;18 task/SBF keys retained mode0600; no transactions/refunds/key cleanup',shared_envj='No shared source/object write; private sources/objects only',repeated_input_incident='REPEATED-INPUT-INCIDENT.json;52002/52003 both charged and rejected; guard added',receipts=dict(lean='LEAN-RECEIPTS.json',scopes='SCOPE-RECEIPTS.json',admission_holds=holds),next_deliverable='Lead review of the counterexample; any newly authorized copy must preserve the frozen bounds-failure Result before the constructor/copy/row work and fixture-byte/adoption gates can resume. No candidate repair made in this run.')
if (E/'CACHE-CLEANUP.json').exists():summary['cache_cleanup']='CACHE-CLEANUP.json'
history=E.parent/'FINAL-before-batch2b-D303.json'
if not history.exists():history.write_bytes((E.parent/'FINAL.json').read_bytes())
summary['historical_final']=str(history)
summary['evidence_directory']=str(E)
summary['cost_projection']='Prior -12.49644059us/proof projection retained historically; current counterexample candidate was not remeasured or adopted.'
summary['proof_source_mapping']='Compiler revision plus dirty-source SHA and source snapshots are recorded for every attempt; ACCEPTED-CHECK.json binds current proof source bytes to accepted inputs.'
(E/'FINAL.json').write_text(json.dumps(summary,indent=2)+'\n')
(E.parent/'FINAL.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(stop='checked op253 error counterexample',lean=len(receipts),scopes=len(scopes),holds=len(holds),accepted=len(latest),all_elf_stages=len(stages)),indent=2))
