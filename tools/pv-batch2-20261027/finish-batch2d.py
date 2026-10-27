"""Compile-free, evidence-only handoff after the mandatory host barrier stop."""
from pathlib import Path
import json,hashlib,re,subprocess,ast
R=Path.cwd();E=Path('evidence/pv-batch2-20261027/batch2d');L=Path('docs/research/v8-r0-zk-20261009/lean');t=json.loads((E/'TALLY.json').read_text());stop=json.loads((E/'HOST-BARRIER-STOP.json').read_text());allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];latest={}
for a in t['attempts']:
 if not a.get('charged'):continue
 r=json.loads((E/f"{a['id']}.json").read_text());assert r['attempt']==a['id']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0
 row={k:r.get(k) for k in ['attempt','module','source_revision','source_sha256','source_git_blob_at_head','source_worktree_git_blob','worktree_source_dirty','deps_fingerprint','dependency_objects','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','cgroup','cgroup_memory_peak_bytes','accepted_axioms']}
 row['print_axioms']=r.get('parsed_axioms',[]) if r['exit_status']==0 else 'REJECTED candidate; full output retained, including recovery axioms'
 row['receipt']=str(E/f"{a['id']}.json");receipts.append(row);latest[r['module']]=r
assert len(receipts)==t['lean_charged']==78
(E/'LEAN-RECEIPTS.json').write_text(json.dumps(receipts,indent=2)+'\n')
objects={a['path'].removeprefix('lean-objects/').removesuffix('.olean'):a for a in json.loads((E/'OUTPUT-OBJECT-PINS.json').read_text())}
accepted=[]
for m,r in sorted(latest.items()):
 if r['exit_status']!=0 or not r['accepted_axioms']:continue
 hp=json.loads((E/'H5-SOURCE-PINS.json').read_text()).get(m);p=Path(hp['path']) if hp else L/(m+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],m
 assert all(set(a['axioms'])<=allowed for a in r['parsed_axioms'])
 assert m in objects,m
 accepted.append(dict(module=m,path=str(p),source_sha256=r['source_sha256'],source_git_blob_at_handoff=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),attempt=r['attempt'],declarations=r['parsed_axioms'],object_pin=objects[m]))
for p in (L/'R1Z').glob('PV_B2_D_*.lean'):
 assert any(a['module']=='R1Z/'+p.stem for a in accepted),('unaccepted new source in main tree',str(p))
(E/'ACCEPTED-PROGRESS.json').write_text(json.dumps(dict(scope='checked source/copy-kernel laws only; no frozen-original equivalence or ledger closure',sources=accepted),indent=2)+'\n')
checks=[]
for name in ['raw-types-batch2d','constructor-environment-batch2d','discriminants-batch2d','row-source-batch2d','row-range-batch2d','from-limbs-batch2d','raw-total-batch2d','table-batch2c','table-range-batch2c','cps-rows-batch2c','stages-batch2c','success-batch2c','sampler-batch2c','gamma-model-batch2c','field251-batch2c','wide251-batch2c']:
 cmd=['python3','tools/pv-batch2-20261027/'+name+'.py','--check'];r=subprocess.run(cmd,capture_output=True,text=True);checks.append(dict(generator=name,command=cmd,exit=r.returncode,output=r.stdout+r.stderr));assert r.returncode==0,(name,r.stdout,r.stderr)
(E/'GENERATOR-CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
subprocess.run(['python3','tools/pv-batch2-20261027/transport-preflight-batch2d.py'],check=True)
# Every successful new theorem has a direct, standard-axiom receipt. Private
# names are excluded from draft commands, as required by the prior audit finding.
names=sorted({d['declaration'] for a in accepted for d in a['declarations'] if '_private.' not in d['declaration']})
roots=['R1Z.PV_B2_D_MaterializeTotal','R1Z.PV_B2_C_ConstructorSuccess','R1Z.PV_B2_C_DRowResult','R1Z.PV_B2_C_NativeGammaCarrier','R1Z.PV_B2_D_CarrierUnion','R1Z.PV_B2_C_ShiftAdapter']
# Draft only: sampler source-cohort restoration is blocked at39887.
old=json.loads((E.parent/'batch2c/AUDIT-PREFLIGHT.json').read_text())
sampler=[a for a in old['accepted'] if any(x in a['module'] for x in ['Gamma','Sampler','AddSmall','MachineArithmetic','U32Arithmetic'])]
names=sorted(set(names)|{d['declaration'] for a in sampler for d in a['declarations'] if '_private.' not in d['declaration']})
d=E/'drafts';d.mkdir(exist_ok=True)
(d/'PV_B2_D_AuditManifest.lean.txt').write_text('-- UNCOMPILED partial source-law audit; no privacy/release closure claim.\n'+''.join('import '+m+'\n' for m in roots)+'\n'+''.join('#print axioms '+n+'\n' for n in names))
closings=['PV_B2_D_MaterializeTotal.source','PV_B2_C_ConstructorSuccess.new_total','PV_B2_C_ConstructorSuccess.new_eq_staged','PV_B2_C_DRowResult.complete','PV_B2_C_GammaSource.op249_source','PV_B2_C_ordinary_sample.op250_source']
(d/'PV_B2_D_AuditClosure.lean.txt').write_text('import R1Z.PV_B2_D_AuditManifest\n'+''.join('#print axioms '+n+'\n' for n in closings))
(E/'AUDIT-HANDOFF.json').write_text(json.dumps(dict(status='NOT RUN: fatal host barrier error',reserved_ids=[39897,39898,39899],draft_manifest=str(d/'PV_B2_D_AuditManifest.lean.txt'),declarations=len(names),draft_closure=str(d/'PV_B2_D_AuditClosure.lean.txt'),pending_prerequisite='R1Z/PV_B2_C_SamplerEnvironment and remaining sampler queue',private_name_commands_excluded=True),indent=2)+'\n')
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();log=subprocess.check_output(['git','log','--oneline','bcde8ada4f..HEAD'],text=True);(E/'git-log-since-bcde8ada4f.txt').write_text(log)
unused=[n for n in range(39800,39900) if n not in {a['id'] for a in t['attempts']}]
report=dict(status='STOP_HOST_BARRIER_ERROR',branch='codex/pv-batch2-20261027',worktree=str(R),start_revision='bcde8ada4f86608ebca8222d1eb87233f28efbe0',source_revision_before_handoff_commit=head,target='not yet established',stop=stop,lean_charged=t['lean_charged'],lean_budget=100,remaining_lean_budget=100-t['lean_charged'],kani_charged=0,kani_budget=0,allocated_ids=[39800,39899],used_ids=[a['id'] for a in t['attempts']],unused_ids=unused,audit_ids=[39897,39898,39899],uncharged=dict(reservation_holds=9,fatal_barrier_errors=1),receipts='LEAN-RECEIPTS.json',accepted='ACCEPTED-PROGRESS.json',generated_instance_fix=dict(generator='tools/pv-batch2-20261027/discriminants-batch2d.py and raw/constructor generators',reference='317a687e34',smallest_checks=[39800,39801,39802,39803],focused_carrier_union=39804,full_combined_closing_manifest='NOT RUN: host barrier stop'),op251=dict(per_cell='PV_B2_D_MaterializeTotal.cell/cells; all raw weights/powers, every j<1024',kernel='PV_B2_D_MaterializeTotal.source;39883; every raw weight/kappa/initial caller array returns complete ok(Ok(),updated)',mixed_product='PV_B2_D_MulQm31Total.source;39852; arbitrary raw mixed products pass from_limbs/unwrap',raw='PV_B2_D_RawTotal.source;39865; all seven kinds, every valid cell',powers='PV_B2_D_PowTotal.source;39860 and replayed C_PowersTotal/Powers7Total',allocation_original_transport='OPEN; no native allocation, original/copy/effect or V258 claim'),per_op={'249':'Prior batch2c complete source gamma rank/nonzero law retained; new sampler cohort replay blocked before compiler at39887; universal original/copy equality and V256 open','250':'Prior source ordinary law retained; universal original/copy equality and V257 open; native ordinary carrier draft uncompiled','251':'Unconditional copied kernel success now proved; original, caller allocation and native effects transport open; V258 open','252':'Constructor fixed boundaries/new_total/new_eq_staged replay39869 passes with qualified carriers; native Box/allocation and universal original equality open; V259 open','253':'Repaired D boundary/failure/invalid-continuation proofs replay39870-39873 passes; universal frozen value/error equality open; V260 open'},rows_closed=[],row_recount=dict(total_distinct_rows=6,newly_closed=0,open=['V256','V257','V258','V259','V260'],existing_candidate_credit=['V261/op254, batch1 shared powers; unchanged and counted once']),premises=dict(removed=[],added=[],weakened=[],transferred_to_T=[],retained=['V256','V257','V258','V259','V260','native allocation/OS failure association','L1/L2/L3 observations','all endpoint and deployment conditions']),trust_fields=['entropy_law','entropy_kernel','observation'],crates_programs_changed=False,elf_gate='No new gate required: Lean/generator changes only; reuse matching batch2c/ELF-GATE.json at unchanged Rust5b11c957a0',fixture_byte_gate='NOT RUN: ordered universal original/copy and ledger bridges unfinished; comparison base73070ddd51',final_combined_audit='NOT RUN: individual accepted theorem axioms all standard; sampler restoration blocked',focused_closure_replay='NOT RUN; audit IDs39897-39899 untouched',h4='All5673 manifest objects hashed before first compile; actual5673 resolutions also verified matching; no library rebuild/substitution',h5_h5_prime='PROJECT-CLOSURE.json;105 EJR sources match shared bytes,2 exact own-HEAD native types built privately, own PV sources; EJR/freeze precedence retained',h6='No other job private project object reused',rust_source_pins='TRANSPORT-PREFLIGHT.json; frozen sampler/weights/transport equal73070ddd51; no new Rust edits',d188='Unchanged Rust/copy bodies; reuse batch2c/D188-FULL-COMPARISON.json; no copy writes through a mutable iterator borrow',retained_counterexample='PV_B2_ErrorCounterexample unchanged from resume HEAD',handling_incident='COOLDOWN-INCIDENT.json:39823 submitted approximately12 seconds early; failed candidate retained; local cooldown timestamp guard added; fatal barrier classification corrected at stop',keys='KEY-RETENTION.json;21 keys retained at0600; no transactions, refunds or cleanup',cache='OUTPUT-OBJECT-PINS.json; private compiled cache retained for dependent recovery; shared sources/objects untouched',uncompiled_drafts='UNCOMPILED-DRAFTS.json plus audit drafts under drafts/',next_deliverable='Lead repairs the host barrier OSError19. Then resume uncharged-target sampler restoration with fresh39888, finish native/original/copy/allocation transports for249-253 and V256-V260, ordered fixture-byte gate, combined audit and focused closure. All22 remaining Lean attempts are unspent; only39888-39899 remain in the current authorized block.',git_log_since_resume=log.splitlines())
assert len(unused)==12 and report['remaining_lean_budget']==22
(E/'FINAL.json').write_text(json.dumps(report,indent=2)+'\n')
root=E.parent/'FINAL.json';backup=E.parent/'FINAL-before-batch2d-D326.json'
if not backup.exists():backup.write_bytes(root.read_bytes())
root.write_bytes((E/'FINAL.json').read_bytes())
print('STOP',report['lean_charged'],'charged;',len(accepted),'accepted modules;',len(checks),'generator checks; unused IDs',unused)
