"""Assemble review packets only after every final gate is present and green."""
from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent
def load(n):return json.loads((E/n).read_text())
def write(n,x):(E/n).write_text(json.dumps(x,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NKA_[LK][0-9][0-9][0-9]/receipt.json'))]
by={r['attempt']:r for r in receipts}
for a in ['NKA_L066','NKA_L067','NKA_L068','NKA_L069','NKA_L070','NKA_L071','NKA_L072','NKA_L073','NKA_L074','NKA_L075']:
 assert by[a]['exit_status']==0,a
scan=load('NKA_audit_final/scan/scan.json');assert scan['exit_status']==0 and scan['policy_pass']
groups=[load('NKA_audit_final/batch0/proof0.json'),load('NKA_audit_final/batch1/proof1.json')]
raw=sum([g['results'] for g in groups],[]);roots=sum(load('NKA_AUDIT_ROOTS.json')['groups'],[])
assert [r['root'] for r in raw]==roots and len(raw)==40
assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
loaded=[json.loads(l) for l in (E/'NKA_LOADED_scan.jsonl').read_text().splitlines()]
assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in loaded)
fixtures=load('NKA_audit/fixtures/fixtures.json');assert fixtures['policy_pass'] and len(fixtures['results'])==8
assert fixtures['binary_sha256']==groups[0]['binary_sha256']==groups[1]['binary_sha256']
host=load('NKA_FINAL_HOST_VALIDATION.json');assert host['status']=='PASS'
assert load('NKA_PATCH_VALIDATION.json')['status']=='PASS'
assert load('NKA_RETENTION.json')['status']=='PASS'
children=load('NKA_CHILD_ADMISSION.json');assert children['gate']=='PASS' and all(r['status']=='CLOSED' for r in children['children'])
baseline=load('NKA_BASELINE_ROWS.json')
basepath=E.parent/'ledger16-20261108/NJW_LEDGER.json.xz'
native=[['NKA_K004','NKA_K005'],['NKA_K018','NKA_K019'],['NKA_K020','NKA_K021','NKA_K022'],['NKA_K023','NKA_K024'],['NKA_K025','NKA_K026'],['NKA_K027','NKA_K028'],['NKA_K029','NKA_K030'],['NKA_K031','NKA_K032']]
for pair in native:
 for i,a in enumerate(pair):
  assert by[a]['exit_status']==(0 if i==0 else 1),(a,by[a]['exit_status'])
  text=(E/a/'stdout.log').read_text()
  assert ('VERIFICATION:- SUCCESSFUL' if i==0 else 'VERIFICATION:- FAILED') in text,a
  assert load(a+'-graph-check.json')['graph_matches_frozen']
  assert load(a+'-lock-check.json')['unchanged']
  assert by[a]['env']['CARGO_NET_OFFLINE']=='true'
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
headline='AspisR1.RPx_Deployed.deployed'
trust='Existing P6/D188 option-A native semantic transport RECLASSIFICATION; existing Allocator/Std/P7 and ReviewedTranscription-queries_from_pairs only within its existing scope; no addition/removal/widening'
gate=dict(combined='NKA_L066',coherence='NKA_L067',raw=['NKA_L068','NKA_L069'],fixtures='NKA_L047',statements='NKA_L070',retention=['NKA_L071','NKA_L072'])
functions=[]
for row,root,domain,pairs in [
 ('TX1:129','AspisR1.NKA_ClaimsRoot.claims','Actual private invocation from SAME parsed prefix; forall r:NP6_StdModel.Reservation with no success premise; exact same allocator.allocate state1392 action and complete returned state/abort; decoder domains derived internally; completed typed-store history Ready before same owned singleton Box is read',native[1:3]+native[4:]),
 ('TX1:069','AspisR1.NKA_OuterCut.queries_from_pairs','All original eight blocks and advances; derived QueryScan default; SAME066/067 inputs/state and all continuing domains internally derived; full Result, first stop, selected advance and unchanged pure frame',native[:1]+native[3:4])]:
  b=baseline[row]
  functions.append(dict(rows=[row],function=b['function'],frozen_body_sha256=b['frozen_body_sha256'],obligation_statement_hash=b['obligation_statement_hash'],route='direct hybrid native/Kani/Lean P6 (az)/(au)/(aq)(5)',root_domain=domain,native_pairs=pairs,lean_roots=[root],complete_carrier=True,premise_policy='Original source inputs and reviewed native cuts only; no child-output/success/endpoint/Run/free cohort Ops premise',trust=trust,caller_domain_certificate='NKA_ROW_OBLIGATIONS.json',dependency_credit=('PENDING next combined ledger gate; NJT066/067 already CLOSED in observed ledger17' if row.endswith('069') else 'PENDING next combined ledger gate')))
write('NKA_CLOSED.json',dict(frozen_revision=frozen,headline=headline,functions=functions,status='Two locally gated CLOSED candidates; authoritative ledger unchanged by this worker; NJT066/067 observed CLOSED in ledger17',unclosed=['TX1:136'],remaining_child='TX1:256 absent as a merged research candidate;136 support only',validation='NKA_AUDIT.json',gate=gate,security_target_established=False))
clauses={}
for row in ['TX1:069','TX1:129']:
 rows=[]
 for original in baseline[row]['obligation']['caller_domain_obligations']:
  c=original.get('callee','');i=original['id'];ref='NKA_CUTS.md; NKA_HYPOTHESIS_INVENTORY.md'
  if row=='TX1:069':
   if 'IncrementalMerkleTree' in c:resolution='RECLASSIFIED spurious-by-name under(az)(1); edge retained; actual derived QueryScan::default K023/K024, NJT_QDomains.initial'
   elif '::scan' in c:resolution='SAME block/state; NKA_QueryPairs.reached and NJT_QDomains.scan_preserved; consumes admitted067 from ledger17; own credit waits next gate'
   elif '::finish' in c:resolution='SAME selected final state; NJT_QPairs/NHB_OuterState.finishCurrent and admitted066 full Result from ledger17; own credit waits next gate'
   else:resolution='Source Ok constructor only; full native/model Result retained'
  elif '/field' in c:
   resolution='Conservative .add name alternative retained and resolved to typed raw-pointer Row::add(p), not a reached field operation; literal frozen site and NKA_Layout offset/bounds plus NJG data/window native packet; no field PacketDomain assumption imposed'
  elif 'validated_record' in c:resolution='Exact source record25 and SAME parsed prefix; NJT_QClaimsCanonical derives getter success and source identity internally'
  elif 'decode_k' in c:resolution='Exact source record25/29/offset29*p for all p<3; NJT_QClaimsCanonical + NJG argument/data/error packet; no decoder success premise at root'
  elif i.endswith(':6'):resolution='Actual reserve1/1392/align4 continuation K020/21/22 and full mapped reply K027/28; actual std rejection mapper K031/32; universal Reservation and SAME allocator action; existing Allocator source-site realization retained'
  elif i.endswith(':7'):resolution='Typed Row ptr::write K029/30 and full data/current/prior frame NJG/NJM; arbitrary p<3, Lean three-step data and write-history induction; error cleanup K018/19'
  elif i.endswith(':8') or i.endswith(':9'):resolution='Same owned allocation raw pointer and Row cast; exact1392/align4 and row offset bounds; K020/21/22, NJG/NJM windows; no pointer-implies-value inference'
  elif i.endswith(':11'):resolution='NKA_InitHistory Ready and all_words from completed actual stores; NKA_HeapCarrier source and same Storage BoxCut; retained NJM data/owner controls, singleton NJT carrier; no data-only initializedness premise'
  else:resolution='Source Ok constructor; preserves complete Result and allocator state'
  rows.append(dict(original=original,resolution=resolution,discharged_by=ref,status='LOCAL_CANDIDATE; requires ledger validation'))
 clauses[row]=dict(canonical_callees_retained=baseline[row]['canonical_callees'],clauses=rows,inventory_domain_obligations=baseline[row]['obligation']['inventory_domain_obligations'],named_hypotheses=baseline[row]['obligation']['named_hypotheses'],scope='Exact source forward instantiation; no incoming parent136 obligation discharged by this packet')
write('NKA_ROW_OBLIGATIONS.json',clauses)
write('NKA_LEDGER_DELTA.json',dict(baseline='evidence/ledger16-20261108/NJW_LEDGER.json.xz',baseline_sha256=sha(basepath),baseline_counts=dict(CLOSED=484,QUALIFIED=0,OPEN=115,total=599),updates=[dict(row=f['rows'][0],previous='OPEN',proposed='CLOSED',packet='NKA_CLOSED.json',lean_roots=f['lean_roots'],canonical_callees=baseline[f['rows'][0]]['canonical_callees'],original_obligation_statement_hash=f['obligation_statement_hash'],caller_domain_certificate='NKA_ROW_OBLIGATIONS.json',credit=f['dependency_credit']) for f in functions],authoritative_ledger_changed=False,credit='PENDING next ledger gate; do not compute after-counts without NJT child admission',untouched_open=['TX1:136','TX1:256'],security_target_established=False))
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits and str(r['swaps'])=='0',r['attempt']
 ad=load(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,r['attempt']
budget=dict(lean_support=sum(r['attempt'][4]=='L' for r in receipts),kani=sum(r['attempt'][4]=='K' for r in receipts),extractions=0,limits=dict(lean_support=100,kani=80,extractions=0),stop_reason='See member-by-member NKA_REMAINING.md; no remaining authorized independent obligation while256 absent and ledger admission external')
write('NKA_AUDIT.json',dict(status='PASS final local gate for069/129 candidates;136 support only',security_target_established=False,branch='codex/cx-claims2-20261107',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,frozen_revision=frozen,headline=headline,observed_child_admission=load('NKA_CHILD_ADMISSION.json'),gate=gate,candidate_rows=['TX1:129','TX1:069'],authoritative_ledger_changed=False,full_combined_import_attempts=['NKA_L043','NKA_L066'],phase1='Superseded129 initialization domain; retained uncredited native interpretation in NKA_PHASE1_* and NKA_INIT_DOMAIN_REVIEW.md',final_scan=dict(attempt='NKA_L067',exit_status=0,modules=len(loaded),declarations=sum(r['declarations'] for r in loaded),references=sum(r['edges'] for r in loaded),dangling=0,incompatible_declarations=0,import_mismatches=0),raw=dict(attempts=['NKA_L068','NKA_L069'],roots=len(raw),all_equal_collectAxioms=True,axioms=sorted(set(sum([r['walked_axioms'] for r in raw],[]))),headline=raw[0]),fixtures=dict(attempt='NKA_L047',cases=8,pass_=True,same_final_binary=True),new_modules=len(load('NKA_MODULES.json')),budget=budget,max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),all_swaps_zero=True,exact_limits=limits,all_admissions_allowed_and_exit0=True,excluded_native=['K008/K009 ineffective leak control','K010 no native Global OOM exhibited','K013 own missing-input compilation diagnostic'],isolated_lean=['L037 heartbeat200000; split Effects/Ownership/Root; no limit increase or unchanged repeat'],timeout_or_memory_killed=[],quarantined=[],suspended=[],trust_changes=dict(added=[],removed=[],widened=[],transport=trust),shipped_source_changed=False,elf_rebuilt=False,inherited_elf_pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),export=load('NKA_EXPORT.json'),host_validation='NKA_FINAL_HOST_VALIDATION.json',resources='NKA_ATTEMPTS.jsonl and per-attempt receipts include exact target/exit/wall/RSS/swap/revision/source+dependency pins/axioms; CARGO_TARGET_DIR recorded in every scope'))
print(json.dumps(dict(packet='NKA_CLOSED.json',candidate_rows=['TX1:129','TX1:069'],raw_roots=len(raw),budget=budget)))
