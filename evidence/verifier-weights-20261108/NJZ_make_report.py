"""Seal only validated row candidates; baseline ledger credit is unchanged."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent
load=lambda n:json.loads(E.joinpath(n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
attempts=[json.loads(l) for l in E.joinpath('NJZ_ATTEMPTS.jsonl').read_text().splitlines()]
by={r['attempt']:r for r in attempts}
for a in ['NJZ_L045','NJZ_L046','NJZ_L047','NJZ_L048']:assert by[a]['exit_status']==0,a
fixtures=load('NJZ_audit/fixtures/fixtures.json')['results'];assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert [r['walked_axioms'] for r in fixtures]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
assert load('NJZ_L036/NJZ_ProofDriver_BINARY_PIN.json')==load('NJZ_L046/NJZ_ProofDriver_BINARY_PIN.json')
raw=[]
for p in sorted(E.glob('NJZ_audit/all/proof*.json')):raw+=json.loads(p.read_text())['results']
expected=[n for g in load('NJZ_AUDIT_ROOTS.json')['groups'] for n in g];assert sorted(r['root'] for r in raw)==sorted(expected)
standard={'propext','Classical.choice','Quot.sound'}
for r in raw:assert r['equal'] and set(r['walked_axioms'])<=standard,(r['root'],r)
scan=[json.loads(l) for l in E.joinpath('NJZ_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
# The adopted cohort, rather than the older unretargeted helper family, is mandatory.
assert 'NFU_Retarget.verifier.echeck' in E.joinpath('NJZ_L045/stdout.log').read_text()
for n in ['NJZ_Echeck','NJZ_CodecProjection','NJZ_CodecSemantics']:
 assert not re.search(r'\bLPt_External\b|\bLPt_LPl\b',E.joinpath(n+'.lean').read_text())
selected=[(6,7),(8,9),(10,11),(14,15),(18,19),(20,21),(22,23),(26,25),(33,34),(35,36),(39,40),(41,42),(49,50),(57,58),(59,60),(61,62),(63,64),(65,66),(67,68),(69,70),(71,72),(73,74),(75,76)]
native=[]
for good,bad in selected:
 pair=[];sources=[]
 for n,positive in [(good,True),(bad,False)]:
  a=f'NJZ_K{n:03d}';r=load(a+'/receipt.json');out=E.joinpath(a+'/stdout.log').read_text();g=load(a+'-graph-check.json');lock=load(a+'-lock-check.json');ad=load(a+'-admission.json')
  assert (r['exit_status']==0)==positive and ('VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED')) in out,a
  assert 'timed out' not in out and 'error[' not in out,a
  assert g['graph_matches_frozen'] and lock['unchanged'] and ad['exit']==0 and ad['reservation']['allowed'] is True,a
  assert lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR'].endswith('/NJZ_target')
  sources.append(r['source_hashes']);pair.append(dict(attempt=a,positive=positive,receipt=a+'/receipt.json',sha256=sha(E/a/'receipt.json'),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_hashes=r['source_hashes']))
 assert sources[0]==sources[1],('unmatched source configuration',good,bad)
 native.append(pair)
E.joinpath('NJZ_NATIVE_PAIRS.json').write_text(json.dumps(native,indent=2)+'\n')
base=json.loads(lzma.open(E.parent/'ledger16-20261108/NJW_LEDGER.json.xz').read());rows=load('NJZ_BASELINE_ROWS.json');assert len(rows)==15 and all(r['status']=='OPEN' for r in rows)
info={
'TX1:176':(['NJZ_Weights.new_source'],[['NJJ_K017','NJJ_K018'],['NJR_K039','NJR_K040'],['NJJ_K070','NJJ_K071']],'SAME64weights; actual source-site Reservation, both arms; complete raw64/terms0/ownership frame','(y)/(ai)/(aq)(5)'),
'TX1:189':(['NJZ_CodecSemantics.root','NJZ_CodecSemantics.source','NJZ_CodecSemantics.domain'],[['NJZ_K035','NJZ_K036'],['NJJ_K007','NJJ_K008']],'All byte slices/k Bool, complete32byte chunks and ignored suffix; canonical child reply derived, first rejection/no suffix','(ah)/(B)/(au)/(aq)(5)'),
'TX1:201':(['NJZ_TreeParent.source'],[['NJZ_K033','NJZ_K034']],'SAME canonical left/right M31[8]; CLOSED TX1:305 complete reply and readonly frame','(ah)/(aq)(5)'),
'TX1:202':(['NJZ_PoolRoot.default'],[['NJZ_K041','NJZ_K042'],['NJZ_K018','NJZ_K019']],'No external inputs; complete child table/empty and all returned fields; no child-success premise','(ah)/(aq)(5)'),
'TX1:203':(['NJZ_PoolRoot.empty'],[['NJZ_K039','NJZ_K040'],['NJZ_K014','NJZ_K015']],'No external inputs; SAME20level roots table; next0/root20/frontier0..19; complete record','(ah)/(aq)(5)'),
'TX1:204':(['NJZ_PoolRoot.roots','NJZ_PoolRoot.domains','NJZ_PoolRoot.parent_clauses'],[['NJZ_K010','NJZ_K011'],['NJZ_K049','NJZ_K050'],['NJZ_K075','NJZ_K076']],'Literal zero21table;20source-ordered steps, every entered child canonical domain internally derived, full untouched frame','(ah)/(B)/(ad)/(aq)(5)'),
'TX2:099':(['NJZ_Weights.finish_source'],[['NJR_K037','NJR_K038'],['NJR_K049','NJR_K050']],'SAME raw64/weights64; arbitrary U64 limbs; initial frame plus per-step cuts derive every size/value/frame','(y)/(B)/(ai)/(aq)(5)'),
'TX2:100':None,
'TX2:102':(['NJZ_Weights.value_source','NJJ_Value.projection'],[['NJJ_K026','NJJ_K027']],'Every U64 row, actual index<raw.length; full four-limb value and readonly receiver, no canonical raw precondition','(y)/(aq)(5)'),
'TX2:105':(['NJZ_Readers.e_reference','NJZ_Readers.e_source','NJZ_Readers.e_window'],[['NJJ_K036','NJJ_K037'],['NJZ_K026','NJZ_K025']],'Actual checkpoint-backed bounded32byte read; full eight-limb/error reply, advanced cursor and immutable backing; model all-prestate law is stronger than native domain','(y)/(au)/(aq)(5)'),
'TX2:106':(['NJZ_Readers.k_reference','NJZ_Readers.k_source','NJZ_Readers.k_window'],[['NJJ_K034','NJJ_K035'],['NJZ_K022','NJZ_K023']],'Actual checkpoint-backed bounded16byte read; full four-limb/error reply, advanced cursor and immutable backing','(y)/(au)/(aq)(5)'),
'TX2:107':(['NJZ_Readers.raw','NJZ_Readers.raw_cut'],[['NJZ_K020','NJZ_K021'],['NJZ_K022','NJZ_K023'],['NJZ_K026','NJZ_K025']],'ONLY native N4/16/32 on1768byte backing at arbitrary valid offset; every byte/cursor/backing frame. Generic kernel raw law is not broader native credit','(y)/(au)/(aq)(5)'),
'TX2:121':(['NJZ_CheckpointReaders.semantic','NJZ_CheckpointReaders.scalar'],[['NJC_K027','NJC_K028'],['NJJ_K048','NJJ_K049']],'Actual1768checkpoint/408cursor, ten SAME evolving Reader calls; complete array10 and first error/abort prefix','(y)/(au)/(aq)(5)'),
'TX2:122':(['NJZ_CheckpointReaders.weights','NJZ_CheckpointReaders.scalar','NJR_WeightFailure.weights'],[['NJR_K007','NJR_K008'],['NJJ_K011','NJJ_K012']],'Actual1768checkpoint/712cursor and SAME owned weights64; complete Result/cursor/Vec frame and owned error/drop prefix','(y)/(B)/(au)/(aq)(5)'),
'TX2:126':(['NJZ_Validator.source','NJZ_Validator.members','NJZ_Validator.unique'],[['NJC_K033','NJC_K034'],['NJC_K036','NJC_K037']],'Every array22 U32, every range/duplicate rejection, full Result and readonly/empty-effects frame; no validity premise','(y)/(B)/(au)/(aq)(5)')}
info['TX2:100']=info['TX1:176']
functions=[];seen=set()
for r in rows:
 key=r['row'];roots,pairs,domain,route=info[key]
 if r['function'] in seen:continue
 seen.add(r['function']);ids=[x['row'] for x in rows if x['function']==r['function']]
 functions.append(dict(rows=ids,function=r['function'],route=route,root_domain=domain,native_pairs=pairs,lean_roots=roots,complete_carrier=True,premise_policy='Only ordinary inputs/derived caller domains, reviewed native cut transcriptions and SAME-source-site Reservation data; no arbitrary Ops/Run/endpoint/child-success/NoBad/history premise',trust='P6/D188 option A RECLASSIFICATION; existing Std/allocator/runtime trust retained; none added/removed',frozen_body_sha256=r['frozen_body_sha256'],callee_functions=r['canonical_callees']))
packet=dict(frozen_revision=base['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',status='READY_FOR_NEXT_LEDGER_REVIEW',security_target_established=False,local_gate='PASS',ledger_credit='PENDING next authoritative ledger gate; NJW baseline unchanged',functions=functions,selected_calibrations=dict(PD_ParentLog=list(range(57,63)),PoolTree=list(range(63,69)),ResultUnitError=list(range(69,75))))

for item in functions:
 if item['route'].startswith('(ah)'):item['reviewed_transcription']=dict(classification='P6/D188 option-A RECLASSIFICATION; existing item scope extended, no runtime/cryptographic trust added or removed',scope=item['function'],evidence='NJZ_AH_TRANSCRIPTION.md',native_source='NJZ_NATIVE_INPUTS.json / NJZ_native.patch',lean_roots=item['lean_roots'])
 if 'TX2:126' in item['rows']:item['model_transport_roots']=['NJC_ValidateCalls.clause','NJC_ValidateCalls.source']
 if any(r in item['rows'] for r in ['TX2:105','TX2:106']):item['model_transport_roots']=['NIL_FreshOps.k_port','NIL_FreshOps.e_port']
E.joinpath('NJZ_CLOSED.json').write_text(json.dumps(packet,indent=2)+'\n')
delta=dict(baseline='evidence/ledger16-20261108/NJW_LEDGER.json.xz',baseline_sha256=sha(E.parent/'ledger16-20261108/NJW_LEDGER.json.xz'),baseline_counts=base['counts'],admitted_changes=[],authoritative_counts_unchanged=True,proposals=[dict(row=r['row'],from_status='OPEN',to_status_requested='CLOSED',packet='NJZ_CLOSED.json',baseline_obligation=r['obligation'],baseline_obligation_statement_hash=r['obligation_statement_hash']) for r in rows],pending_gate=True,security_target_established=False)
E.joinpath('NJZ_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
scopes={k:sum(r['kind']==k for r in attempts) for k in sorted({r['kind'] for r in attempts})}
audit=dict(gate='PASS',combined_audit_count=2,final_import='NJZ_L045',raw_ax2='NJZ_L046',scan='NJZ_L047',fixture='NJZ_L036',fixtures_reused_same_binary=True,fixture_results=fixtures,raw_results=raw,raw_roots=len(raw),standard_axioms_only=True,scan_summary=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,duplicate_owners=0,import_mismatches=0,compatible_cache_replicas=sum(len(r['cached_replicas']) for r in scan)),all_scope_counts=scopes,scope_wall_seconds=sum(r['wall_seconds'] for r in attempts),maximum_peak_rss_kib=max(int(r['peak_rss_kib']) for r in attempts),swaps=sum(int(r['swaps']) for r in attempts),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exact_receipts='NJZ_ATTEMPTS.jsonl plus per-attempt receipt.json',first_audit_retained='NJZ_FIRST_AUDIT.json.xz',walker=load('NJZ_WALKER_PIN.json'),budget=dict(Kani_limit=90,Lean_support_limit=100,extraction_limit=1,Kani_slots_consumed=75,Kani_scopes=74,Kani_prelaunch_failure="NJZ_K001",skipped_Kani_id="NJZ_K038",Lean_support_slots_consumed=max(int(r['attempt'][-3:]) for r in attempts if r['attempt'].startswith('NJZ_L')),extraction_slots_consumed=1),target_not_established=True)
E.joinpath('NJZ_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
assert len(functions)==14 and sum(len(r['rows']) for r in functions)==15
print(f'Report validation PASS: 15 row candidates /14 functions; {len(raw)} standard-only roots; NFX exit0; baseline credit unchanged.')
