from pathlib import Path
import json,runpy,hashlib,lzma,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
ctx=runpy.run_path(str(E/'NHH_certify_cm.py'))
J=lambda p:json.loads(Path(p).read_bytes())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
for n in ['NHH_AUDIT.json','NHH_CLOSED.json','NHH_EDGES.json','NHH_LEDGER_DELTA.json']:
 p=E/n;q=E/(p.stem+'_CM.json')
 if not q.exists():q.write_bytes(p.read_bytes())
pairs=[]
configs=[(45,46,'m31_embed','NHH_SOURCE_PINS.json','invert'),(47,48,'cm31_embed','NHH_SOURCE_PINS.json','invert'),(49,50,'qm31_embed','NHH_SOURCE_PINS.json','invert'),(51,52,'wide_embed','NHH_SOURCE_PINS.json','invert'),(53,54,'cm_inherent','NHH_SOURCE_PINS.json','invert'),(55,56,'qm_neg','NHH_SOURCE_PINS.json','invert'),(57,58,'copy_control','NHH_SOURCE_PINS.json','invert'),(59,60,'cm_inverse_log','NHH_ARG_CM_PINS.json','bad_argument'),(61,62,'qm_try_log','NHH_ARG_Q_PINS.json','bad_argument'),(63,64,'qm_inv_log','NHH_ARG_Q_PINS.json','bad_argument'),(65,66,'copy_control','NHH_ARG_CM_PINS.json','invert'),(67,68,'copy_control','NHH_ARG_Q_PINS.json','invert'),(69,70,'qm_zero_none','NHH_ARG_Q_PINS.json','invert'),(71,72,'qm_zero_panic','NHH_ARG_Q_PINS.json','invert'),(73,74,'cm_zero_panic','NHH_CM_ZERO_PINS.json','invert'),(75,76,'cm_zero_prefix','NHH_CM_ZERO_PINS.json','invert'),(77,78,'copy_control','NHH_CM_ZERO_PINS.json','invert')]
for p,n,harness,payload,flag in configs:
 pp=f'NHH_K{p:03}';nn=f'NHH_K{n:03}';pc=J(E/(pp+'.json'));nc=J(E/(nn+'.json'))
 for a,c,neg in [(pp,pc,False),(nn,nc,True)]:
  rc=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));g=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'));sc=J(E/(a+'-source-check.json'));text=(E/a/'stdout.log').read_text()
  assert rc['exit_status']==(1 if neg else 0)and('VERIFICATION:- FAILED'if neg else'VERIFICATION:- SUCCESSFUL')in text
  assert 'Timed out'not in text and str(rc['swaps'])=='0'
  assert ad['exit']==0 and ad['reservation']['allowed']is True
  assert g['graph_matches_frozen']and not g['edge_errors']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert sc['frozen_files']==735 and not sc['errors']and sc['frozen_pins_sha256']==hashlib.sha256((E/'NHH_FROZEN_RELEASE_PINS.json').read_bytes()).hexdigest()
  assert J(E/a/'sources/NHH_SOURCE_PINS.json')==J(E/payload)
  assert c['module']=='NHH_fields::'+harness and c['env']['CARGO_NET_OFFLINE']=='true'
  core=next(x['features']for x in g['selected_closure']if x['name']=='aspis-core');assert core==['r0']
  probe=next(x['features']for x in g['selected_closure']if x['name']=='aspis-r1-cost-probe');assert probe==['default','optimized-terminal','private-leaf-salts','program-build']
 token=' --cfg NHH_'+flag;assert nc['env']['RUSTFLAGS'].count(token)==1
 ne=dict(nc['env']);ne['RUSTFLAGS']=ne['RUSTFLAGS'].replace(token,'',1);assert ne==pc['env']and nc['native_command']==pc['native_command']
 pairs.append(dict(positive=pp,negative=nn,harness=harness,payload_pins=payload,control='canonical recorded argument corruption'if flag=='bad_argument'else'expected-panic suppression'if harness.endswith('zero_panic')else'assertion inversion',frozen_files=735,source_matched=True,frozen_graph=True,unchanged_lock=True,deployed_features=True,credit='LOCAL ONLY: endpoint unresolved'if harness=='qm_neg'else'packet support',quarantined=False,suspended=False))
put('NHH_NATIVE_VALIDATION.json',dict(status='PASS',pairs=pairs,all_final_native_ids=list(range(45,79)),no_field_multiplication_verified=True,writable_static=False,generic_function_pointer_credit=False,contract_or_stub_verified_uses=0,source_preflight_strengthened=True,earlier_receipts_retained_not_promoted=True))
summary=J(E/'NHH_review_outcomes/SUMMARY.json');rs=[x for c in summary['commands']if c['target'].startswith('proof')for x in c['results']];fixtures=J(E/'NHH_review_outcomes/fixtures.json')['results'];scan=J(E/'NHH_review_outcomes/SCAN_SUMMARY.json');roots=J(E/'NHH_L049/sources/NHH_AUDIT_ROOTS.json')['roots']
assert summary['status']=='PASS'and len(rs)==len(roots)==113 and {x['root']for x in rs}==set(roots)
assert all(x['equal']and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in rs)
assert len(fixtures)==8 and all(x['equal']for x in fixtures)
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
put('NHH_AUDIT.json',dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',results=rs,fixtures=fixtures,scan=scan,receipt='NHH_L049/receipt.json',raw_authoritative=True,cold_release_replay=False,earlier_stages_retained=['NHH_AUDIT_STAGE1.json','NHH_AUDIT_CM.json','NHH_AUDIT_Q.json'],walker=J(E/'NHH_WALKER_PIN.json'),driver_diff='NHH_DRIVER_q.diff'))
c=J(E/'NHH_CLOSED.json')
for f in c['functions']:
 if f['function'].endswith('::CM31::inv'):f.update(native_positive='NHH_K059',matched_control='NHH_K060',copy_pair=['NHH_K065','NHH_K066'],control='recorded argument corruption',full_frozen_source_files=735,domain='SAME canonical two-word receiver; exact zero assertionFailure and nonzero returned record',outcome_root='NHH_InverseOutcomes.complex',zero_pair=['NHH_K073','NHH_K074'],zero_prefix_pair=['NHH_K075','NHH_K076'],zero_copy_pair=['NHH_K077','NHH_K078'])
 else:
  old=int(f['native_positive'][-3:]);pos={7:45,9:47,11:49,13:51,15:53}[old];f.update(native_positive=f'NHH_K{pos:03}',matched_control=f'NHH_K{pos+1:03}',copy_pair=['NHH_K057','NHH_K058'],full_frozen_source_files=735)
qtry=dict(function='crates/aspis-core/src/field.rs::QM31::try_inv',rows=['TX1:034'],status='CLOSED',form='ordinary (y) full zero/nonzero local-record caller and exact emitted/cohort partial Result',domain='SAME canonical four-word receiver, including zero',native_positive='NHH_K061',matched_control='NHH_K062',zero_pair=['NHH_K069','NHH_K070'],copy_pair=['NHH_K067','NHH_K068'],model_root='NHH_QBridge.try_packet',full_partial_result='NHH_QAll.try_association',trace='NHH_QTrace.source/encoded/zero',stub_domains='NHH_StubDomains.qm_log',callee_packets='retained CLOSED CM31 square/mul/neg/sub/by_r and new fixed CM31 inverse; actual source is CM31, not conservative QM31 alternatives',frame='full Option record and ordered five-call log; zero None has empty log',control='recorded argument corruption',full_frozen_source_files=735,trust='P6/D188 option A retained/reclassified; no new trust')
qinv=dict(function='crates/aspis-core/src/field.rs::QM31::inv',rows=['TX1:027'],status='CLOSED',form='ordinary (y) SAME child Option and native expect wrapper, exact zero panic separately',domain='SAME canonical four-word receiver; exact zero panic and nonzero returned record',native_positive='NHH_K063',matched_control='NHH_K064',panic_pair=['NHH_K071','NHH_K072'],copy_pair=['NHH_K067','NHH_K068'],model_root='NHH_QBridge.inverse_packet',full_partial_result='NHH_QAll.inverse_association',zero_result='NHH_QInverse.inverse_zero',outcome_root='NHH_InverseOutcomes.quadratic',domain_proof='NHH_QBridge.decode_live derives nonzero field value from SAME canonical raw limbs; try_nonzero derives SAME Some reply and canonical output',frame='immutable input, SAME recorded child receiver/reply, actual expect consumes it unchanged',control='recorded argument corruption',full_frozen_source_files=735,trust='P6/D188 option A retained/reclassified; no new trust')
c['functions'] += [qtry,qinv];c.update(new_composed_functions=8,new_composed_rows=12,generic_inv_with_status='OPEN',qm31_neg_status='OPEN');put('NHH_CLOSED.json',c)
ed=J(E/'NHH_EDGES.json')
# Repoint earlier certificates to final full-source support without changing any baseline edge.
for e in ed['edges']:
 if e.get('native')=='NHH_K021':e['native']='NHH_K059'
 else:
  old=int(e.get('native','NHH_K000')[-3:]);m={7:45,9:47,11:49,13:51,15:53}
  if old in m:e['native']=f'NHH_K{m[old]:03}'
ed['edges'] += [dict(caller=qinv['function'],callee=qtry['function'],status='CLOSED',argument_domain='SAME canonical nonzero original receiver',proof='NHH_QBridge.inverse_packet',native='NHH_K063'),dict(caller=qtry['function'],callee='crates/aspis-core/src/field.rs::QM31::is_zero',status='CLOSED',argument_domain='SAME original canonical receiver, zero included',proof='NHH_QInverse.test_association/zero_test',native='NHH_K061'),dict(caller=qtry['function'],callee='crates/aspis-core/src/field.rs::mul_by_r',status='CLOSED',argument_domain='SAME canonical second square reply',proof='NHH_CMAlgebra.rotate/NHH_QTrace.encoded',native='NHH_K061')]
for alternative,actual in [('inv','inv'),('mul','mul'),('neg','neg'),('square','square'),('sub','sub')]:
 ed['edges'].append(dict(caller=qtry['function'],callee='crates/aspis-core/src/field.rs::QM31::'+alternative,status='EXCLUDED-TYPED-ALTERNATIVE',actual_source_callee='crates/aspis-core/src/field.rs::CM31::'+actual,proof='NHH_QAll.try_association',native='NHH_K061',frozen_erasure='NHH_QINVERSE_ERASURE.json',inventory_unchanged=True))
ed['new_closed_edges']=sum(e['status']=='CLOSED'for e in ed['edges']);ed['typed_alternatives_excluded']=5;put('NHH_EDGES.json',ed)
d=J(E/'NHH_LEDGER_DELTA.json');d['new_closed_rows']+=['TX1:034','TX1:027'];d['new_functions']=8;d['pending']=[r for r in d['pending']if r['row']not in ['TX1:034','TX1:027']];d['final_native_validation']='NHH_NATIVE_VALIDATION.json';d['audit']='NHH_AUDIT.json';d['global_after_additive_delta']={'total':599,'CLOSED':315,'OPEN':284,'QUALIFIED':0};d['Q_after_additive_delta']={'total':161,'CLOSED':159,'OPEN':2,'QUALIFIED':0};d['no_authoritative_graph_or_membership_edit']=True;put('NHH_LEDGER_DELTA.json',d)
assert {r['row']for r in d['pending']}=={'TX1:006','TX1:031'}and len(d['new_closed_rows'])==12
# All target-body identities are byte-exact against the frozen git objects.
body_pins=[]
for r in J(E/'NHH_TARGETS.json')['rows']:
 raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+r['source_file']],cwd=R);a,b=r['frozen_body_byte_range'];h=hashlib.sha256(raw[a:b]).hexdigest();assert h==r['frozen_body_sha256'];body_pins.append(dict(row=r['row'],function=r['function'],source_file=r['source_file'],source_sha256=hashlib.sha256(raw).hexdigest(),body_sha256=h,byte_range=[a,b]))
put('NHH_SOURCE_VALIDATION.json',dict(status='PASS',targets=body_pins,patches=J(E/'NHH_PATCHES.json'),field_arithmetic_source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',shipped_changes=[]))
print(json.dumps(dict(status='PASS',closed_rows=12,Q_closed=159,Q_open=2,raw_roots=len(rs),scan_modules=scan['modules'],native_pairs=len(pairs))))
