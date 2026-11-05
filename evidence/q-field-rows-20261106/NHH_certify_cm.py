from pathlib import Path
import runpy,json,hashlib
E=Path(__file__).resolve().parent
runpy.run_path(str(E/'NHH_certify.py'))
J=lambda p:json.loads(Path(p).read_bytes())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
for n in ['NHH_AUDIT.json','NHH_CLOSED.json','NHH_EDGES.json','NHH_LEDGER_DELTA.json']:
 p=E/n;q=E/(p.stem+'_STAGE1.json')
 if not q.exists():q.write_bytes(p.read_bytes())

def pair(p,n,harness,payload):
 ps=J(E/(p+'.json'));ns=J(E/(n+'.json'))
 for a,c,negative in [(p,ps,False),(n,ns,True)]:
  r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));g=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'));s=(E/a/'stdout.log').read_text()
  assert ad['exit']==0 and ad['reservation']['allowed']is True
  assert r['exit_status']==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL')in s
  assert 'Timed out'not in s and g['graph_matches_frozen']and not g['edge_errors']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert c['env']['CARGO_NET_OFFLINE']=='true'
  assert c['module']=='NHH_fields::'+harness
  assert '-j'in c['native_command']and c['native_command'][c['native_command'].index('-j')+1]=='1'
  assert set(next(x['features'] for x in g['selected_closure']if x['name']=='aspis-r1-cost-probe'))>={'default','private-leaf-salts','optimized-terminal','program-build'}
  assert 'r0-op-count' not in next(x['features']for x in g['selected_closure']if x['name']=='aspis-core')
  stored=J(E/a/'sources/NHH_SOURCE_PINS.json')
  assert stored==J(E/payload),a
 flags=ns['env']['RUSTFLAGS'];assert flags.count(' --cfg NHH_invert')==1
 env=dict(ns['env']);env['RUSTFLAGS']=flags.replace(' --cfg NHH_invert','',1)
 assert env==ps['env']and ns['native_command']==ps['native_command']
 return dict(positive=p,negative=n,harness=harness,payload_pins=payload,source_matched=True,frozen_graph=True,deployed_features=True,unchanged_lock=True,matched_control='FAIL',quarantined=False,suspended=False)
np=[pair('NHH_K021','NHH_K022','cm_inverse_log','NHH_INVERSE_PINS.json'),pair('NHH_K023','NHH_K024','copy_control','NHH_INVERSE_PINS.json')]
put('NHH_CM_NATIVE_VALIDATION.json',dict(status='PASS',pairs=np,generic_function_pointer_credit=False))
review=E/'NHH_review_cm';s=J(review/'SUMMARY.json');roots=J(E/'NHH_L030/sources/NHH_AUDIT_ROOTS.json')['roots'];assert s['status']=='PASS'
rs=[x for c in s['commands']if c['target'].startswith('proof')for x in c['results']];fixtures=J(review/'fixtures.json')['results'];scan=J(review/'SCAN_SUMMARY.json')
assert len(rs)==len(roots)==78 and {x['root']for x in rs}==set(roots)
assert len(fixtures)==8 and all(x['equal']for x in fixtures)
assert all(x['equal']and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in rs)
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
put('NHH_AUDIT.json',dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',results=rs,fixtures=fixtures,scan=scan,receipt='NHH_L030/receipt.json',raw_authoritative=True,cold_release_replay=False,earlier_stages_retained=['NHH_AUDIT_STAGE1.json']))
c=J(E/'NHH_CLOSED.json');f=dict(function='crates/aspis-core/src/field.rs::CM31::inv',rows=['TX1:005'],status='CLOSED',form='ordinary (y) fixed direct backend specialization; generic callback credit excluded',domain='SAME canonical nonzero two-word receiver',native_positive='NHH_K021',matched_control='NHH_K022',copy_pair=['NHH_K023','NHH_K024'],model_root='NHH_CMBridge.packet',full_partial_result='NHH_CMAll.inverse_association',domain_proof='NHH_ScalarDomain.norm and NHH_CMTrace.backend_domain derive SAME nonzero canonical norm, every product/negative/backend reply canonical; no selected successful reply premise',specialized_child='NHH_CMBridge.specialized_packet',selected_backend='NHH_CMBridge.selected_backend',frame='full returned record, immutable input and five ordered opaque calls',trust='P6/D188 option A retained/reclassified; no new trust; no generic function-pointer credit')
c['functions'].append(f);c.update(new_composed_functions=6,new_composed_rows=10);put('NHH_CLOSED.json',c)
e=J(E/'NHH_EDGES.json');e['edges'].append(dict(caller=f['function'],callee='crates/aspis-core/src/field.rs::CM31::inv_with',status='CLOSED',scope='fixed M31::inv instance only; generic row remains OPEN',model_packet='NHH_CMBridge.specialized_packet',source_selection='NHH_CMBridge.selected_backend',native='NHH_K021',caller_domain='source literal inv_with(M31::inv); SAME canonical nonzero receiver',no_generic_function_pointer_credit=True));e['new_closed_edges']=len(e['edges']);put('NHH_EDGES.json',e)
d=J(E/'NHH_LEDGER_DELTA.json');d['new_closed_rows'].append('TX1:005');d['new_functions']=6;d['pending']=[r for r in d['pending']if r['row']!='TX1:005'];d['contextual_specializations']=[dict(row='TX1:005',callee_row='TX1:006',callee_packet='NHH_CMBridge.specialized_packet',generic_callee_status='OPEN',rationale='The frozen caller statically selects M31::inv; no arbitrary function-pointer semantic claim.')];put('NHH_LEDGER_DELTA.json',d)
print(json.dumps(dict(status='PASS',new_closed_rows=d['new_closed_rows'],audit_roots=len(rs),modules=scan['modules'])))
