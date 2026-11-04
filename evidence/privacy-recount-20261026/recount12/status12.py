from audit12 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
# All requested changed source cones, consumers and ruling expressions at pins.
patterns=['V183|PV_FXM_ReserveSelected|allocation denial','P_pthread_create_transfer|P_pthread_join_quiescence|P_scope_atomic_lifetime|P_thread_prefix_frame','ActualEntropyEntryPrefix','RuntimeReturnData']
scans=[]
for k in revs:
 for pat in patterns:
  z=__import__('subprocess').run(['git','grep','-n','-E',pat,revs[k],'--','lean','docs/research/v8-r0-zk-20261009/lean','evidence/pv-b3p6-20261028/lean','design/PRIVACY-LEDGER-20261026.md'],capture_output=True,text=True)
  scans.append({'ref':k,'revision':revs[k],'pattern':pat,'exit':z.returncode,'matches':z.stdout.splitlines()})
(P/'consumer-scans12.json').write_text(json.dumps(scans,indent=1)+'\n')
# Provider reports and exact statements/receipts, never their cached objects.
paths={
'b3p6':['evidence/pv-b3p6-20261028/lean/PV_B3P_OriginalSelection29177_29182_29187.lean','evidence/pv-b3p6-20261028/lean/PV_B3P_CombinedShapes630227.lean','evidence/pv-b3p6-20261028/resume18/verification-summary-D628.json','evidence/pv-b3p6-20261028/resume18/verification-summary-D630.json','evidence/pv-b3p6-20261028/resume18/REPORT-D630.md'],
'evhB':['evidence/pv-evhB-20261103/BLOCKER-D624.md','evidence/pv-evhB-20261103/OWNER-D597.md','lean/PV_EVHB_AdoptedAbort.lean','lean/PV_EVHB_OWNER.lean'],
'evhc':['evidence/pv-evhc10-20261104/'+q for q in ['REPORT.md','AUTHORIZATION.json','RECEIPT-VALIDATION.json','admission-92080-0.json','admission-status-0.json','lean-92080/receipt.json','agg-92080/RAW-AXIOMS.json','agg-92080/SCAN.json','agg-92080/SEQUENCE.json','agg-92080/step-1.json','agg-92080/step-2.json','agg-92080/step-3.json','agg-92080/PV_BR_FixtureConsumer.lean']]}
for k,ps in paths.items():
 for p in ps:read(k,p)
# Every row citing V183 is identified against both machine row data and pinned
# source closures, including transitive native consumers named by OWNER.
rows=json.loads((B/'recount11/rows11.json').read_text());census=[]
for r in rows:
 s=json.dumps(r)
 if 'V183' in s or 'ReserveSelected' in s:
  census.append({'row':r['id'],'before':r['recount11_status'],'disposition':'Source theorem retaining Result/failure/divergence only; generic denial is not native allocator null. No returned-native-denial credit survives.'})
for id in ['V165','V167','V178','V181','V228','V241','V244','V245','V258','V263','V370','V396','V400','V403']:
 if not any(z['row']==id for z in census):census.append({'row':id,'before':next(r['recount11_status'] for r in rows if r['id']==id),'disposition':'Native/RunJoin/source-world consumer rechecked: actual null -> abort terminal/divergence; no returned denial or witness-independence discharged. Existing OPEN/REDUCED/trust qualification remains.'})
(P/'v183-consumers12.json').write_text(json.dumps(census,indent=1)+'\n')
result={'D602':{'verdict':'CONFIRM qualification','source':'tools/r1-cost-probe/src/bin/devnet_spend/diagnostics.rs','adopted_source_ref':'uc','model_theorem':'R1Z.PV_FXM_ReserveSelected.complete','before':'generic returning allocation-denial law, native association uninstalled','after':'generic returning-model law retained; adopted null is abort/divergence; actual world and timing/witness-independence open','row_closure_change':False},
'D630':{'verdict':'ONE conditional hybrid package, not row closure','theorem':'PV_B3P_OriginalSelection29177_29182_29187.first_package','hypotheses':['NativePendingSelection623','NativeFaultSelection623','NativeEffectsSelection623','ResourceTimingIndependenceSelection623'],'OWNER':'PV_EVHB_OWNER.OWNER','audit':92894,'raw_roots':183,'whole_op227':'OPEN'},
'D636':{'verdict':'THREE conditional local caller packages, not row closures','theorems':['PV_B3P_CombinedLift630227.package','PV_B3P_CombinedComponent630227.package','PV_B3P_CombinedArithmetic630227.package'],'hypotheses':{s:['NativePending'+s+'630','NativeFault'+s+'630','NativeEffects'+s+'630','ResourceTimingIndependence'+s+'630'] for s in ['Lift','Component','Arithmetic']},'sites':10,'remaining_callers':217,'remaining_sites':1494,'audit':92895,'raw_roots':220,'DeployedWrapper557':'OPEN'},
'D624_D625':{'verdict':'OPEN P obligations, pending owner; not discharged or T','contracts':['P_pthread_create_transfer','P_pthread_join_quiescence','P_scope_atomic_lifetime','P_thread_prefix_frame'],'T':['entropy_law','entropy_kernel','observation'],'ordered_families_spawn_prefix_linear':'OPEN'},
'D589_l3_2':{'verdict':'Source projections stay independent of physical FRAME','projections':['native events','fileTrace','countTrace','timeTrace','oraclePrefix'],'residual':'ActualEntropyEntryPrefix source-to-machine pairing (V370/L3), named/unproved; not a counted row or premise consumed by any row','source_entry_world':'Defined over source Machine.run, including pending-resume. Actual installation and five RuntimeBinding equations remain OPEN.'},
'D597':{'verdict':'CONFIRM scoped coherent composition; not whole deployed non-vacuity','audit':92080,'steps':3,'roots':32,'modules':16539,'hypotheses_retained':['FixturePdaRuntime base','event acquisition','joint simulation'],'resources':'Provider authorized agg16: MemoryHigh14G/Max16G/swap0; does not authorize new recount run','whole_wall_seconds':160.604783654,'peak_rss_kib':12424428,'swap':0,'revision':'74ac46dbcac0643157cf9c90b1fcb212212513cb'},
'k3scan3':{'C051':'RESTORED','C053':'RESTORED','C163':'RESTORED','C164':'RESTORED','C156':'SUSPENDED; missing full-raw mul child/frame/G bridge'},'endpoint_premises_removed_added_weakened':[0,0,0]}
# Retain resource/axiom results verbatim and verify raw audit obligations in
# provider JSON, not merely a LOG claim.
for suffix in ['D628','D630']:
 q='evidence/pv-b3p6-20261028/resume18/verification-summary-'+suffix+'.json'
 result[suffix+'_receipt']=json.loads(txt('b3p6',q))
result['D597_receipt_validation']=json.loads(txt('evhc','evidence/pv-evhc10-20261104/RECEIPT-VALIDATION.json'))
result['D597_raw_roots']=json.loads(txt('evhc','evidence/pv-evhc10-20261104/agg-92080/RAW-AXIOMS.json'))
(P/'status-audit12.json').write_text(json.dumps(result,indent=1)+'\n');save();print('status audit retained')
