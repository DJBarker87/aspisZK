"""Rule-B certificates from unchanged NEE steps and a stronger same-run join."""
from pathlib import Path
import json,hashlib,subprocess,copy
E=Path(__file__).resolve().parent;R=E.parent.parent;P=E.parent/'slice-s-compose2-20261029';D=E.parent/'slice-s-compose-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
ref=lambda p:dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def theorem(source,receipt,snapshot,name):
 s=source.read_text();short=name.rsplit('.',1)[-1];a=s.index('theorem '+short+' ');z=s.find('\ntheorem ',a+1)
 if z<0:z=s.index('\n#print',a)
 statement=s[a:z]
 return dict(name=name,source=ref(source),receipt=ref(receipt),snapshot_path=snapshot,statement=statement,statement_sha256=sha(statement.encode()))
value=theorem(E/'NEJ_ScannerFramed.lean',E/'NEJ_L012/receipt.json','NEJ_generated/NEJ_ScannerFramed.lean','NEJ_ScannerFramed.value_and_frame')
width=theorem(E/'NEJ_ScannerWidth.lean',E/'NEJ_L013/receipt.json','NEJ_generated/NEJ_ScannerWidth.lean','NEJ_ScannerWidth.width')
packet=json.loads((E/'NEJ_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEJ_REVIEWED_CERTIFICATES.json').read_text());base=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
for case,mod,stem,lo,hi in [('forest','pair_forest_accounts','account',41,42),('tree','pair_tree_profile','profile',43,44)]:
 f='crates/aspis-statement/src/pool_v1/'+mod+'.rs::digest_is_canonical'
 association=[theorem(D/'NED_ScannerCohorts.lean',D/'NED_L055/receipt.json','NED_generated/NED_ScannerCohorts.lean','NED_ScannerCohorts.'+stem+s) for s in ['_body','_result']]
 if case=='tree':association.append(theorem(P/'NEE_CanonicalFrame.lean',P/'NEE_L023/receipt.json','NEE_generated/NEE_CanonicalFrame.lean','NEE_CanonicalFrame.tree_body'))
 external_ids=sorted({o['id'] for row in base['rows'] if row['function']==f for o in row['caller_domain_obligations'] if 'callee' not in o})
 q=dict(external_ids=external_ids,external_length_theorem=width,method='rule B: one native step, Lean induction, emitted step association',shape='Bool',invariant='0<=i<=8; canonical iff suffix from i; same external state',trust_classification='P6/D188 option A reclassification',inner_hypotheses_remaining=[],native_external_modifies=[],case=case,function=f,frozen_body_sha256=json.loads((P/('NEE_'+case+'_LOOP_positive.json')).read_text())['native_body_sha256'],value_frame_theorem=value,emitted_association_theorems=association)
 for kind,n in [('positive',lo),('negative',hi)]:
  a=f'NEE_K{n:03}'
  q[kind]={key:ref(path) for key,path in dict(receipt=P/a/'receipt.json',stdout=P/a/'stdout.log',contract=P/(a+'-NEE_native_contracts.patch'),oracle=P/(a+'-NEE_oracle.patch'),graph=P/(a+'-graph-check.json'),lock=P/(a+'-lock-check.json'),config=P/(a+'.json'),source_check=P/(a+'-source-check.json'),features=P/(a+'-metadata-pin.json'),admission=P/(a+'-admission.json')).items()}
 ts=[value,width,*association];claims=sorted({x for r in base['rows'] if r['function']==f for x in r['selected_claims']})
 c=dict(id='NEJ_loop_'+case,kind='root-composition',subject=f,frozen_revision=base['frozen_revision'],theorems=ts,native_association=[q[k]['receipt'] for k in ['positive','negative']]+[q['positive']['contract'],q['negative']['contract']],same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation='Same typed raw32 eight-word carrier; exact frozen one-step body with local counter and only local ghost modifies; same-run Lean canonical result plus arbitrary external frame; rule B under P6/D188 option A. Initial invariant is i=0; no canonicality assumption.',callee_domain_established=True,canonical_carrier_established=True,hypotheses=['CompositionTrustOptionA'],loop_composition=q,call_domain_certificate=dict(subject=f,frozen_revision=base['frozen_revision'],native_association_kind='native-loop',domain_theorems=[association[1]],physical_theorems=[value,association[0]],selected_callee_claims=claims,inner_hypotheses_remaining=[],exact_callsite='frozen '+f+'; initial i=0; same arbitrary digest for every iteration',canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=[]))
 def put(group,subject,c):
  c=copy.deepcopy(c);c['subject']=subject;c['call_domain_certificate']['subject']=subject;c.pop('semantic_review_sha256',None)
  digest=sha(json.dumps(c,sort_keys=True).encode());c['semantic_review_sha256']=digest;review[subject]=digest;packet[group][subject]=c
 put('members',f,c)
 for subject in external_ids:
  x=copy.deepcopy(c);x['kind']='external-domain';x['id']+='_fixed_width'
  packet.setdefault('externals',{});put('externals',subject,x)
 names={h['name'] for r in base['rows'] if r['function']==f for h in r['named_hypotheses']}
 for name in names:
  h=copy.deepcopy(c);h['kind']='hypothesis-discharge';h['id']+='_'+name
  put('hypotheses',f+'::'+name,h)
(E/'NEJ_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n');(E/'NEJ_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
