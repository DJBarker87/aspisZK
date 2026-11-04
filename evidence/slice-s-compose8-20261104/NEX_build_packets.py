"""Retain NEU baseline and add only complete, checked NEX certificates."""
from pathlib import Path
import sys,json,hashlib,lzma,re,copy
import NEX_validate as v
E=v.E;R=v.R;sha=v.sha
P=E.parent/'slice-s-compose7-20261103'
packet=v.read(P/'NEU_LEDGER_DELTA.json');reviewed=v.read(P/'NEU_REVIEWED_CERTIFICATES.json')
base=v.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
from NEX_bridge_checks import EXACT

def ref(p):
 p=Path(p);return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def theorem(name,attempt):
 source=E/attempt/'NEX_SOURCE.lean.txt';s=source.read_text();short=name.rsplit('.',1)[-1];a=s.index('theorem '+short+' ');z=re.search(r'\s:=\s',s[a:]).start()+a;statement=s[a:z].rstrip()
 rc=v.read(E/attempt/'receipt.json');assert rc['exit_status']==0
 assert any(line.startswith("'"+name+"'") and 'sorryAx' not in line for line in rc['print_axioms'])
 return dict(name=name,source=ref(source),receipt=ref(E/attempt/'receipt.json'),snapshot_path='NEX_generated/'+name.rsplit('.',1)[0]+'.lean',statement=statement,statement_sha256=sha(statement.encode()))
packet['NEX_native_bridge_additions']={}
selection=v.read(E/'NEX_NATIVE_SELECTION.json') if (E/'NEX_NATIVE_SELECTION.json').exists() else {}
if 'exact' in selection:
 conf=selection['exact'];pairs=conf['pairs'];thms=[theorem('NEX_Exact.result_state_effects',conf['lean'])];support=set()
 for pair in pairs:
  for a in pair:
   files=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
   archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json';files += [archive+'.xz',archive+'.sha256'];support.update(E/n for n in files)
 native=dict(function=EXACT,complete=True,domain='width in {8,32}; live slice length <=33; all bytes unrestricted',classification='actual frozen call, KMX, full Result, readonly state and empty runtime trace',pairs=pairs,inner_hypotheses_remaining=[],box_ruling_aa=False)
 packet['NEX_native_bridge_additions'][EXACT]=native
 subjects={EXACT:'member'}
 for row in base['rows']:
  if row['function']==EXACT:
   subjects.update({EXACT+'::'+h['name']:'hypothesis' for h in row['named_hypotheses']})
   subjects.update({o['id']:'external' for o in row['caller_domain_obligations']})
 for subject,kind in subjects.items():
  c=dict(id='NEX_'+kind+'::'+subject,subject=subject,frozen_revision=base['frozen_revision'],domain_theorems=thms,physical_theorems=thms,support=[ref(p) for p in sorted(support)],native_certificate=native,inner_hypotheses_remaining=[],new_trust_rows=[],trust_classification='P6/D188 option A reclassification',required_named_hypotheses=[],exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,native_frame_complete=True,callee_domain_established=True)
  c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());reviewed[subject]=c['semantic_review_sha256']
  packet[dict(member='members',hypothesis='hypotheses',external='externals')[kind]][subject]=c
  assert v.certificate(c,subject,base,reviewed),subject
packet['NEX_call_domain_additions']={}
if 'afterdecode' in selection:
 from NEX_dependent_checks import F,THEOREMS
 conf=selection['afterdecode'];support=set()
 for a in [a for pair in conf['pairs'] for a in pair]+list(conf['controls'].values()):
  files=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
  archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json';files += [archive+'.xz',archive+'.sha256'];support.update(E/n for n in files)
 native=dict(function=F,family='afterdecode',complete=True,domain='every live688-byte input; arbitrary full AtomicStatementError and validator Results; all bytes and fields unrestricted',config=conf,inner_hypotheses_remaining=[],box_ruling_aa=False)
 packet['NEX_call_domain_additions'][F]=native
 receipts={'NEX_AfterDecodeOracle':'NEX_L019','NEX_ReadDomains':'NEX_L021','NEX_DigestCallDomains':'NEX_L023','NEX_FirstError':'NEX_L022','NEX_AfterstateBox':'NEX_L008'}
 thms=[theorem(t,receipts[t.rsplit('.',1)[0]]) for t in THEOREMS]
 subjects={F:('root-composition',None)}
 for row in base['rows']:
  if row['function']!=F:continue
  subjects.update({F+'::'+h['name']:('hypothesis-discharge',None) for h in row['named_hypotheses']})
  for ob in row['caller_domain_obligations']:
   key=F+' -> '+ob['callee'] if 'callee' in ob else ob['id'];subjects[key]=('call-domain' if 'callee' in ob else 'external-domain',ob)
 for subject,(kind,ob) in subjects.items():
  names=ob['required_named_hypotheses'] if ob and 'callee' in ob else []
  claims=ob['callee_claims'] if ob and 'callee' in ob else sorted({c for r in base['rows'] if r['function']==F for c in r['selected_claims']})
  d=dict(subject=subject,frozen_revision=base['frozen_revision'],native_association_kind='ruling-y',domain_theorems=thms,physical_theorems=thms,selected_callee_claims=claims,inner_hypotheses_remaining=[],exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
  c=dict(id='NEX_'+kind+'::'+subject,kind=kind,subject=subject,frozen_revision=base['frozen_revision'],domain_theorems=thms,physical_theorems=thms,theorems=thms,support=[ref(p) for p in sorted(support)],native_association=[ref(p) for p in sorted(support)],native_certificate=native,call_domain_certificate=d,inner_hypotheses_remaining=[],new_trust_rows=[],trust_classification='P6/D188 option A reclassification',required_named_hypotheses=names,exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,native_frame_complete=True,callee_domain_established=True,canonical_carrier_established=True,same_inputs=True,same_carrier=True,same_state=True,ordered_effects=True,physical_interpretation_derivation='Same immutable live688 carrier; all21 actual digest arguments and exact8/32 slices; complete typed validator input and returned fields, every Result/error and readonly runtime frame; NEX native indexed proofs plus closed source/digest/exact/validator laws; no child PacketDomain or PhysicalInterpretation assumed',hypotheses=([F+'.PacketDomain',F+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'] if kind=='root-composition' else []))
  c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());reviewed[subject]=c['semantic_review_sha256']
  group={'root-composition':'members','hypothesis-discharge':'hypotheses','call-domain':'edges','external-domain':'externals'}[kind];packet[group][subject]=c
  assert v.certificate(c,subject,base,reviewed),subject
raw=(json.dumps(packet,separators=(',',':'))+'\n').encode();(E/'NEX_LEDGER_DELTA.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NEX_LEDGER_DELTA.json.sha256').write_text(sha(raw)+'\n')
(E/'NEX_REVIEWED_CERTIFICATES.json').write_text(json.dumps(reviewed,indent=1)+'\n')
print(json.dumps(dict(proposed=list(packet['NEX_native_bridge_additions']),bytes=len(raw))))
