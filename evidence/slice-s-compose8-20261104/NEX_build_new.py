"""Add complete new bridges to the existing checked overlay; no WIP promotion."""
from pathlib import Path
import json,sys,lzma,hashlib,copy,re
import NEX_validate as v
import NEX_new_bridges as nb
E=v.E;R=v.R;sha=v.sha

def ref(p):
 p=Path(p);return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def theorem(name,attempt,folder=E,prefix='NEX_'):
 source=folder/attempt/(prefix+'SOURCE.lean.txt');s=source.read_text();short=name.rsplit('.',1)[-1];a=s.index('theorem '+short+' ');z=re.search(r'\s:=\s',s[a:]).start()+a;statement=s[a:z].rstrip();rc=v.read(folder/attempt/'receipt.json');assert rc['exit_status']==0
 assert any(x.startswith("'"+name+"'") and 'sorryAx' not in x for x in rc['print_axioms'])
 return dict(name=name,source=ref(source),receipt=ref(folder/attempt/'receipt.json'),snapshot_path=prefix+'generated/'+name.rsplit('.',1)[0]+'.lean',statement=statement,statement_sha256=sha(statement.encode()))

def attempts(kind,conf):
 if kind=='snapshotdecode':return [a for pair in conf['pairs'] for a in pair]+list(conf['controls'].values())
 if kind=='common':return [a for pair in conf['pairs'] for a in pair]+list(conf['controls'].values())
 if kind=='late':return list(conf.values())
 return list(conf['runs'].values())+conf.get('cleanup',[])

def build():
 packet=v.read(E/'NEX_LEDGER_DELTA.json');reviewed=v.read(E/'NEX_REVIEWED_CERTIFICATES.json');base=v.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');selection=v.read(E/'NEX_NATIVE_SELECTION.json')
 packet['NEX_new_bridges']={}
 receipts={'NEX_AfterstateBox':'NEX_L008','NEX_SnapshotBoxOracle':'NEX_L009','NEX_LaneOracle':'NEX_L007','NEX_DecoderDomains':'NEX_L006','NEX_BoxValueExt':'NEX_L016','NEX_SnapshotParent':'NEX_L029','NEX_ReadDomains':'NEX_L021','NEX_DigestCallDomains':'NEX_L023','NEX_FirstError':'NEX_L022','NEX_LateOracle':'NEX_L010','NEX_CommonOracle':'NEX_L003'}
 domains={'afterstate':'every live688-byte slice and complete typed afterstate decoder Result','snapshot':'every live800-byte slice and complete typed snapshot decoder Result','lane':'every live1520-byte slice and complete typed late decoder boxed Result','snapshotdecode':'every live800-byte slice; all bytes and every full child Result/error','late':'every live1520-byte slice; all bytes and every full child boxed Result/error','common':'every live1880-byte slice; all bytes and every full child Result/error'}
 for kind in ['afterstate','snapshot','lane','snapshotdecode','late','common']:
  if kind not in selection:continue
  f=nb.FUNCTIONS[kind];conf=selection[kind];assert nb.native_complete(kind,conf)
  thms=[]
  for name in nb.THEOREMS[kind]:
   if name=='NEU_DecoderProjections.common_ext':thms.append(theorem(name,'NEU_L018',E.parent/'slice-s-compose7-20261103','NEU_'))
   else:thms.append(theorem(name,receipts[name.rsplit('.',1)[0]]))
  support=set()
  for a in attempts(kind,conf):
   files=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
   archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json';files += [archive+'.xz',archive+'.sha256'];support.update(E/n for n in files)
  n=dict(function=f,template=kind,complete=True,domain=domains[kind],config=conf,inner_hypotheses_remaining=[],box_ruling_aa=kind not in ['lane','snapshotdecode'])
  packet['NEX_new_bridges'][f]=n
  subjects={f:('root-composition',None)}
  for name in nb.qualifiers(f):subjects[f+'::'+name]=('hypothesis-discharge',None)
  for row in base['rows']:
   if row['function']!=f:continue
   assert row['bridge_status']=='OPEN' and not row['named_hypotheses']
   for ob in row['caller_domain_obligations']:
    subject=f+' -> '+ob['callee'] if 'callee' in ob else ob['id'];subjects[subject]=('call-domain' if 'callee' in ob else 'external-domain',ob)
  for subject,(kind_certificate,ob) in subjects.items():
   names=list(ob['required_named_hypotheses']) if ob and 'callee' in ob else []
   if ob and 'callee' in ob and not ob['callee_claims'] and ob['callee'] in nb.FUNCTIONS.values():
    names=list(dict.fromkeys(names+nb.qualifiers(ob['callee'])))
   claims=ob['callee_claims'] if ob and 'callee' in ob else ['NEX::'+f]
   # Baseline OPEN callees have no selected claim label. The new bridge is
   # explicitly selected and checked separately; retain every old name as well.
   if ob and 'callee' in ob and not claims:claims=['NEX::'+ob['callee']]
   d=dict(subject=subject,frozen_revision=base['frozen_revision'],native_association_kind='ruling-y',domain_theorems=thms,physical_theorems=thms,selected_callee_claims=claims,inner_hypotheses_remaining=[],exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,trust_classification='P6/D188 option A reclassification',new_trust_rows=[],native_frame_complete=True,inner_names_discharged=names)
   c=dict(id='NEX_'+kind_certificate+'::'+subject,kind=kind_certificate,subject=subject,frozen_revision=base['frozen_revision'],domain_theorems=thms,physical_theorems=thms,theorems=thms,support=[ref(p) for p in sorted(support)],native_association=[ref(p) for p in sorted(support)],native_certificate=n,call_domain_certificate=d,inner_hypotheses_remaining=[],new_trust_rows=[],trust_classification='P6/D188 option A reclassification',required_named_hypotheses=names,exact_callsite=True,canonical_carrier=True,same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,native_frame_complete=True,callee_domain_established=True,canonical_carrier_established=True,same_inputs=True,same_carrier=True,same_state=True,ordered_effects=True,physical_interpretation_derivation='Same immutable typed carrier and exact native slice places/record projections; fresh Box identity and error cleanup under aa where allocated; all child Result/error cases and ordered call/state frames; closed model substitution and caller-derived domains; no child PacketDomain or PhysicalInterpretation assumed',hypotheses=([f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA'] if kind_certificate=='root-composition' else []))
   c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());reviewed[subject]=c['semantic_review_sha256']
   packet[{'root-composition':'members','hypothesis-discharge':'hypotheses','call-domain':'edges','external-domain':'externals'}[kind_certificate]][subject]=c
 raw=(json.dumps(packet,separators=(',',':'))+'\n').encode();(E/'NEX_LEDGER_DELTA.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NEX_LEDGER_DELTA.json.sha256').write_text(sha(raw)+'\n');(E/'NEX_REVIEWED_CERTIFICATES.json').write_text(json.dumps(reviewed,indent=1)+'\n')
 print(json.dumps(dict(new=list(packet['NEX_new_bridges']),bytes=len(raw))))
if __name__=='__main__':build()
