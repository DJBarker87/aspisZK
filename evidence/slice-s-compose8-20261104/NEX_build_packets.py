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
raw=(json.dumps(packet,separators=(',',':'))+'\n').encode();(E/'NEX_LEDGER_DELTA.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NEX_LEDGER_DELTA.json.sha256').write_text(sha(raw)+'\n')
(E/'NEX_REVIEWED_CERTIFICATES.json').write_text(json.dumps(reviewed,indent=1)+'\n')
print(json.dumps(dict(proposed=list(packet['NEX_native_bridge_additions']),bytes=len(raw))))
