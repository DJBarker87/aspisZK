"""Review inherited ADOPTED field bridges, never manufacture a native pass."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
D=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');scope=obj(E/'NEB_SCOPE.json');assert sha((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_bytes())==scope['ledger_sha256']
F=D['frozen_revision'];field='crates/aspis-core/src/field.rs::';wide='crates/aspis-core/src/field/wide_exact.rs::'
FUNCTIONS=[field+'M31::mul',field+'CM31::mul',field+'CM31::mul_m31',field+'QM31::mul',field+'QM31::mul_m31',field+'mul_by_r',wide+'mul_u',wide+'WideExact::mul',wide+'WideExact::mul_m31',wide+'WideExact::mul_qm31']
records=[]
for f in FUNCTIONS:
 rows=[r for r in D['rows'] if r['function']==f];assert rows
 for r in rows:
  assert r['bridge_status']=='CLOSED-CONDITIONAL' and r['selected_claims'] and r['frozen_body_verified'] and not r['no_credit_reason']
  assert r['feature_parity'] and all(x['status']=='SAME BODIES' for x in r['feature_parity'])
  raw=subprocess.check_output(['git','show',F+':'+r['source_file']],cwd=R);a,b=r['frozen_body_byte_range'];body=raw[a:b]
  assert sha(raw)==r['source_file_sha256'] and sha(body)==r['frozen_body_sha256']
  assert not any(x in body for x in [b'Option<fn',b'copy_from_slice',b'copy_nonoverlapping',b'.clone(',b'.to_vec(',b'Vec::',b'alloc::',b'sol_sha256',b'hashv(',b'unsafe'])
  receipts=[]
  for p,h in r['receipt_sha256'].items():
   packet=subprocess.check_output(['git','show','HEAD:'+p],cwd=R);assert sha(packet)==h
   receipt=json.loads(packet)
   receipts.append(dict(path=p,sha256=h,kind=receipt['kind'],exit_status=receipt['exit_status'],role='adopted successful evidence' if receipt['exit_status']==0 else 'EXCLUDED historical failure, zero proof credit'))
  assert any(x['kind']=='lean' and x['exit_status']==0 for x in receipts),'no successful inherited field proof'
  records.append(dict(row=r['row'],function=f,selected_claims=r['selected_claims'],native_body_sha256=r['frozen_body_sha256'],feature_parity=r['feature_parity'],inherited_receipts=receipts,bridge_source='Authoritative NDT already-adopted conditional field bridge; NOT a newly claimed Kani proof',qualification='Only own-root PacketDomain/PhysicalInterpretation plus approved P6/D188 trust. New call-domain and carrier/Result/frame certificates remain mandatory.'))
out=dict(schema='NEB-adopted-field-transport-review-v1',authoritative_ledger_sha256=scope['ledger_sha256'],frozen_revision=F,records=records,method='LEAD field-translation ruling A and existing adopted NBG/LPi/JFv bridge; compose through the caller own CLOSED-CONDITIONAL bridge, not a new evaluator or XRn stand-in',not_a_kani_result=True,field_multiplication_in_kani=False,trust='Approved NativeContractSemanticTransport option A is reclassification, never removal',remaining='This review alone gives ZERO composition credit. New exact call-domain/inner interpretation/Result/state/effect witnesses are separately required; no SDK/ELF/headline result.')
p=E/'NEB_FIELD_TRANSPORT_REVIEW.json'
if '--check' in sys.argv:assert obj(p)==out
else:p.write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(adopted_bridge_functions=len(FUNCTIONS),occurrences=len(records),new_native_passes=0,composition_credit_from_review_alone=0)))
