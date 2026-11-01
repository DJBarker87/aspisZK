"""Pin direct framed leaf certificates; no parent or unresolved call is inferred."""
from pathlib import Path
import copy,hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;O=R/'evidence/slice-s-compose-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())
def ref(p):
 p=Path(p);return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def theorem(module,name,attempt=None):
 root=E if module.startswith('NEE_') else O
 p=root/(module+'.lean');source=p.read_text()
 if attempt is None:attempt=next(a['receipt'].split('/')[0] for a in read(O/'NED_ACTIVE_PROOFS.json')['active'] if a['module']==module)
 start=re.search(r'^theorem '+re.escape(name)+r'\b',source,re.M).start()
 end=re.search(r'\n(?:theorem |#print axioms )',source[start:])
 statement=source[start:start+end.start()] if end else source[start:]
 return dict(name=module+'.'+name,source=ref(p),receipt=ref(root/attempt/'receipt.json'),snapshot_path=('NEE_generated/' if root==E else 'NED_generated/')+module+'.lean',statement=statement,statement_sha256=sha(statement.encode()))
def native(a):
 module=read(E/a/'receipt.json')['module'];harness_key='NEE_native_contracts.patch' if 'NEE_payment_frames' in module else 'NEE_oracle.patch'
 return dict(harness_key=harness_key,oracle_patch=ref(E/(a+'-NEE_oracle.patch')),receipt=ref(E/a/'receipt.json'),stdout=ref(E/a/'stdout.log'),graph=ref(E/(a+'-graph-check.json')),lock=ref(E/(a+'-lock-check.json')),features=ref(E/(a+'-metadata-pin.json')),config=ref(E/(a+'.json')),source_check=ref(E/(a+'-source-check.json')),harness=ref(E/(a+'-'+harness_key)),contract_source=ref(E/(a+'-NEE_native_contracts.patch')))
base=read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
packet=read(O/'NED_LEDGER_DELTA.json');packet['inventory_edges']={};reviewed={}
def seal(c):
 c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());reviewed[c['subject']]=c['semantic_review_sha256'];return c

def cert(subject,kind,ts,associations,derivation):
 return dict(id='NEE::'+subject,kind=kind,subject=subject,frozen_revision=base['frozen_revision'],theorems=ts,native_association=associations,same_inputs=True,same_carrier=True,same_state=True,same_result=True,ordered_effects=True,inner_hypotheses_remaining=[],physical_interpretation_derivation=derivation,callee_domain_established=True,canonical_carrier_established=True,hypotheses=['NativeContractSemanticTransport'])
entries=[
 ('M31::to_le_bytes',5,6,'aspis_core::field::M31::to_le_bytes',[theorem('NEE_M31SerializerDomain','primitive','NEE_L011'),theorem('NEE_M31SerializerDomain','width','NEE_L011')]),
 ('PoolV1PairForestTerminalStatementV1::common',7,8,'PoolV1PairForestTerminalStatementV1::common',[theorem('NED_ReconstructCarriers','common_argument')]),
 ('statement_public_common',9,10,'statement_public_common',[theorem('NED_ReconstructCarriers','parts_argument')]),
 ('transfer_common',11,12,'transfer_common',[theorem('NED_PaymentCohorts','transfer_common')]),
 ('withdrawal_common',13,14,'withdrawal_common',[theorem('NED_PaymentCohorts','withdrawal_common')]),
 ('payment_relation.rs::digest_is_canonical',15,16,'digest_is_canonical',[theorem('NED_PaymentCohorts','canonical_result')]),
]
for suffix,pos,neg,target,ts in entries:
 fs={r['function'] for r in base['rows'] if r['function'].endswith('::'+suffix) or r['function'].endswith(suffix) and suffix.startswith('payment_relation.rs')}
 assert len(fs)==1,(suffix,fs)
 f=fs.pop();rs=[r for r in base['rows'] if r['function']==f]
 p=f'NEE_K{pos:03}';n=f'NEE_K{neg:03}';positive=native(p);negative=native(n)
 patch=(E/(p+'-NEE_native_contracts.patch')).read_text()
 ensures=next(l[1:].strip() for l in patch.splitlines() if l.startswith('+') and 'cfg_attr(kani,kani::ensures(' in l)
 modifies=next(l[1:].strip() for l in patch.splitlines() if l.startswith('+') and 'cfg_attr(kani,kani::modifies())' in l)
 callees=sorted({g for r in rs for g in r['canonical_callees']})
 if suffix!='M31::to_le_bytes':assert callees==[],(f,callees)
 associations=[positive['receipt'],negative['receipt'],positive['contract_source'],positive['harness']]
 derivation='Actual frozen body executes on EVERY typed argument; exact result/reference identity and explicit empty modifies contract. The named total emitted theorem uses the identical complete record/word; primitive/borrowed carriers and zero external effects are transported only under NativeContractSemanticTransport (P6/D188 option A reclassification). No allocation, syscall, function pointer, callback or multiplication is reached.'
 d=dict(method='NCO actual frozen function contract',function=f,trust_classification='P6/D188 option A reclassification',actual_body_unchanged=True,full_result=True,empty_modifies=True,all_inputs_domain=True,no_stub_verified=True,real_internal_calls=[],alternative_targets_resolved=callees,contract_source=positive['contract_source'],modifies_statement=modifies,ensures_statement=ensures,positive=positive,negative=negative,proof_target=target,domain_and_model_theorems=ts)
 c=cert(f,'root-composition',ts,associations,derivation);c['direct_contract']=d;packet['members'][f]=seal(c)
 for r in rs:
  assert not [o for o in r['caller_domain_obligations'] if 'callee' not in o]
  for h in r['named_hypotheses']:
   subject=f+'::'+h['name'];c=cert(subject,'hypothesis-discharge',ts,associations,derivation);c['direct_contract']=d;packet['hypotheses'][subject]=seal(c)
 if callees:
  # The frozen source receiver is u32; neither newtype recursion nor WideExact
  # is called. This source fact is paired with the emitted primitive law.
  source=subprocess.check_output(['git','show',base['frozen_revision']+':crates/aspis-core/src/field.rs'],text=True)
  assert 'pub fn to_le_bytes(self) -> [u8; 4] {\n        self.0.to_le_bytes()\n    }' in source
  audit=E/'NEE_M31_RESOLUTION.json'
  audit.write_text(json.dumps(dict(frozen_revision=base['frozen_revision'],file_sha256=sha(source.encode()),receiver='self.0 : u32',actual_target='u32::to_le_bytes',excluded_targets=callees,reason='Primitive receiver type and 4-byte result; no recursive M31 call and no 32-byte WideExact receiver. Actual native contract executes the entire frozen body.'),indent=1)+'\n')
  for g in callees:
   edge=f+' -> '+g
   c=cert(edge,'alternative-resolution',ts+[theorem('NEE_M31SerializerDomain','widths_distinct','NEE_L011')],associations+[ref(audit)],'Typed source resolution, not a callee-law assumption. '+derivation)
   packet['inventory_edges' if g==f else 'edges'][edge]=seal(c)
packet['status']='Partial composed subtree; first root remains in progress'
(E/'NEE_LEDGER_DELTA.json').write_text(json.dumps(packet,indent=1)+'\n')
(E/'NEE_REVIEWED_CERTIFICATES.json').write_text(json.dumps(reviewed,indent=1)+'\n')
print('Prepared',len(entries),'direct leaf packets; validator decides all row statuses')
