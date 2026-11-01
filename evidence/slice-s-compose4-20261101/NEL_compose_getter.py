from pathlib import Path
import hashlib,json,copy
E=Path(__file__).resolve().parent;R=E.parent.parent
ref=lambda p:dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
p=json.loads((E/'NEL_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEL_REVIEWED_CERTIFICATES.json').read_text())
f=next(k for k in p['members'] if k.endswith('::PoolV1PairForestTerminalStatementV1::common'))
for key,c in [(f,p['members'][f])]+[(k,v) for k,v in p['hypotheses'].items() if k.startswith(f+'::')]:
 c['id']='NEL_'+key;c.pop('direct_contract',None)
 c['borrowed_projection']=dict(method='C3-BIN ruling (y-prime), 2026-11-01',function=f,all_typed_inputs=True,empty_modifies=True,no_stub_verified=True,trust_classification='P6/D188 option A reclassification',source_identity=ref(E/'NEL_GETTER_IDENTITY.json'),extracted_identity='NED_ReconstructCarriers.common_argument',axioms_audit=ref(E/'NEL_L001/receipt.json'))
 c['borrowed_projection']['native_support']=[ref(E/n) for a in ['NEL_K006','NEL_K007'] for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEL_native_contracts.patch',a+'-NEL_oracle.patch']]
 c['native_association'] += [ref(E/'NEL_K006/receipt.json'),ref(E/'NEL_K007/receipt.json'),ref(E/'NEL_GETTER_IDENTITY.json')]
 c['physical_interpretation_derivation']+=' Ruling y-prime: pure projection preserves the precise receiver place and borrow lifetime. Complete native caller passes with designated field and fails with the disjoint harness-owned field. No Arbitrary reference or stub_verified is used.'
 c['call_domain_certificate']['exact_callsite']='Frozen getter projection and first validator callsite; actual receiver field place, unchanged native caller with arbitrary full child Results; ruling y-prime.'
 c.pop('semantic_review_sha256',None);h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review[key]=h
(E/'NEL_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n');(E/'NEL_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
