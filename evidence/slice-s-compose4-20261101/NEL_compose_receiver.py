from pathlib import Path
import json,copy,hashlib
from NEL_artifacts import ref,theorem
E=Path(__file__).resolve().parent;R=E.parent.parent
p=json.loads((E/'NEL_LEDGER_DELTA.json').read_text());review=json.loads((E/'NEL_REVIEWED_CERTIFICATES.json').read_text())
original=next(c for k,c in p['edges'].items() if k.startswith('crates/aspis-core/src/field.rs::M31::to_le_bytes -> ') and c['kind']=='alternative-resolution')
f='crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical';edge=f+' -> crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'
c=copy.deepcopy(original);c['id']='NEL_receiver_'+edge;c['subject']=edge
c['theorems'].append(theorem('NEL_DigestLoopFrame','step_and_bytes'))
c['native_association']+=[ref(E/'NEL_K012/receipt.json'),ref(E/'NEL_RECEIVER.json')]
c['receiver_resolution']=dict(function=f,receiver='&M31',excluded='WideExact',source_check=ref(E/'NEL_RECEIVER.json'),compile_receipt=ref(E/'NEL_K012/receipt.json'),compile_source=ref(E/'NEL_K012-NEL_native_contracts.patch'),actual_source_expression='value.to_le_bytes()',no_execution_of_alternative=True,trust_classification='P6/D188 option A reclassification')
c['call_domain_certificate']['subject']=edge;c['call_domain_certificate']['exact_callsite']='Atomic digest loop: value is &M31 through the actual frozen Digest alias. Its inherent four-byte serializer is selected; the WideExact 32-byte candidate is not called.'
c['physical_interpretation_derivation']='Static receiver and inherent-method resolution, checked against four frozen source files and the successful typed M31 probe; model body/serializer identity imported. No order, heap, actual Enumerate count, parent bridge or WideExact execution is inferred.'
c.pop('semantic_review_sha256',None);h=hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest();c['semantic_review_sha256']=h;review[edge]=h;p['edges'][edge]=c
(E/'NEL_LEDGER_DELTA.json').write_text(json.dumps(p,indent=1)+'\n');(E/'NEL_REVIEWED_CERTIFICATES.json').write_text(json.dumps(review,indent=1)+'\n')
