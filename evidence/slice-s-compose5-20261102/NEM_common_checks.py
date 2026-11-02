"""Exact source windows and same-call certificates for the common encoder."""
from pathlib import Path
import json,hashlib,subprocess,re
FUNCTION='crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common'
PAIRS=[('NEJ_K005','NEJ_K006'),('NEJ_K007','NEJ_K008'),('NEJ_K009','NEJ_K010')]+[(f'NEJ_K{i:03}',f'NEJ_K{i+1:03}') for i in range(14,28,2)]

def validate(c,expected,ledger,v):
 try:
  q=c['common_composition'];f=FUNCTION
  assert q['function']==f and q['all_typed_inputs'] and q['same_complete_prestate']
  assert q['method']=='source-ordered window composition with same-call child instances'
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['windows']==[[0,4],[4,1],[5,1],[6,1],[8,32],[40,32],[72,8],[80,32],[112,32],[144,4]]
  assert q['native_pairs']==[['NEM_K006','NEM_K007'],['NEM_K008','NEM_K009'],['NEM_K010','NEM_K011']]
  assert all(v.native_pair(*p) for p in q['native_pairs'])
  assert q['inherited_windows']==[list(p) for p in PAIRS]
  P=v.R/'evidence/slice-s-compose3-20261101'
  assert all(v.native_pair(*p,folder=P,prefix='NEJ_') for p in PAIRS)
  assert q['frame']=='only bytes [0,7) union [8,148); original byte 7 and suffix >=148 preserved'
  assert q['empty_child_modifies'] and q['reply_widths']==[32,32,4]
  assert q['ordered_children']==['common.anchor_root','common.nullifier','common.asset_id']
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+f.split('::')[0]],cwd=v.R,text=True)
  a=source.index('fn encode_common(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  stmts=[x.strip()+';' for x in body[body.index('    output[..4]'):body.rindex('}')].split(';') if x.strip()]
  assert stmts==q['statements'] and len(stmts)==10
  # This exact sequence is also the accepted emitted frame's source sequence.
  assert [re.sub(r'\s+','',x) for x in stmts]==[
   'output[..4].copy_from_slice(&magic);','output[4]=POOL_V1_PAYMENT_STATEMENT_VERSION;','output[5]=kindasu8;',
   'output[6]=POOL_V1_DIGEST_ENCODING_VERSION;',
   'output[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&common.pool);',
   'output[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET].copy_from_slice(&common.deployment_domain);',
   'output[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET].copy_from_slice(&common.anchor_sequence.to_le_bytes());',
   'output[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET].copy_from_slice(&encode_digest_canonical(&common.anchor_root));',
   'output[NULLIFIER_OFFSET..ASSET_ID_OFFSET].copy_from_slice(&encode_digest_canonical(&common.nullifier));',
   'output[ASSET_ID_OFFSET..AMOUNT_OR_RESERVED_OFFSET].copy_from_slice(&common.asset_id.to_le_bytes());']
  for name,value in [('POOL_OFFSET',8),('DEPLOYMENT_DOMAIN_OFFSET',40),('ANCHOR_SEQUENCE_OFFSET',72),('ANCHOR_ROOT_OFFSET',80),('NULLIFIER_OFFSET',112),('ASSET_ID_OFFSET',144),('AMOUNT_OR_RESERVED_OFFSET',148)]:
   assert re.search(r'const '+name+r': usize = '+str(value)+r';',source)
  assert [t['name'] for t in q['theorems']]==['NEJ_CommonSourceFrame.result_and_frame','NEJ_CommonFrame.common_bytes','NEJ_WindowStep.iteration','NEL_CopyArrayLaw.loop_binding']
  assert all(v.inherited.theorem(t) for t in q['theorems'])
  for ref in q['native_support']:v.inherited.artifact(ref)
  from NEM_artifacts import native_support,ref
  required=native_support([a for p in q['native_pairs'] for a in p])
  for pair in PAIRS:
   for a in pair:
    required += [ref(P/n) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEJ_native_contracts.patch',a+'-NEJ_oracle.patch']]
  assert q['native_support']==required
  rs=[r for r in ledger['rows'] if r['function']==f];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={f}|{f+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{f+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  if c['kind']=='alternative-resolution':
   assert expected==f+' -> crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'
   assert 'asset_id: M31,' in source and 'common.asset_id.to_le_bytes()' in body
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
