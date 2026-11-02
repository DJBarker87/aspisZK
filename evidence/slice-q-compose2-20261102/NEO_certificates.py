"""Exact new leaf registrations over NEN; no historical credit changed."""
from pathlib import Path
import json,hashlib
import NEO_native_review as native
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def expected(base,check_receipt):
 review=native.review();assert review==obj(E/'NEO_NATIVE_REVIEW.json')
 definitions={
  'crates/aspis-core/src/field.rs::M31::from_le_bytes':dict(native='M31::from_le_bytes',domain='Every owned [u8;4], full Option; no canonical input or acceptance premise',proofs=[('NEO_L004',['NEO_ParserShapes.scalar_result']),('NEO_L011',['NEO_ParserReference.scalar']),('NEO_L015',['NEO_ParserCanonical.scalar'])],externals={'u32::from_le_bytes':'SAME_BYTES_STANDARD_U32_LE','Some':'TRANSPARENT_SOME','M31':'TRANSPARENT_M31'}),
  'crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs':dict(native='WideExact::from_limbs',domain='Every owned [u32;8], full Option; no canonical input or acceptance premise',proofs=[('NEO_L004',['NEO_ParserShapes.limbs_result','NEO_ParserShapes.wide_observation_injective']),('NEO_L011',['NEO_ParserReference.limbs']),('NEO_L012',['NEO_ParserTotal.eight','NEO_ParserTotal.result','NEO_ParserTotal.option_lossless']),('NEO_L015',['NEO_ParserCanonical.wide'])],externals={'Some':'TRANSPARENT_SOME','M31':'TRANSPARENT_M31'})
 }
 rows={}
 association=E/'NEO_PARSER_ASSOCIATION.md'
 for row in base['rows']:
  spec=definitions.get(row['function'])
  if spec is None:continue
  assert row['composed_status']=='OPEN' and row['frozen_body_verified']
  nr=review[spec['native']];proofs=[]
  for a,names in spec['proofs']:
   p=E/a/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),theorems=names)
   for name in names:
    rc=check_receipt(item,name)
    for source,digest in rc['source_hashes'].items():
     assert sha(E/source)==digest,'current proof source differs from successful one'
   proofs.append(item)
  native_receipt=obj(E/nr['positive']/'receipt.json')
  code=native.snapshot(nr['positive'])['NEO_src/'+row['source_file']].encode()
  a,b=row['frozen_body_byte_range'];assert hashlib.sha256(code[a:b]).hexdigest()==row['frozen_body_sha256']
  externals={}
  for obligation in row['caller_domain_obligations']:
   assert 'callee' not in obligation,'new leaf unexpectedly has an internal call'
   syntax=obligation['call'].get('expression',obligation['call'].get('syntax'));assert syntax in spec['externals'],syntax
   externals[obligation['id']]=dict(kind=spec['externals'][syntax],syntax=syntax,source_line=obligation['call']['line'],source_body_sha256=row['frozen_body_sha256'],proofs=[n for p in proofs for n in p['theorems']])
  rows[row['row']]=dict(id='NEO-parser-root:'+row['row'],row=row['row'],function=row['function'],frozen_revision=base['frozen_revision'],frozen_body_sha256=row['frozen_body_sha256'],claim_id='NEO::'+row['function'],domain=spec['domain'],parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,native_pair=[nr['positive'],nr['negative']],active_support_receipts=[str((E/nr['positive']/'receipt.json').relative_to(R))],historical_support_restored=[],inner_hypotheses_discharged=[h['name'] for h in row['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in row['inventory_domain_obligations']],external_obligations=externals,remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],review=dict(path=str(association.relative_to(R)),sha256=sha(association),conclusion_hiding=False,statement_and_native_association_checked=True),native_review=dict(path=str((E/'NEO_NATIVE_REVIEW.json').relative_to(R)),sha256=sha(E/'NEO_NATIVE_REVIEW.json')))
 assert len(rows)==4
 return rows
