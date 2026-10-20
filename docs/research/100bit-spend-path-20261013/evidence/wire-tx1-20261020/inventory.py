from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[5]
ev=Path(__file__).resolve().parent
paths=['crates/aspis-r1-cost-probe/src/'+f+'.rs' for f in ['candidate','compact','r1_wire','r1_semantic','transcript','multiproof','verifier']]
paths+=['crates/aspis-core/src/state_only_private_merkle.rs','crates/aspis-core/src/r0/merkle.rs','crates/aspis-core/src/digest.rs','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']
paths += ['docs/research/100bit-spend-path-20261013/lean/'+f for f in ['extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Funs.lean','extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Types.lean','ExtractedDigest32Transcript.lean','ExtractedDigest32Callers.lean','ExtractedDigest32Begin.lean','ExtractedPrefixParse.lean','ExtractedRecordFraming.lean','ExtractedRowShape.lean']]
paths += ['docs/research/100bit-spend-path-20261013/lean/'+f for f in ['bridge-prepared-3335-20261016/ExtractedPreparedModel.lean','bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean','bridge-tx1-e5c186ba3-20261016/ExtractedTx1Model.lean']]
def pin(p):
 b=(root/p).read_bytes();return dict(path=p,sha256=hashlib.sha256(b).hexdigest(),size_bytes=len(b))
sites=[]
for p in paths[:12]:
 for line,s in enumerate((root/p).read_text().splitlines(),1):
  for match in re.finditer(r'\.digest\(',s):
   cone='outside'
   category='not in adopted tx1'
   if p.endswith('r1_wire.rs') and 179<=line<=205:cone='tx1';category='initializer' if line==182 else 'semantic absorb' if line==203 else 'read/advance'
   if p.endswith('transcript.rs') and line<=54:cone='tx1';category='opening reseed' if line==12 else 'opening absorb' if line==15 else 'read/advance'
   if p.endswith('state_only_private_merkle.rs') and line==46:cone='tx1';category='salted leaf'
   if p.endswith('multiproof.rs') and line in [139,146,148]:cone='tx1';category='binary parent'
   if p.endswith('verifier.rs') and line in [274,284]:cone='tx1';category='checkpoint binding/checksum'
   sites.append(dict(path=p,line=line,column=match.start()+1,cone=cone,category=category,source=s.strip()))
backend_calls=[dict(path='programs/r1-cost-probe/src/lib.rs',line=i,source=s.strip(),cone='tx1 backend' if i==14 else 'stage2 checksum update') for i,s in enumerate((root/'programs/r1-cost-probe/src/lib.rs').read_text().splitlines(),1) if 'hashv(' in s]
result=dict(hashv_sites=backend_calls,schema='wire-tx1-source-inventory-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),scope='Source-reading inventory; no whole-cone extraction or execution proof',pins=[pin(p) for p in paths],digest_sites=sites,counts=dict(tx1_syntactic_digest_sites=sum(s['cone']=='tx1' for s in sites)),checkpoint=dict(proof_bytes=57607,public_asf8_bytes=1880,checkpoint_bytes=1768,checksum_body_bytes=1736,checksum_domain_bytes=22,checksum_input_bytes=1758))
(ev/'source-inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['counts'])
