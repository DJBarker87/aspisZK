from pathlib import Path
import json,base64,lzma,hashlib,re,copy
B=Path.cwd();P=B.parent/'codex-cx-extract-stage-20261106';sha=lambda raw:hashlib.sha256(raw).hexdigest()
raw=lzma.decompress((P/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes());assert sha(raw)==(P/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip();frozen={n:base64.b64decode(v).decode() for n,v in json.loads(raw).items() if n.endswith('.rs')}
def check(x):
 assert x['frozen']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 assert sha(x['fragment'].encode())==x['fragment_sha256']
 assert x['fragment'] in frozen[x['path']]
 return True
cuts=[json.loads((B/n).read_text()) for n in ['NIL_TREE_CUT.json','NIL_PREFIX_NATIVE_CUT.json','NIL_CTOR_CUT.json']]
for x in cuts:assert check(x)
controls=[]
for i,x in enumerate(cuts):
 for mode in ['hash','source']:
  y=copy.deepcopy(x);y['fragment']+=' NIL_CORRUPTION'
  if mode=='source':y['fragment_sha256']=sha(y['fragment'].encode())
  try:check(y)
  except AssertionError:controls.append(dict(cut=i,corruption=mode,rejected=True))
  else:raise AssertionError('accepted modified cut')
s=frozen['crates/aspis-r1-cost-probe/src/candidate.rs'];a=s.index('fn batch_merkle<');z=s.index('\n}',a)+2;parent=s[a:z]
def parent_check(body):
 assert set(re.findall(r'\bp\.(\w+)',body))=={'roots','queries'}
 assert not re.search(r'\bproof\s*\[',body)
 assert 'batch_merkle_values(proof, p.queries, [root0, root1, *folded_root], batch, hash)' in body
parent_check(parent)
for name,body in [('extra_field',parent+' p.rho'),('proof_read',parent+' proof[0]'),('root_order',parent.replace('[root0, root1, *folded_root]','[root1, root0, *folded_root]'))]:
 try:parent_check(body)
 except AssertionError:controls.append(dict(parent_corruption=name,rejected=True))
 else:raise AssertionError('accepted modified projection')
assert 'bytes[11..16].iter().any(|&b|b!=0)' in frozen['crates/aspis-r1-cost-probe/src/verifier.rs']
out=dict(status='PASS',literal_cuts=len(cuts),negative_controls=controls,parent_sha256=sha(parent.encode()),prepared_projection_fields=['roots','queries'],projection_scope='frozen parent body forwards proof; no proof byte read or other Prepared field; native leaf/tree and complete frame laws still OPEN',header_window='checkpoint[11..16], same frozen callback',no_closed_row_credit=True)
(B/'NIL_PROJECTION_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
