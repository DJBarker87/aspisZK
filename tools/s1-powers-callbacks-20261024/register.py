#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
names={'S1PowersCallbackChainV1':'s1-powers-callback-chain-v4','S1PowersCallbackSlotsV1':'s1-powers-callback-slots-v1','S1PowersCanonicalInjectiveV1':'s1-powers-canonical-injective-v1','S1PreparedPowersCallbacksV1':'s1-prepared-powers-callbacks-v2','S1PreparedPowersScratchV1':'s1-prepared-powers-scratch-v2','S1TopPrepareCallbackProgramV1':'s1-top-prepare-callback-program-v1'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rs=[];m=json.loads((E/'accepted-targets.json').read_text())
for n,a in names.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['target']==n and r['exit_status']==0,n
 assert sha(S/(n+'.lean'))==r['source_sha256'] and sha(E/a/'source.lean')==r['source_sha256'],n
 assert sha(Path('/tmp/s126-current-caller-20261021-objects')/(n+'.olean'))==r['object_sha256'],n
 assert r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms']),n
 rs.append(r);m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json'
metrics={'targets':len(names),'wall_seconds':sum(r['wall_seconds'] for r in rs),'max_rss_bytes':max(r['peak_rss_bytes'] for r in rs),'swaps':sum(r['swaps'] for r in rs)}
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
(E/'s1-powers-callback-targets.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','targets':names,'metrics':metrics,'qualification':'Complete emitted callback chain on canonical arithmetic domain, exact source slot order, full raw scratch equality and final multiplication from same accepted op7 execution. ACCEPTED-ONLY parent; not unconditional R22, native Std/from_fn/SDK or release security closure.'},indent=2)+'\n')
failed=[]
for glob in ['s1-powers-callback-chain-v*','s1-powers-callback-slots-v*','s1-powers-canonical-injective-v*','s1-prepared-powers-callbacks-v*','s1-prepared-powers-scratch-v*','s1-top-prepare-callback-program-v*']:
 for p in sorted(E.glob(glob+'/receipt.json')):
  r=json.loads(p.read_text())
  if r['exit_status']!=0:failed.append({'receipt':str(p.relative_to(E)),**{k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','source_sha256']}})
(E/'s1-powers-callback-failures.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':failed,'explanation':'Tuple/closure alias normalization, ambiguous reflexivity and missing namespace elaboration failures, retained outside accepted imports; no resource defaults changed.'},indent=2)+'\n')
(E/'s1-powers-callback-tool-pins.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','scripts':{str(p.relative_to(R)):sha(p) for p in sorted((R/'tools/s1-powers-callbacks-20261024').glob('*.py'))}},indent=2)+'\n')
print(json.dumps(metrics))
