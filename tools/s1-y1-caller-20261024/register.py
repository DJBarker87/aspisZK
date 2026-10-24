#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
names={'S1PrepareBufferY1RecombineV1':'s1-prepare-buffer-y1-recombine-v1','S1WideViewY1V1':'s1-wide-view-y1-v1','S1PrepareBothBuffersV1':'s1-prepare-both-buffers-v1','S1ClaimY1ReadsV1':'s1-claim-y1-reads-v1','S1ValuesOwnedPrepareViewY1V1':'s1-values-owned-prepare-view-y1-v2','S1TopPrepareY1ProvenanceV1':'s1-top-prepare-y1-provenance-v2','S1ValuesOwnedStage1ViewY1V1':'s1-values-owned-stage1-view-y1-v1'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rs=[];m=json.loads((E/'accepted-targets.json').read_text())
for n,a in names.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['target']==n and r['exit_status']==0,n
 assert sha(S/(n+'.lean'))==r['source_sha256'] and sha(E/a/'source.lean')==r['source_sha256'],n
 assert sha(Path('/tmp/s126-current-caller-20261021-objects')/(n+'.olean'))==r['object_sha256'],n
 assert r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms']),n
 rs.append(r);m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json'
metrics={'targets':len(names),'wall_seconds':sum(r['wall_seconds'] for r in rs),'max_rss_bytes':max(r['peak_rss_bytes'] for r in rs),'swaps':sum(r['swaps'] for r in rs)}
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
(E/'s1-y1-caller-targets.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','targets':names,'metrics':metrics,'qualification':'Same accepted full preparation/installed op7/owned stage1 derives actual View.y1 reconstruction and exact byte content, and all 29 concrete field parses with canonical full outputs. ACCEPTED-ONLY, source-model installation; no native SDK/runtime, arbitrary-input R22 or security closure.'},indent=2)+'\n')
failed=[]
for glob in ['s1-y1-recombine-probe-v*','s1-prepare-buffer-y1-recombine-v*','s1-wide-view-y1-v*','s1-prepare-both-buffers-v*','s1-claim-y1-reads-v*','s1-values-owned-prepare-view-y1-v*','s1-top-prepare-y1-provenance-v*','s1-values-owned-stage1-view-y1-v*']:
 for p in sorted(E.glob(glob+'/receipt.json')):
  r=json.loads(p.read_text())
  if r['exit_status']!=0:failed.append({'receipt':str(p.relative_to(E)),**{k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','source_sha256']}})
(E/'s1-y1-caller-failures.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':failed,'explanation':'The sole failed probe printed Std range specifications, then referenced a nonexistent List lemma. It is excluded from accepted evidence; the proof uses List.drop_left. Source changes strengthening final parent statements justified their focused dependent recompilation.'},indent=2)+'\n')
(E/'s1-y1-caller-tool-pins.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','scripts':{str(p.relative_to(R)):sha(p) for p in sorted((R/'tools/s1-y1-caller-20261024').glob('*.py'))}},indent=2)+'\n')
templates=['S1PrepareBufferRecombineV1','S1WideViewSemanticV1','S1PrepareExpansionBuffersV1','S1ValuesOwnedPrepareY1V1','S1ValuesOwnedStage1Y1V1']
(E/'s1-y1-caller-source-pins.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','scope':'Proof/control templates and reused source/native evidence, not a new source freeze or artifact certificate. No Rust, SDK, parser or arithmetic owner source changed. The adopted29cb/25866 authority and separate historical pins remain as recorded in the powers reconciliation.','templates':{str((S/(n+'.lean')).relative_to(R)):sha(S/(n+'.lean')) for n in templates},'reused_evidence':{str(p.relative_to(R)):sha(p) for p in [E/'s1-prepare-effects-targets.json',E/'s1-prepare-effects-tool-pins.json',E/'s1-powers-callback-source-pins.json',E/'s1-prepare-count-targets.json',E/'s1-prepare-count-import-pins.json']},'native_jobs_launched':0},indent=2)+'\n')
print(json.dumps(metrics))
