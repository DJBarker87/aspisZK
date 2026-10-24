#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-accepted-rounds-numeric-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
targets={'S1SemanticProducerRangesV1':'s1-semantic-producer-ranges-v1','S1AcceptedSemanticNumericV1':'s1-accepted-semantic-numeric-v3','S1AcceptedRoundsNumericV1':'s1-accepted-rounds-numeric-v3','S1PrepareNumericV1':'s1-prepare-numeric-v1','S1OwnedStage1NumericV1':'s1-owned-stage1-numeric-v3'}
m=json.loads((E/'accepted-targets.json').read_text());receipts=[]
for name,attempt in targets.items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['target']==name
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 assert r['print_axioms'] and all('sorryAx' not in x for x in r['print_axioms'])
 m['targets'][name]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][name]['receipt']=attempt+'/receipt.json';receipts.append(r)
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n')
metrics=dict(targets=len(targets),wall_seconds=sum(r['wall_seconds'] for r in receipts),max_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=sum(r['swaps'] for r in receipts),axiom_reports=sum(len(r['print_axioms']) for r in receipts))
all_attempts=[]
for prefix in ['s1-accepted-rounds-numeric-v','s1-accepted-semantic-numeric-v','s1-semantic-producer-ranges-v','s1-owned-stage1-numeric-v','s1-prepare-numeric-v','s1-top-prepare-numeric-v','s1-numeric-caller-import-probe-v']:
 for p in sorted(E.glob(prefix+'*')):
  r=json.loads((p/'receipt.json').read_text());all_attempts.append(dict(attempt=p.name,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],selected=p.name in targets.values(),source_sha256=r['source_sha256']))
(P/'targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=targets,metrics=metrics,attempts=all_attempts,scope='ACCEPTED-ONLY complete source-model rounds, finish, verify, preparation and owned stage1 ranges. Reached arithmetic TOTAL is reused, not whole native/SDK/caller TOTAL. No new op7 aggregation or frozen release claim.'),indent=2)+'\n')
# Four-word range source proofs are dependency-factored, not re-proved against a different decoder.
old=S/'S1ExtractedDecodedRoundTotalV1.lean';new=S/'S1SemanticProducerRangesV1.lean'
a=old.read_text().split('theorem decoded_success_inv',1)[1].split('/-- Once decoding',1)[0]
b=new.read_text().split('theorem decoded_success_inv',1)[1].split('#print axioms decoded_success_inv',1)[0]
assert a==b
(P/'factor-source.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',original=str(old.relative_to(R)),original_sha256=sha(old),factored=str(new.relative_to(R)),factored_sha256=sha(new),copied_proof_span_sha256=hashlib.sha256(a.encode()).hexdigest(),qualification='Exact three proof bodies reused; only imports, enclosing namespace and definition of Canonical factored. canonical_iff_source_ranges proves identical full word ranges with no axioms.'),indent=2)+'\n')
(P/'tools.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(R)):sha(p) for p in (R/'tools/s1-accepted-rounds-20261024').glob('*.py')},reused={str(p.relative_to(R)):sha(p) for p in [R/'tools/s126-sdk-20261021/lean-local.py',R/'tools/s126-sdk-20261021/pin-imports.py',E/'s1-round-canonical-cache-20261024/provenance.json',E/'s1-finish-selectors-20261024/targets.json']}),indent=2)+'\n')
print(json.dumps(metrics))
