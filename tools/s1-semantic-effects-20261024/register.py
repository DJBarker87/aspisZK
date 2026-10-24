#!/usr/bin/env python3
"""Register only successful current source objects; no compilation here."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
names={}
for stem,attempt in [('SampleBlock','sample-block-v2'),('SampleBlockExact','sample-block-exact-v1'),('SemanticValidated','semantic-validated-v1'),('SemanticValidatedExact','semantic-validated-exact-v1'),('Begin','begin-v2'),('BeginExact','begin-exact-v2'),('NewTranscript','new-transcript-v1'),('NewTranscriptExact','new-transcript-exact-v1'),('PublicTranscript','public-transcript-v1'),('PublicTranscriptExact','public-transcript-exact-v1'),('RoundStep','round-step-v2'),('RoundStepExact','round-step-exact-v2'),('Rounds','rounds-v2'),('RoundsExact','rounds-exact-v2'),('CircleValidated','circle-validated-v1'),('CircleValidatedExact','circle-validated-exact-v2'),('Finish','finish-v2'),('FinishExact','finish-exact-v2'),('Verify','verify-v2'),('VerifyExact','verify-exact-v2'),('P3Valid','p3-valid-v2'),('Dictionary','dictionary-v2')]:names['S1SemanticCode'+stem+'V1']='s1-semantic-code-'+attempt
names.update({'S1SemanticGhostDictionaryV1':'s1-semantic-ghost-dictionary-v1','S1SemanticCurrentCodeV1':'s1-semantic-current-code-v2','S1CurrentPrepareCodeV1':'s1-current-prepare-code-v3','S1CurrentPrepareCodeExactV1':'s1-current-prepare-code-exact-v3','S1CurrentPrepareCausalV1':'s1-current-prepare-causal-v2','S1OwnedStage1PrepareEffectsV1':'s1-owned-stage1-prepare-effects-v1','S1TopPrepareCodeV1':'s1-top-prepare-code-v1','S1TopPrepareCausalV1':'s1-top-prepare-causal-v1','S1TopPrepareOracleV1':'s1-top-prepare-oracle-v1'})
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();receipts=[];m=json.loads((E/'accepted-targets.json').read_text())
for n,a in names.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['target']==n and r['exit_status']==0,n
 assert sha(S/(n+'.lean'))==r['source_sha256'],n
 assert sha(Path('/tmp/s126-current-caller-20261021-objects')/(n+'.olean'))==r['object_sha256'],n
 assert r['print_axioms'] and all('sorryAx' not in s for s in r['print_axioms']),n
 receipts.append(r);m['targets'][n]={k:r[k] for k in ['source_sha256','wall_seconds','peak_rss_bytes','swaps','print_axioms']};m['targets'][n]['receipt']=a+'/receipt.json'
metrics={'targets':len(names),'wall_seconds':sum(r['wall_seconds'] for r in receipts),'max_rss_bytes':max(r['peak_rss_bytes'] for r in receipts),'swaps':sum(r['swaps'] for r in receipts)}
packet={'schema':'focused-extractor-proof-packet-v1','targets':names,'metrics':metrics,'qualification':'Full current installed source-model prepare effect program and all-outcome source equality, same owned stage1 and top op7 candidate. Fixed causal P3 program, not frozen native SDK/primitive/driver security closure.'}
(E/'accepted-targets.json').write_text(json.dumps(m,indent=2)+'\n');(E/'s1-prepare-effects-targets.json').write_text(json.dumps(packet,indent=2)+'\n');print(json.dumps(metrics))
