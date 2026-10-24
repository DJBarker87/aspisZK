#!/usr/bin/env python3
"""Validate focused source evidence without replaying unchanged proofs."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=Path(__file__).resolve().parent
for name in ['generate.py','begin.py','proofs.py','begin-proofs.py','tail-proofs.py','oracle-valid.py','oracle-irrelevance.py','prepare-code.py','pin-native.py']:
 subprocess.run([sys.executable,str(P/name),'--check'],check=True)
subprocess.run([sys.executable,str(R/'tools/s1-semantic-port-20261024/check-models.py'),'--check-source'],check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((E/'s1-prepare-effects-targets.json').read_text());pins=json.loads((E/'s1-prepare-effects-import-pins.json').read_text())
for n,a in m['targets'].items():
 p=S/(n+'.lean');r=json.loads((E/a/'receipt.json').read_text())
 assert r['target']==n and r['exit_status']==0 and r['source_sha256']==sha(p),n
 assert sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][n]['source_sha256'],n
 assert r['object_sha256']==pins['targets'][n]['object_sha256'],n
 assert '-j1' in r['command'] and '-M4400' in r['command'] and r['swaps']==0,n
 assert r['peak_rss_bytes']<4400*1024**2 and r['print_axioms'],n
 for s in r['print_axioms']:
  if 'does not depend on any axioms' in s:continue
  found=re.search(r'depends on axioms:\s*\[([^]]*)\]',s,re.S);assert found
  assert set(re.findall(r'[A-Za-z_.]+',found[1]))<={'propext','Classical.choice','Quot.sound'},(n,s)
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),n
# Complete generated call-graph audit. Native fissions are proof-only mirrors;
# their effectful counterparts must never lift a native digest-bearing callee.
selected=['r1_wire.SemanticTranscript.sample_block_validated','r1_wire.SemanticTranscript.semantic_validated','r1_wire.SemanticTranscript.new','r1_semantic.public_transcript','r1_wire.begin','RoundModel.step','RoundModel.rounds','FinishModel.circle_validated','FinishModel.finish','VerifyPrefix.verify']
for n in [*json.loads((E/'s1-semantic-effects-source-pins.json').read_text())['targets']]:
 text=(S/(n['target']+'.lean')).read_text();body=text.split(':= do',1)[1]
 for name in selected:assert not re.search(r'(?<![A-Za-z0-9_.])'+re.escape(name)+r'(?![A-Za-z0-9_.])',body),(n['target'],name)
 assert not re.search(r'aspis_coreDigest32Inst\.digest\b',body),n['target']
text=(S/'S1SemanticCodeBeginV1.lean').read_text();body=text[text.index('def begin13 {H'):]
for name in selected:assert name not in body,('begin',name)
for p in (E/'s1-prepare-effects-tool-pins.json',E/'s1-prepare-effects-failures.json'):assert p.is_file()
for path,h in json.loads((E/'s1-prepare-effects-tool-pins.json').read_text())['scripts'].items():assert sha(R/path)==h,path
print(json.dumps({'checked_targets':len(m['targets']),'metrics':m['metrics'],'fixed_causal_full_prepare':True,'actual_frozen_sdk_or_security_closure':False}))
