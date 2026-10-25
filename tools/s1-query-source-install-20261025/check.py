#!/usr/bin/env python3
"""Audit concrete owned decoder installation without compiler replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=[('S1OwnedQueryListStepV1','s1-owned-query-list-step-v3'),('S1OwnedQueryBlockSourceLoopV1','s1-owned-query-block-source-loop-v2'),('S1QueryWordsTotalV1','s1-query-words-total-v3'),('S1OwnedQueryBlockSourceV1','s1-owned-query-block-source-v2'),('S1OwnedQueryPairsSourceStepV1','s1-owned-query-pairs-source-step-v1'),('S1OwnedQueryPairsSourceFinishV1','s1-owned-query-pairs-source-finish-v1'),('S1OwnedQueryPairsSourceTailV1','s1-owned-query-pairs-source-tail-v1'),('S1OwnedQueryPairsSourceRunV1','s1-owned-query-pairs-source-run-v1'),('S1OwnedQueryPairsSourceV1','s1-owned-query-pairs-source-v4'),('S1OwnedQueryDecoderInstallationV1','s1-owned-query-decoder-installation-v1'),('S1QueryContinuationTotalV1','s1-query-continuation-total-v2'),('S1QueryDecodeTotalV1','s1-query-decode-total-v1'),('S1QueryProgramTotalV1','s1-query-program-total-v3')]
metrics=[]
for name,attempt in entries:
 p=E/attempt;j=json.loads((p/'receipt.json').read_text());c=json.loads((p/'command.json').read_text());src=S/(name+'.lean')
 assert j['exit_status']==0 and j['swaps']==0 and j['source_sha256']==sha(src)==c['source_sha256']==sha(p/'source.lean')
 assert j['target']==name and '-j1'in j['command'] and '-M4400'in j['command']
 assert j['print_axioms']
 for a in j['print_axioms']:
  if 'depends on axioms:'in a:
   assert set(re.search(r'\[(.*?)\]',a,re.S)[1].split()) <= {'propext,','Classical.choice,','Quot.sound'},a
  else:assert 'does not depend on any axioms'in a
 for n,v in j['direct_imports'].items():assert sha(Path(v['path']))==v['sha256'],n
 for tool,h in j['tool_pins'].items():assert sha(Path(tool))==h
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',src.read_text()),name
 metrics.append({k:j[k]for k in ['target','source_revision','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']})
# Record native/extraction evidence as separate prerequisites, not a Lean axiom.
for tool in ['s1-query-block-cut-20261025','s1-query-membership-current-20261025','s1-query-pairs-cut-20261025','s1-query-pairs-reference-extract-20261025']:
 p=subprocess.run(['python3',str(R/'tools'/tool/'check.py')],text=True,capture_output=True)
 assert p.returncode==0,(tool,p.stderr,p.stdout)
print(json.dumps(dict(schema='focused-extractor-proof-packet-v1',status='PASS',scope='Full Result equality into existing preparation decoder and complete preparation code; TOTAL full row31 byte-oracle program including rejection/embedding/trace continuation. No query success/model law hypothesis. SDK/native/runtime/release admission remains.',focused_targets=metrics),indent=2))
