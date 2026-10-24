#!/usr/bin/env python3
"""Verify retained source-only failed experiments, not semantic closure."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
count=0
for name in ['s1-native-mir-20261024','s1-loop-contract-20261024','s1-native-control-followup-20261024']:
 root=E/name;m=json.loads((root/'manifest.json').read_text());assert m['schema']=='focused-extractor-proof-packet-v1'
 for p,h in m['files'].items():
  f=root/p;assert f.resolve().is_relative_to(root.resolve()) and sha(f)==h
  assert f.suffix not in ['.olean','.llbc','.bc','.rlib','.o','.so','.a','.exe']
  count+=1
 for p in root.rglob('receipt.json'):
  r=json.loads(p.read_text());assert r['swaps']==0 and r['limits']['memory.swap.max'] in ['0',0]
  assert int(r['limits']['memory.max'])>0
  assert r['print_axioms']=='N/A: no Lean compilation'
  if 'aeneas' in str(p):assert r['exit_status']==2
  elif 'charon' in str(p):assert r['exit_status']==0
  elif 'preflight-v2-' in str(p) or 'preflight-v4-' in str(p):assert r['exit_status']==0
  else:assert r['exit_status']!=0
root=E/'s1-loop-contract-20261024';parent=root/'inputs/aspis-s1-claim-powers-cut-v1-20261024/src/lib.rs';tape=root/'inputs/s1-claim-ordered-tape-v1-20261024/src/lib.rs';assert sha(parent)==sha(tape)
frozen=subprocess.check_output(['git','show','b2727acd3abf79315d18b754a260f58f4b1c6326:crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R,text=True)
def body(s):
 start=s.index('{',s.index('fn prepared_claim<'));i=start;depth=0
 while i<len(s):
  depth+=(s[i]=='{')-(s[i]=='}')
  if depth==0:return s[start:i+1]
  i+=1
assert re.sub(r'\s+','',body(frozen))==re.sub(r'\s+','',body(tape.read_text()))
for n in ['s1-original-whole-powers-cut-v1','s1-claim-ordered-tape-v1']:
 r=json.loads((root/'attempts'/n/'receipt.json').read_text());assert r['exit_status']!=0
 text=(root/'attempts'/n/'stdout.log').read_text()+(root/'attempts'/n/'stderr.log').read_text();assert 'timeout' in text.lower() or 'timed out' in text.lower()
for n in ['s1-claim-loop-contract-v2','s1-claim-loop-contract-v2-backtrace','s1-claim-loop-contract-v3']:
 assert 'Kani can only insert instructions after terminators' in (root/'attempts'/n/'stdout.log').read_text()
print(json.dumps(dict(source_only_files=count,whole_claim_proof=False,native_claim_refinement=False,unchanged_original_claim_body=True)))
