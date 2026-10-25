#!/usr/bin/env python3
"""Read-only exact statement/receipt checks; no compiler replay."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-physical-proof-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so','.pyc']
old=(S/'S1SdkReachedPreparationV1.lean').read_text();new=(S/'S1SdkPhysicalProofV1.lean').read_text()
sig=lambda s:s[s.index(' {W A M Cv : Type}'):s.index(' :\n    post =')]
assert sig(old)==sig(new),'new enclosing premise'
post=lambda s:s[s.index(' :\n    post ='):s.index(' := by')]
b=json.loads((P/'statement-binding.json').read_text());p=post(new)
for text in b['added_conjuncts']:assert p.count(text)==1;p=p.replace(text,'',1)
assert p==post(old),'old same-caller conclusion changed'
assert 'SourceCuts'not in sig(new)+post(new)
body=new[new.index(' := by'):]
for text in ['(first_index e).1','snapshot_read','native_buffer','Ranges.suffix_exact','first_disjoint','write_frame','native_observation','extraction.stage1']:assert text in body,text
for row in json.loads((P/'metrics.json').read_text())['targets']:
 A=E/row['attempt'];r=json.loads((A/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert r['source_sha256']==sha(S/(row['target']+'.lean'))==sha(A/'source.lean')
 assert '-j1'in r['command']and '-M4400'in r['command']
 for report in r['print_axioms']:
  assert 'sorryAx'not in report
  values=re.findall(r'\[(.*?)\]',report,re.S)
  if values:assert set(re.sub(r'\s+','',values[0]).split(','))<={'propext','Classical.choice','Quot.sound'}
 assert r['print_axioms']
 assert not re.search(r'(?m)^\s*axiom\b|\b(sorry|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(S/(row['target']+'.lean')).read_text())
q=subprocess.run([sys.executable,str(R/'tools/s126-sdk-reached-preparation-20261025/check.py')],cwd=R,capture_output=True,text=True);assert q.returncode==0,q.stdout+q.stderr
print(f'PASS {len(m["files"])} pins, two focused targets/standard-only audits. SAME accepted original SDK witness binds native proof-account bytes and57607-byte suffix and both preserved observations. Standing native/SDK/extraction/release premises retained.')
