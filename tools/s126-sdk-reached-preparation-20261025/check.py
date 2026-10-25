#!/usr/bin/env python3
"""Read-only audit of reached SDK witnesses and unchanged enclosing hypotheses."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'sdk-reached-preparation-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so','.pyc']
old=(S/'S1SdkFinalArithmeticV1.lean').read_text();new=(S/'S1SdkReachedPreparationV1.lean').read_text()
signature=lambda s:s[s.index(' {W A M Cv : Type}'):s.index(' :\n    post =')]
assert signature(old)==signature(new),'SDK/extraction/acceptance hypotheses changed'
tail=lambda s:s[s.index('      f.pub ='):s.index(' := by')]
assert tail(old)==tail(new),'same-caller preparation/range/trace/continuation tail changed'
post=new[new.index(' :\n    post ='):new.index(' := by')]
assert 'SourceCuts' not in post and 'SecondCut' not in post and '∃ f : FirstCut' in post
for value in ['ok f.proofAccount','ok f.publicAccount','ok (.Ok f.statement)','f.statement = ok f.semantic','f.raw.val.length = 58295','ok (.Ok out)']:
 assert value in post,value
helper=(S/'S6SdkReachedFirstV1.lean').read_text()
for v in ['AdapterRw.Accepted.first_call','extraction.stage1','S2W_D189Wrappers.first_accepted','RepinS6First.reuse_decoded']:
 assert v in helper,v
for row in json.loads((P/'metrics.json').read_text())['targets']:
 A=E/row['attempt'];r=json.loads((A/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(row['target']+'.lean'))==r['source_sha256']==sha(A/'source.lean')
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert r['print_axioms']
 for report in r['print_axioms']:
  assert 'sorryAx' not in report
  v=re.findall(r'\[(.*?)\]',report,re.S)
  if v:assert set(re.sub(r'\s+','',v[0]).split(','))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'(?m)^\s*axiom\b|\b(sorry|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(S/(row['target']+'.lean')).read_text())
# Excluded failed elaboration is retained, never accepted as a theorem.
f=json.loads((E/'s1-sdk-reached-preparation-v1/receipt.json').read_text())
assert f['exit_status']==1 and 'Unknown identifier `saved`' in (E/'s1-sdk-reached-preparation-v1/lean.log').read_text()
q=subprocess.run([sys.executable,str(R/'tools/s1-final-arithmetic-20261025/check.py')],cwd=R,capture_output=True,text=True)
assert q.returncode==0,q.stdout+q.stderr
print(f'PASS {len(m["files"])} pins, two focused targets/standard-only audits; unchanged SDK binders and exact full preparation/ranges/trace tail. Actual reached first witness derived, no input SourceCuts. Native/extraction/settlement/coherent release remain OPEN.')
