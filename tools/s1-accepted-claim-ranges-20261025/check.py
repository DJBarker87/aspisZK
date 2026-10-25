#!/usr/bin/env python3
"""Source-only focused S1 SDK trace packet audit, no trusted cache import."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'s1-accepted-claim-ranges-20261025'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'targets.json').read_text()); pins=json.loads((E/'s1-accepted-claim-ranges-import-pins.json').read_text())
for n,a in m['targets'].items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][n]['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command'] and r['print_axioms']
 for report in r['print_axioms']:
  words=re.findall(r'\[(.*?)\]',report,re.S); assert words
  assert set(words[0].replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 source=re.sub(r'/\-.*?\-/', '', (S/(n+'.lean')).read_text(),flags=re.S);source=re.sub(r'--[^\n]*','',source)
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',source)
 for dep,row in r['direct_imports'].items():
  if dep in m['targets']:
   d=json.loads((E/m['targets'][dep]/'receipt.json').read_text());assert row['sha256']==d['object_sha256']
for a in m['rejected']:
 r=json.loads((E/a/'receipt.json').read_text()); assert r['exit_status']!=0 and sha(E/a/'source.lean')==r['source_sha256']
for rel,h in json.loads((P/'tools.json').read_text()).items(): assert sha(R/rel)==h
names={}
for row in pins['modules']:
 assert row['name'] not in names or names[row['name']]==row['sha256'];names[row['name']]=row['sha256']
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',**m['metrics'],selected_import_modules=len(names),scope=m['scope'])))

# Complete published endpoint header is unchanged; only one range conclusion is added.
old=(S/'S1SdkSelectedSemanticTraceV1.lean').read_text()
new=(S/'S1SdkClaimInputRangesV1.lean').read_text()
header=lambda text:text[text.index('{W A M Cv'):text.index('    post = writeBracket')]
assert header(old)==header(new)
post=lambda text:text[text.index('    post = writeBracket'):text.index(' := by')]
addition='        AspisS1ClaimAcceptedCallerRanges.CurrentClaimsNumeric sem ∧\n'
assert post(new).count(addition)==1
assert post(new).replace(addition,'')==post(old)
assert 'scratch claimed' in new
assert '(hk :' not in (S/'S1ClaimAcceptedScalarRangesV1.lean').read_text()
assert '(hk :' not in (S/'S1ClaimAcceptedCallerRangesV1.lean').read_text()
print('PASS exact old SDK hypotheses and conclusions preserved; one Claims range conclusion added')

full=json.loads((P/'manifest.json').read_text())
for rel,h in full['files'].items():
 assert sha(R/rel)==h,rel
 assert Path(rel).suffix not in ['.olean','.ir','.llbc','.so','.o','.a','.pyc','.rlib','.bc']
print('PASS complete source-only manifest',len(full['files']))
