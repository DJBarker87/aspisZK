#!/usr/bin/env python3
"""Source-only audit: no build, private-cache mutation or release replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-first-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((P/'targets.json').read_text());pins=json.loads((E/'s6-sdk-first-import-pins.json').read_text())
for name,attempt in m['targets'].items():
 d=E/attempt;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(name+'.lean'))==sha(d/'source.lean')==r['source_sha256']==pins['targets'][name]['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 for audit in r['print_axioms']:
  matches=re.findall(r'\[(.*?)\]',audit,re.S)
  if matches:assert set(matches[0].replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
for row in m['rejected']:
 r=json.loads((E/row['attempt']/'receipt.json').read_text());assert r['exit_status']!=0 and not row['selected']
 assert sha(E/row['attempt']/'source.lean')==row['source_sha256']==r['source_sha256']
 if r['exit_status']==134:assert 'memory_exception' in (E/row['attempt']/'time.log').read_text()
assert sha(S/'S6SdkStage1ReuseV1.lean')==sha(E/'s6-sdk-stage1-reuse-v2/source.lean')
# Source identity of every recovered SDK module, independent of private object presence.
for row in json.loads((P/'sdk-source-binding.json').read_text())['sources']:
 assert sha(R/row['source'])==row['sha256']
 actual=subprocess.check_output(['git','show',row['research_revision']+':'+row['research_path']],cwd=R)
 assert hashlib.sha256(actual).hexdigest()==row['sha256']
# Check complete adapter source normalization, not just names/object similarity.
subprocess.run(['python3',str(R/'tools/s6-sdk-first-20261024/adapter-audit.py')],check=True,cwd=R)
t=json.loads((P/'tools.json').read_text())
for group in ['files','reused']:
 for rel,h in t[group].items():assert sha(R/rel)==h,rel
byname={}
for row in pins['modules']:
 assert row['name'] not in byname or byname[row['name']]==row['sha256'];byname[row['name']]=row['sha256']
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',**m['metrics'],selected_import_modules=len(byname),actual_sdk_bridge_checked=False,scope=m['scope'])))
