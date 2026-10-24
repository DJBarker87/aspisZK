#!/usr/bin/env python3
"""Source-only audit of exact SDK declaration factor and checked consumers."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-first-factor-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'tools/s6-sdk-first-20261024/factor.py'),'--check'],check=True)
m=json.loads((P/'targets.json').read_text());pins=json.loads((E/'s6-sdk-first-factor-import-pins.json').read_text())
for name,a in m['targets'].items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert sha(S/(name+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][name]['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 for audit in r['print_axioms']:
  matches=re.findall(r'\[(.*?)\]',audit,re.S)
  if matches:assert set(matches[0].replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(E/a/'source.lean').read_text())
 for dep,row in r['direct_imports'].items():
  if dep in m['targets']:
   p=json.loads((E/m['targets'][dep]/'receipt.json').read_text());assert p['object_sha256']==row['sha256']
for a in m['rejected']:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==134 and 'memory_exception' in (E/a/'time.log').read_text()
# Successful SDK bridge differs from the rejected complete candidate only in
# import selection and its own consumer namespace. No operation/type/proof replaced.
a=(S/'S6SdkStage1ReuseV1.lean').read_text().replace('import S2W_D189Consolidation','import S6SdkDependencyFactorV1').replace('AspisS6SdkStage1Reuse','AspisS6SdkStage1ReuseFactored')
assert a==(S/'S6SdkStage1ReuseFactoredV1.lean').read_text()
for rel,h in json.loads((P/'tools.json').read_text()).items():assert sha(R/rel)==h
byname={}
for row in pins['modules']:
 assert row['name'] not in byname or byname[row['name']]==row['sha256'];byname[row['name']]=row['sha256']
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',**m['metrics'],selected_import_modules=len(byname),scope=m['scope'])))
