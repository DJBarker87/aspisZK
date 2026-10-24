#!/usr/bin/env python3
"""Source-only enclosing-cut audit; no compiler or private-cache mutation."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s6-sdk-source-cuts-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'tools/s6-sdk-first-20261024/source-cuts.py'),'--check'],check=True)
m=json.loads((P/'targets.json').read_text());pins=json.loads((E/'s6-sdk-source-cuts-import-pins.json').read_text())
for n,a in m['targets'].items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(n+'.lean'))==sha(E/a/'source.lean')==r['source_sha256']==pins['targets'][n]['source_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 if n!='S6SdkSourceCutTypesV1':assert r['print_axioms']
 for audit in r['print_axioms']:
  match=re.findall(r'\[(.*?)\]',audit,re.S)
  if match:assert set(match[0].replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 source=re.sub(r'/\-.*?\-/', '', (E/a/'source.lean').read_text(), flags=re.S)
 source=re.sub(r'--[^\n]*', '', source)
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',source)
 for dep,row in r['direct_imports'].items():
  if dep in m['targets']:
   d=json.loads((E/m['targets'][dep]/'receipt.json').read_text());assert d['object_sha256']==row['sha256']
for a in m['rejected']:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']!=0
 assert sha(E/a/'source.lean')==r['source_sha256']
# The read-only comparison is diagnostic; the differing complete first body
# is separately connected by a kernel-checked all-outcome function equality.
audit=json.loads((P/'declaration-audit-summary.json').read_text())
r=json.loads((E/audit['attempt']/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
assert sha(S/'S6SdkDeclarationAuditV1.lean')==sha(E/audit['attempt']/'source.lean')==r['source_sha256']
lines=(E/audit['attempt']/'lean.log').read_text().splitlines()
summary=json.loads(next(l[len('SUMMARY '):] for l in lines if l.startswith('SUMMARY ')))
assert summary==audit['summary']==dict(different=1,identical=233,missing=3,proof_only=2)
rows=[json.loads(l[5:]) for l in lines if l.startswith('DECL ')]
assert all(row['same_type'] for row in rows)
assert [row['name'] for row in rows if not row['identical'] and not row['proof_only']]==['AspisR1.S2W_D189Wrappers.first']
helper=json.loads((P/'declaration-audit-helper.json').read_text())
original_helper=subprocess.check_output(['git','show',helper['revision']+':'+helper['path']],cwd=R).decode()
body=original_helper[original_helper.index('def sameDeclaration'):original_helper.index('\ndef load')]
assert hashlib.sha256(original_helper.encode()).hexdigest()==helper['source_sha256']
assert hashlib.sha256(body.encode()).hexdigest()==helper['copied_body_sha256']
assert body in (S/'S6SdkDeclarationAuditV1.lean').read_text()
input_binding=json.loads((P/'declaration-audit-input.json').read_text())
assert input_binding['scope'].startswith('Read-only')
# No cache files are needed for this source-only audit. Exact before/after
# pin equality was recorded while they existed; files are not distributed.
binding=json.loads((P/'equivalence-input-binding.json').read_text())
assert binding['all_inputs_unchanged'] and binding['original_wrapper_sha256']=='767215ab84602f604bff75713c814e79a8954bdd6464fd747b2cd37f96106443'
assert binding['original_source_sha256']=='e41d41520f0da7eec5eb5f4d004427a37b80d5bb9a8093cd8c75bb2c68285a68'
assert binding['input_manifest_sha256']==sha(P/'declaration-audit-input.json')
for manifest in ['tools.json','reused.json']:
 for rel,h in json.loads((P/manifest).read_text()).items():assert sha(R/rel)==h
byname={}
for row in pins['modules']:
 assert row['name'] not in byname or byname[row['name']]==row['sha256'];byname[row['name']]=row['sha256']
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',**m['metrics'],selected_import_modules=len(byname),scope=m['scope'])))
