#!/usr/bin/env python3
"""Check final focused receipts and source/import pins without replaying Lean."""
import hashlib, json, pathlib, re, subprocess
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT/'docs/research/100bit-spend-path-20261013'
MODULES = ['RawRecordedLogCostObstruction', 'RawRecordedInitialCutObstruction',
           'RawRecordedExtractorBranchTrace', 'RawExtractorParameterPolynomial']
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
manifest = json.loads((HERE/'manifest.json').read_text())
source_pins = json.loads((HERE/'source-pins.json').read_text())
for pin in source_pins['files']:
    assert sha(ROOT/pin['path'])==pin['sha256'], ('source pin',pin['path'])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
results = []
for module in MODULES:
    source = BASE/'lean'/(module+'.lean')
    attempt = [a for a in manifest['attempts'] if a['module']==module][-1]
    assert attempt['exit']==0, (module, 'latest attempt not accepted')
    assert attempt['source_sha256']==sha(source), (module, 'source changed')
    log = (ROOT/attempt['log']).read_text()
    assert not re.search(r'(^|\n).*\berror:',log), module
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))",log)
    for _, axioms, _ in reports:
        assert {s.strip() for s in axioms.split(',') if s.strip()} <= allowed
    text = source.read_text()
    code = re.sub(r'/\-.*?\-/','',text,flags=re.S)
    code = re.sub(r'--[^\n]*','',code)
    directives = re.findall(r'^#print axioms (\S+)',code,re.M)
    theorems = re.findall(r'^theorem (\w+)',code,re.M)
    assert set(theorems)==set(directives), (module, theorems, directives)
    assert len(reports)==len(theorems), (module,len(reports),len(theorems))
    assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',code)
    assert not re.search(r'^\s*axiom\b',code,re.M)
    for dep in attempt['direct_imports']:
        assert dep['sha256']==sha(dep['path']), (module,dep['module'])
    assert attempt['swaps']==0 and attempt['peak_rss_bytes'] < 8*1024**3
    results.append({k: attempt[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
base = '6bb2b9cb1'
status = subprocess.check_output(['git','diff','--name-status',base],cwd=ROOT,text=True).splitlines()
assert all(s.startswith('A\t') for s in status), 'existing tracked files changed'
result = {'schema':'m10-focused-static-audit-v1','source_and_import_pins_current':True,
          'standard_axioms_only':True,'all_new_theorems_audited':True,
          'existing_tracked_files_unchanged':True,'results':results,
          'scope':'focused cached checks; no coherent frozen-manifest release replay; ledger and actual input-size family remain open'}
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
