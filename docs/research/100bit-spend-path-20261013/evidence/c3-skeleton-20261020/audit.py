#!/usr/bin/env python3
"""Validate final receipts without rerunning Lean or rebuilding a dependency."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
j=json.loads((HERE/'manifest.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
results=[]
for module,count in [('R1FinalSoundnessNumeric',7),('R1FinalSoundness',1)]:
 a=[a for a in j['attempts'] if a['module']==module][-1]
 assert a['exit']==0,(module,'not green')
 assert a['source_sha256']==sha(BASE/'lean'/f'{module}.lean')
 log=(ROOT/a['log']).read_text()
 assert not re.search(r'(^|\n).*\berror:',log)
 sets=re.findall(r"depends on axioms:\s*\[([^]]*)\]",log)
 assert len(sets)==count,(module,len(sets))
 for found in sets: assert {x.strip() for x in found.split(',') if x.strip()}<=allowed
 for dep in a['direct_imports']:
  assert sha(dep['path'])==dep['sha256'],(module,dep['module'])
 assert a['swaps']==0 and a['peak_rss_bytes']<4400*1024*1024
 results.append({'module':module,'attempt':a['attempt'],'exit':a['exit'],'source_sha256':a['source_sha256'],'axiom_reports':len(sets),'standard_only':True,'source_and_direct_import_pins_current':True})
for name in ['R1FinalSoundness','R1FinalSoundnessNumeric']:
 text=(BASE/'lean'/f'{name}.lean').read_text()
 # Comments may describe rejected evidence; scan code after removing comments.
 code=re.sub(r'/\-.*?\-/','',text,flags=re.S)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',code)
 # Every declared theorem has its own axiom report directive.
 for theorem in re.findall(r'^theorem (\w+)',code,re.M): assert f'#print axioms {theorem}' in code
changed=subprocess.check_output(['git','diff','--name-only','1ba1336ac'],cwd=ROOT,text=True).splitlines()
assert not any(p.startswith('crates/') or p.startswith('programs/') for p in changed)
result={'schema':'c3-focused-static-audit-v1','results':results,'total_new_theorem_reports':8,'scope':'focused cache check only; no frozen-manifest replay; external premise slots and source bridges remain conditional'}
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
