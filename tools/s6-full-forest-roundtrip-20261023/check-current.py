#!/usr/bin/env python3
"""Source/receipt audit only. Never replay unchanged verification jobs."""
from pathlib import Path
import copy,hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for script in ['materialize.py','materialize-codec.py','materialize-digest-reference.py']:
 subprocess.run(['python3',str(Path(__file__).parent/script),'--check'],check=True)
subprocess.run(['python3',str(Path(__file__).parent/'check.py')],check=True)
pins=load(E/'s6-full-forest-current-import-pins.json');accepted=load(E/'accepted-targets.json')['targets'];reports=0
for module in pins['targets']:
 r=load(E/accepted[module]['receipt']);p=S/(module+'.lean')
 assert r['exit_status']==0 and r['swaps']==0
 assert sha(p)==sha((E/accepted[module]['receipt']).parent/'source.lean')==r['source_sha256']==pins['targets'][module]['source_sha256']
 assert r['object_sha256']==pins['targets'][module]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for line in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',line,re.S)
  assert m and set(re.findall(r'[A-Za-z_.]+',m[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
for folder in ['s6-full-forest-encoder-extraction','s6-full-forest-codec-extraction','s6-full-forest-exploration']:
 root=E/folder
 for name,h in load(root/'manifest.json')['files'].items():assert sha(root/name)==h,(folder,name)
root=E/'s6-full-forest-codec-extraction';before=load(root/'llbc/original.llbc.json');after=load(root/'llbc/renamed.llbc.json')
changes=load(root/'source/backend-renaming.json')['changes']
for f in after['translated']['fun_decls']:
 if f and any(x['id']==f['def_id'] for x in changes):f['item_meta']['attr_info']['rename']=None
assert before==after,'Only backend naming metadata may change'
for name,count in [('digest-encoder',191),('digest-roundtrip',392),('snapshot-frontier-loop',195),('afterstate-frontier-loop',195)]:
 root=E/'s6-full-forest-native'/name;r=load(root/'attempt/receipt.json');assert r['exit_status']==0 and r['swaps']==0
 for path,h in load(root/'manifest.json')['files'].items():assert sha(root/path)==h
 binding=load(root/'input/frozen-statement-binding.json')
 for f,h in binding['source_files'].items():assert sha(root/'input/frozen-source/crates/aspis-statement'/f)==h
 assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
 assert all(load(root/'attempt/all-local-after.json')['unchanged'].values())
 assert f'0 of {count} failed' in (root/'attempt/stdout.log').read_text()
 assert sha(root/'runner.py')==load(root/'attempt/input.json')['runner_sha256']
print(json.dumps(dict(accepted_lean_targets=len(pins['targets']),standard_axiom_reports=reports,
 actual_outer_source_models=True,source_model_wrong_length_branch_proved=True,
 native_digest_original_reference_checked=True,native_snapshot_loop_full800_frame_checked=True,
 full_forest_roundtrip=False,native_sdk_binding=False,whole_s1_closed=False,whole_s6_closed=False)))
