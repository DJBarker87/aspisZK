#!/usr/bin/env python3
"""Check source-only encoder totality evidence; no compiler replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['owned-frontier','afterstate-parent','snapshot-helper','snapshot-parent','late-parent','forest-parent']:
 subprocess.run(['python3','-B',str(Path(__file__).with_name('materialize-'+name+'.py')),'--check'],check=True)
for folder in ['s6-owned-frontier','s6-afterstate-loop-parent','s6-snapshot-helper','s6-snapshot-loop-parent','s6-late-parent','s6-forest-parent']:
 root=E/folder
 for name,h in load(root/'manifest.json')['files'].items():assert sha(root/name)==h,(folder,name)
 assert not list(root.rglob('*.olean')) and not list(root.rglob('*.tar.gz'))
rows=load(E/'s6-encoder-total-targets.json')['targets'];accepted=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-encoder-total-import-pins.json');reports=0
for target,attempt in rows.items():
 r=load(E/attempt/'receipt.json');assert r['exit_status']==0 and r['swaps']==0
 assert accepted[target]['receipt']==attempt+'/receipt.json'
 assert sha(S/(target+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']
 assert pins['targets'][target]['source_sha256']==r['source_sha256'] and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',(S/(target+'.lean')).read_text(),re.M)
 assert r['print_axioms']
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   a=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert a and set(re.findall(r'[A-Za-z_.]+',a[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
compat=load(E/'s6-current-statement-source-compatibility.json')
for path,h in compat['byte_equal_files'].items():
 for revision in [compat['historical_freeze'],compat['current_research']]:
  blob=subprocess.check_output(['git','-C',str(R),'show',revision+':'+path])
  assert hashlib.sha256(blob).hexdigest()==h
print(json.dumps(dict(accepted_targets=len(rows),standard_or_empty_axiom_reports=reports,whole_s6_closed=False,actual_sdk_binding=False)))
