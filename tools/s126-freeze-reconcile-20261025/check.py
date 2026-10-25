#!/usr/bin/env python3
"""Immutable Git source comparison only; no compiler, cache or worktree edits."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/freeze-reconcile-20261025';sha=lambda b:hashlib.sha256(b).hexdigest();j=json.loads((E/'comparison.json').read_text())
def git(rev,path):return subprocess.check_output(['git','show',rev+':'+path],cwd=R)
for row in j['whole_files']:
 a=git(j['historical_component'],row['path']);b=git(j['later_build_source'],row['path']);assert sha(a)==row['before_sha256']and sha(b)==row['after_sha256'];assert(a==b)==row['identical']
for row in j['selected_items']:
 for key,rev in [('before',j['historical_component']),('after',j['later_build_source'])]:
  s=git(rev,row['path']).decode();a=s.index(row['start']);z=s.index('{',a)+1;depth=1
  while depth:depth+=(s[z]=='{')-(s[z]=='}');z+=1
  assert sha(s[a:z].encode())==row[key+'_sha256']
 assert row['identical']==(row['before_sha256']==row['after_sha256'])
for row in j['core_source_files']:
 assert sha(git(j['later_build_source'],row['source']))==row['later_sha256'];assert row['identical']==(row['historical_sha256']==row['later_sha256'])
print(json.dumps(dict(status='PASS',whole_files=len(j['whole_files']),selected_items=len(j['selected_items']),core_files=len(j['core_source_files']),all_core_files_identical=all(r['identical']for r in j['core_source_files']),qualification='Exact scoped source comparisons only. Not whole-context/dependency/artifact identity or later-build actual SDK closure.')))
