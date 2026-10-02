#!/usr/bin/env python3
"""Offline integrity check for R388 translation output; does not run Aeneas or Lean."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'R388ReduceU62Ordered.llbc'; assert sha(source)=='95480c0a8938629f770f7c381fe61a71f44e8275fe2e7275e9edfd4a4bb7f040'
result=json.loads((R/'result.json').read_text()); command=json.loads((R/'command.json').read_text())
assert result['exit_status']==0 and result['Lean_compiled'] is False and result['template_filling']=='not performed'
assert result['binary_sha256']=='3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
assert result['input_sha256']==sha(source) and command['namespace']=='AspisR388ReduceU62'
for path, digest in result['generated_files'].items(): assert sha(R/path)==digest,(path,digest)
funs=(R/'generated/AspisR388ReduceU62/Funs.lean').read_text()
block=(R/'generated-reduce-u62-definition-verbatim.lean').read_text()
assert block in funs and 'def aspis_core.field.M31.reduce_u62' in block
assert 'let i ← aspis_core.field.reduce_u64 value' in block and 'assert' not in block
raw=json.loads((R/'raw-release-debug-assert-branch.json').read_text())
assert raw['false_guard_assignment_statement']['kind']['Assign'][1]['Use'][0]['Const']['kind']['Literal']['Bool'] is False
assert 'Switch' in raw['conditional_branch_statement']['kind']
plan=json.loads((R/'translation-plan.json').read_text())
assert plan['translation_attempt_count']==1 and plan['translation_exit_status']==0
assert (R/'history/translation-service-preflight-failure.log').is_file()
print(json.dumps({'status':'PASS','input_sha256':sha(source),'binary_sha256':result['binary_sha256'],'generated_files':result['generated_files'],'literal_reduce_u62_body_sha256':sha(R/'generated-reduce-u62-definition-verbatim.lean'),'raw_false_assert_guard':True,'Lean_compiled':False,'template_filling':False},indent=2))
